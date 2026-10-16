// Typed builders for machines, decisions and loops: names are declared once and come back as typed values, so a
// misspelled name, a law that reads a request, or a step that sets an undeclared variable is a TypeScript error, and
// the input kinds the kernel would otherwise see as hand encodings (a flag, an optional fact, a choice among values)
// are declared as kinds. Everything here compiles to the plain values kernel.ts and the runtimes take (Machine, Law,
// Goal, Loop), so nothing in this file is trusted: the kernel checks what it is given, and its scope check refuses
// whatever the types here let through.
//
//   const budget = rule('budget')
//     .params({b: nat, m: nat})
//     .inputs({c: nat})
//     .state({s: 0})
//     .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
//   const bounded = budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))
//   proveRule(budget, [bounded])
//
// A step returns its updates as one object: every right-hand side reads the state before the step, as the kernel and
// both runtimes do.
import {type C, type E, type Law, type Machine, type State, interpret, loadJs} from './machine.ts'
import {type Goal, type Loop, type Tree, check, loopObligations} from '../kernel/kernel.ts'
import {grow, proveLaws} from '../kernel/prove.ts'

// --- terms and conditions -------------------------------------------------------------------------------------------

const naturalConst = (v: number): number => {
  if (!Number.isSafeInteger(v) || v < 0) throw new RangeError(`${v} is not a natural`)
  return v
}
export type TermLike = Term | number
export const termOf = (t: TermLike): E => (typeof t === 'number' ? {op: 'const', value: naturalConst(t)} : t.e)

// A natural-valued term. `minus` is truncated (a ∸ b), `times` multiplies by a constant, `mul` by another term (a
// product: the kernel proves with it, the GPU searches don't take it).
export class Term {
  constructor(readonly e: E) {}
  plus(b: TermLike): Term { return new Term({op: 'add', a: this.e, b: termOf(b)}) }
  minus(b: TermLike): Term { return new Term({op: 'sub', a: this.e, b: termOf(b)}) }
  times(k: number): Term { return new Term({op: 'mul', k: naturalConst(k), a: this.e}) }
  mul(b: TermLike): Term { return new Term({op: 'prod', a: this.e, b: termOf(b)}) }
  lt(b: TermLike): Cond { return new Cond({op: '<', a: this.e, b: termOf(b)}) }
  atMost(b: TermLike): Cond { return new Cond({op: '<=', a: this.e, b: termOf(b)}) }
  gt(b: TermLike): Cond { return new Cond({op: '<', a: termOf(b), b: this.e}) }
  atLeast(b: TermLike): Cond { return new Cond({op: '<=', a: termOf(b), b: this.e}) }
  eq(b: TermLike): Cond { return new Cond({op: '=', a: this.e, b: termOf(b)}) }
  ne(b: TermLike): Cond { return this.eq(b).not() }
}

export class Cond {
  constructor(readonly c: C) {}
  and(...xs: Cond[]): Cond { return all(this, ...xs) }
  or(...xs: Cond[]): Cond { return any(this, ...xs) }
  not(): Cond { return new Cond({op: 'not', x: this.c}) }
  implies(b: Cond): Cond { return any(this.not(), b) }
  iff(b: Cond): Cond { return all(this.implies(b), b.implies(this)) }
}

export const lit = (v: number): Term => new Term(termOf(v))
export const yes = new Cond({op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}})
export const no = new Cond({op: '<', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}})
export const all = (...cs: Cond[]): Cond => (cs.length === 0 ? yes : cs.length === 1 ? cs[0]! : new Cond({op: 'and', xs: cs.map(c => c.c)}))
export const any = (...cs: Cond[]): Cond => (cs.length === 0 ? no : cs.length === 1 ? cs[0]! : new Cond({op: 'or', xs: cs.map(c => c.c)}))
export const not = (c: Cond): Cond => c.not()
export const min = (a: TermLike, b: TermLike): Term => new Term({op: 'min', a: termOf(a), b: termOf(b)})
export const max = (a: TermLike, b: TermLike): Term => new Term({op: 'max', a: termOf(a), b: termOf(b)})
export const when = (c: Cond, then: TermLike, otherwise: TermLike): Term => new Term({op: 'if', c: c.c, then: termOf(then), else: termOf(otherwise)})
// A condition by cases: `then` where c holds, `otherwise` elsewhere.
export const choose = (c: Cond, then: Cond, otherwise: Cond): Cond => any(all(c, then), all(c.not(), otherwise))
// 1 where c holds, else 0: what a sum over a history adds per record.
export const count = (c: Cond): Term => when(c, 1, 0)
export const sum = (first: TermLike, ...rest: TermLike[]): Term => rest.reduce<Term>((acc, t) => acc.plus(t), typeof first === 'number' ? lit(first) : first)

// --- kinds: what a param or input may be ------------------------------------------------------------------------------

type Rand = (k: number) => number
type Raw = number | boolean | string | null | undefined

// A kind names the variables a value is encoded in, what is assumed of them, the value the builders hand out, and how
// a runtime value is encoded and drawn at random (the examples' harness draws inputs this way).
export abstract class Kind<V> {
  declare readonly _value: V
  abstract vars(name: string): string[]
  abstract assume(name: string): Cond[]
  abstract value(name: string, prefix?: string): V
  abstract encode(name: string, raw: Raw): Record<string, number>
  abstract random(name: string, rand: Rand, bound: number): Record<string, number>
}
const v = (name: string) => new Term({op: 'var', name})
const asNat = (name: string, raw: Raw): number => {
  if (typeof raw !== 'number' || !Number.isSafeInteger(raw) || raw < 0) throw new RangeError(`${name} must be a natural, not ${String(raw)}`)
  return raw
}

class NatKind extends Kind<Term> {
  constructor(readonly maxValue?: number) { super() }
  vars(name: string) { return [name] }
  assume(name: string) { return this.maxValue === undefined ? [] : [v(name).atMost(this.maxValue)] }
  value(name: string, prefix = '') { return v(prefix + name) }
  encode(name: string, raw: Raw) {
    const n = asNat(name, raw)
    if (this.maxValue !== undefined && n > this.maxValue) throw new RangeError(`${name} is at most ${this.maxValue}, not ${n}`)
    return {[name]: n}
  }
  random(name: string, rand: Rand, bound: number) { return {[name]: rand((this.maxValue ?? bound) + 1)} }
}
export const nat: Kind<Term> = new NatKind()
// A natural known to be at most `maxValue` (a percentage, a floor number, a weekday).
export const upTo = (maxValue: number): Kind<Term> => new NatKind(naturalConst(maxValue))

// A yes/no value, encoded as 0 or 1. It is a condition; `.n` is its 0/1 term (to add or count it).
export class Bool extends Cond {
  constructor(readonly n: Term) { super({op: '=', a: n.e, b: {op: 'const', value: 1}}) }
}
class BoolKind extends Kind<Bool> {
  vars(name: string) { return [name] }
  assume(name: string) { return [v(name).atMost(1)] }
  value(name: string, prefix = '') { return new Bool(v(prefix + name)) }
  encode(name: string, raw: Raw) {
    if (typeof raw === 'boolean') return {[name]: raw ? 1 : 0}
    if (raw === 0 || raw === 1) return {[name]: raw}
    throw new RangeError(`${name} must be a boolean, not ${String(raw)}`)
  }
  random(name: string, rand: Rand) { return {[name]: rand(2)} }
}
export const bool: Kind<Bool> = new BoolKind()

// One of a few named values, encoded as its index. `match` takes every case (TypeScript checks none is missing).
export class Choice<K extends string> {
  constructor(readonly n: Term, readonly values: readonly K[]) {}
  is(k: K): Cond {
    const i = this.values.indexOf(k)
    if (i < 0) throw new Error(`${k} is not one of ${this.values.join(', ')}`)
    return this.n.eq(i)
  }
  match(cases: {[k in K]: () => Cond}): Cond
  match(cases: {[k in K]: () => TermLike}): Term
  match(cases: {[k in K]: () => Cond | TermLike}): Cond | Term {
    const results = this.values.map(k => [k, cases[k]()] as const)
    if (results.every(([, r]) => r instanceof Cond)) return any(...results.map(([k, r]) => all(this.is(k), r as Cond)))
    if (results.some(([, r]) => r instanceof Cond)) throw new Error('every case of a match is a condition, or every case is a term')
    // The last case is what's left: the kind's assumption says the index is below the number of values.
    return results.slice(0, -1).reduceRight<Term>((acc, [k, r]) => when(this.is(k), r as TermLike, acc), typeof results.at(-1)![1] === 'number' ? lit(results.at(-1)![1] as number) : results.at(-1)![1] as Term)
  }
}
class OneOfKind<K extends string> extends Kind<Choice<K>> {
  constructor(readonly values: readonly K[]) {
    super()
    if (values.length === 0 || new Set(values).size !== values.length) throw new Error('oneOf takes distinct values')
  }
  vars(name: string) { return [name] }
  assume(name: string) { return [v(name).lt(this.values.length)] }
  value(name: string, prefix = '') { return new Choice(v(prefix + name), this.values) }
  encode(name: string, raw: Raw) {
    const i = this.values.indexOf(raw as K)
    if (i < 0) throw new RangeError(`${name} is one of ${this.values.join(', ')}, not ${String(raw)}`)
    return {[name]: i}
  }
  random(name: string, rand: Rand) { return {[name]: rand(this.values.length)} }
}
export const oneOf = <const K extends string>(...values: K[]): Kind<Choice<K>> => new OneOfKind(values)

// A value that may be missing, encoded as a presence bit and the value. The value can only be read in `some`, so no
// law or step can read a missing value; the encoding leaves it unconstrained when missing, so nothing proven depends
// on it.
export class Maybe<V> {
  constructor(private readonly present: Term, private readonly inner: V) {}
  get isSome(): Cond { return this.present.eq(1) }
  get isNone(): Cond { return this.present.eq(0) }
  match(cases: {none: () => Cond, some: (value: V) => Cond}): Cond
  match(cases: {none: () => TermLike, some: (value: V) => TermLike}): Term
  match(cases: {none: () => Cond | TermLike, some: (value: V) => Cond | TermLike}): Cond | Term {
    const none = cases.none(), some = cases.some(this.inner)
    if (none instanceof Cond && some instanceof Cond) return choose(this.isSome, some, none)
    if (none instanceof Cond || some instanceof Cond) throw new Error('both cases of a match are conditions, or both are terms')
    return when(this.isSome, some, none)
  }
}
class MaybeKind<V> extends Kind<Maybe<V>> {
  constructor(readonly of: Kind<V>) { super() }
  private has(name: string) { return `${name}$some` }
  vars(name: string) { return [this.has(name), ...this.of.vars(name)] }
  assume(name: string) { return [v(this.has(name)).atMost(1), ...this.of.assume(name)] }
  value(name: string, prefix = '') { return new Maybe(v(prefix + this.has(name)), this.of.value(name, prefix)) }
  encode(name: string, raw: Raw) {
    if (raw === null || raw === undefined) return {[this.has(name)]: 0, ...Object.fromEntries(this.of.vars(name).map(n => [n, 0]))}
    return {[this.has(name)]: 1, ...this.of.encode(name, raw)}
  }
  random(name: string, rand: Rand, bound: number) {
    return rand(4) === 0 ? {[this.has(name)]: 0, ...Object.fromEntries(this.of.vars(name).map(n => [n, rand(bound + 1)]))} : {[this.has(name)]: 1, ...this.of.random(name, rand, bound)}
  }
}
export const maybe = <V>(of: Kind<V>): Kind<Maybe<V>> => new MaybeKind(of)

// --- maps, laws, relations ------------------------------------------------------------------------------------------

export type MapWrite = {readonly map: string, readonly key: E, readonly value: E}
// A map from naturals to naturals, every cell starting at `init`. One write per map per step.
export class MapRef {
  constructor(readonly name: string, readonly init: number) {}
  at(key: TermLike): Term { return new Term({op: 'get', map: this.name, key: termOf(key)}) }
  set(key: TermLike, value: TermLike): MapWrite { return {map: this.name, key: termOf(key), value: termOf(value)} }
  // key's cell plus `by` where `c` holds (the counter every cap keeps).
  bump(key: TermLike, c: Cond = yes, by: TermLike = 1): MapWrite { return this.set(key, when(c, this.at(key).plus(by), this.at(key))) }
}

export type Forall = {readonly forall: (key: Term) => Cond}
// A law about every key of a map: proven at a fresh key, assumed at the keys a step reads.
export const forall = (f: (key: Term) => Cond): Forall => ({forall: f})
export type Relation = {readonly when: Cond, readonly holds: Cond}
// For histories: `holds` (a <= b, homogeneous over sums and queries) wherever `when` (params and plain inputs) holds.
export const relation = (holds: Cond, whenever: Cond = yes): Relation => ({when: whenever, holds})

// --- rules: machines -----------------------------------------------------------------------------------------------

type Kinds = Record<string, Kind<unknown>>
type ValuesOf<K extends Kinds> = {[n in keyof K]: K[n] extends Kind<infer V> ? V : never}
type Obj = object
type Update<S extends Obj, M extends Obj> = Partial<{[k in keyof S]: TermLike} & {[k in keyof M]: MapWrite}>
let keyCounter = 0

type Spec = {
  name: string
  params: [string, Kind<unknown>][]
  inputs: [string, Kind<unknown>][]
  state: [string, number | ((p: never) => TermLike)][]
  maps: [string, number][]
  flags: ((env: never) => Record<string, Cond>)[]
  step?: (env: never) => Record<string, TermLike | MapWrite | undefined>
  pre: ((p: never) => Cond)[]
  assume: ((env: never) => Cond)[]
  record?: string[]
  sums: [string, (r: never, p: never) => TermLike][]
  queries: [string, (r: never, v: never) => TermLike][]
  keep?: (env: never) => Cond
  relations?: (env: never) => Relation[]
  prune?: {order: string, after: (p: never) => TermLike}
}

// P params, I inputs, S state, M maps, F flags, R a history's record, Su its sums, Q its queries: each a record of the
// values the builders hand out, grown by each call.
export class Rule<P extends Obj = {}, I extends Obj = {}, S extends Obj = {}, M extends Obj = {}, F extends Obj = {}, R extends Obj = {}, Su extends Obj = {}, Q extends Obj = {}> {
  constructor(private readonly spec: Spec) {}
  private with(more: Partial<Spec>): never { return new Rule({...this.spec, ...more}) as never }
  get name() { return this.spec.name }

  params<K extends Kinds>(kinds: K): Rule<P & ValuesOf<K>, I, S, M, F, R, Su, Q> { return this.with({params: [...this.spec.params, ...Object.entries(kinds)]}) }
  inputs<K extends Kinds>(kinds: K): Rule<P, I & ValuesOf<K>, S, M, F, R, Su, Q> { return this.with({inputs: [...this.spec.inputs, ...Object.entries(kinds)]}) }
  // Each variable starts at a natural or at a term over the params.
  state<T extends Record<string, number | ((p: P) => TermLike)>>(init: T): Rule<P, I, S & {[k in keyof T]: Term}, M, F, R, Su, Q> {
    return this.with({state: [...this.spec.state, ...Object.entries(init) as [string, number | ((p: never) => TermLike)][]]})
  }
  maps<T extends Record<string, number>>(init: T): Rule<P, I, S, M & {[k in keyof T]: MapRef}, F, R, Su, Q> { return this.with({maps: [...this.spec.maps, ...Object.entries(init)]}) }
  // Named conditions of the step, decided once per step before it; each call's flags may read the earlier calls'. A flag
  // named again replaces the earlier definition in place (what a variant needs: one call, the step unchanged); the new
  // definition may read only the flags defined before the original's place, as the kernel checks.
  flags<T extends Record<string, Cond>>(f: (env: P & I & S & M & F & Su & Q) => T): Rule<P, I, S, M, F & {[k in keyof T]: Cond}, R, Su, Q> {
    return this.with({flags: [...this.spec.flags, f as (env: never) => Record<string, Cond>]})
  }
  // The step (replaces an earlier one, so a variant is one call away): its updates read the state before it.
  step(f: (env: P & I & S & M & F & Su & Q) => Update<S, M>): Rule<P, I, S, M, F, R, Su, Q> {
    return this.with({step: f as (env: never) => Record<string, TermLike | MapWrite | undefined>})
  }
  // A precondition on the params: the laws are claimed only for params that meet it.
  pre(f: (p: P) => Cond): Rule<P, I, S, M, F, R, Su, Q> { return this.with({pre: [...this.spec.pre, f as (p: never) => Cond]}) }
  // What every request satisfies (with the input kinds' own assumptions): it holds at each step, not at the start.
  assume(f: (env: P & I & S & M & F & Su & Q) => Cond): Rule<P, I, S, M, F, R, Su, Q> { return this.with({assume: [...this.spec.assume, f as (env: never) => Cond]}) }

  // A history: the requests the step keeps, each recorded with these inputs.
  log<const N extends keyof I & string>(...record: N[]): Rule<P, I, S, M, F, Pick<I, N>, Su, Q> { return this.with({record}) }
  // State equal to the sum over the history of a term of the record and the params.
  sums<T extends Record<string, (r: R, p: P) => TermLike>>(sums: T): Rule<P, I, S, M, F, R, Su & {[k in keyof T]: Term}, Q> {
    return this.with({sums: [...this.spec.sums, ...Object.entries(sums) as [string, (r: never, p: never) => TermLike][]]})
  }
  // An input the runtime computes: the sum over the history before the request of a term of the record, the params and
  // the request's other inputs.
  queries<T extends Record<string, (r: R, v: P & I) => TermLike>>(queries: T): Rule<P, I, S, M, F, R, Su, Q & {[k in keyof T]: Term}> {
    return this.with({queries: [...this.spec.queries, ...Object.entries(queries) as [string, (r: never, v: never) => TermLike][]]})
  }
  keep(f: (env: P & I & S & M & F & Su & Q) => Cond): Rule<P, I, S, M, F, R, Su, Q> { return this.with({keep: f as (env: never) => Cond}) }
  relations(f: (env: P & I & Su & Q) => Relation[]): Rule<P, I, S, M, F, R, Su, Q> { return this.with({relations: f as (env: never) => Relation[]}) }
  // Requests come in nondecreasing `order`; a record whose order plus `after` is at most the request's is dropped
  // (the kernel proves it adds nothing to any query).
  prune(order: keyof R & string, after: (p: P) => TermLike): Rule<P, I, S, M, F, R, Su, Q> { return this.with({prune: {order, after: after as (p: never) => TermLike}}) }

  // A law about the params, the state, the maps and the sums (not a request): `forall` for every key of a map.
  law(name: string, f: (env: P & S & M & Su) => Cond | Forall): Law {
    const out = f(this.env({flags: false, inputs: false, queries: false}) as never)
    if (out instanceof Cond) return {name, holds: out.c}
    const key = `key$${++keyCounter}`
    return {name, forall: key, holds: out.forall(v(key)).c}
  }

  // A decision: whenever the params and the request meet `given`, `then` holds. Decisions don't read the state.
  decide(name: string, given: (env: P & I) => Cond | Cond[], then: (env: P & I) => Cond): Decision {
    const env = this.env({flags: false, state: false, queries: false}) as never
    const g = given(env), hyps = [...this.kindAssumptions(), ...this.spec.pre.map(f => f(env as never).c), ...this.spec.assume.map(f => f(env as never).c), ...(Array.isArray(g) ? g : [g]).map(c => c.c)]
    const t = then(env).c
    return {name, rule: this as Rule<Obj>, given: hyps, then: t, goal: {name, hyps: [...hyps, {op: 'not', x: t}]}}
  }

  // --- what it compiles to ------------------------------------------------------------------------------------------
  private kindAssumptions(which: 'params' | 'inputs' | 'both' = 'both'): C[] {
    const ps = which === 'inputs' ? [] : this.spec.params.flatMap(([n, k]) => k.assume(n))
    const is = which === 'params' ? [] : this.spec.inputs.flatMap(([n, k]) => k.assume(n))
    return [...ps, ...is].map(c => c.c)
  }
  // The values handed to the builders' callbacks.
  private env(parts: {inputs?: boolean, state?: boolean, flags?: boolean, queries?: boolean} = {}): Record<string, unknown> {
    const out: Record<string, unknown> = {}
    for (const [n, k] of this.spec.params) out[n] = k.value(n)
    if (parts.inputs !== false) for (const [n, k] of this.spec.inputs) out[n] = k.value(n)
    if (parts.state !== false) {
      for (const [n] of this.spec.state) out[n] = v(n)
      for (const [n, init] of this.spec.maps) out[n] = new MapRef(n, init)
      for (const [n] of this.spec.sums) out[n] = v(n)
    }
    if (parts.queries !== false) for (const [n] of this.spec.queries) out[n] = v(n)
    if (parts.flags !== false) for (const f of this.spec.flags) for (const n of Object.keys(f(out as never))) out[n] = new Cond({op: 'flag', name: n})
    return out
  }
  get machine(): Machine {
    const s = this.spec
    const params = s.params.flatMap(([n, k]) => k.vars(n)), queries = s.queries.map(([n]) => n)
    const inputs = [...s.inputs.flatMap(([n, k]) => k.vars(n)), ...queries]
    const pEnv = this.env({inputs: false, state: false, flags: false, queries: false})
    const env: Record<string, unknown> = this.env({flags: false})
    const flags: Record<string, C> = {}
    for (const f of s.flags) for (const [n, c] of Object.entries(f(env as never))) { flags[n] = c.c; env[n] = new Cond({op: 'flag', name: n}) } // a name again: replaced in place
    const updates = s.step?.(env as never) ?? {}
    const state: Record<string, E> = {}, maps: Record<string, {key: E, value: E}> = {}
    for (const [n, u] of Object.entries(updates)) {
      if (u === undefined) continue
      if (typeof u === 'object' && 'map' in u) {
        if (u.map !== n) throw new Error(`${s.name}: the step writes map ${u.map} under the name ${n}`)
        maps[n] = {key: u.key, value: u.value}
      } else state[n] = termOf(u)
    }
    const pre = [...this.kindAssumptions('params'), ...s.pre.map(f => f(pEnv as never).c)]
    const assume = [...this.kindAssumptions('inputs'), ...s.assume.map(f => f(env as never).c)]
    const m: Machine = {
      name: s.name, params, inputs,
      state: Object.fromEntries(s.state.map(([n, init]) => [n, typeof init === 'number' ? termOf(init) : termOf(init(pEnv as never))])),
      ...(s.maps.length ? {maps: Object.fromEntries(s.maps)} : {}),
      step: {...(Object.keys(flags).length ? {flags} : {}), ...(Object.keys(state).length ? {state} : {}), ...(Object.keys(maps).length ? {maps} : {})},
      ...(pre.length ? {pre: pre.length === 1 ? pre[0]! : {op: 'and', xs: pre}} : {}),
      ...(assume.length ? {assume: assume.length === 1 ? assume[0]! : {op: 'and', xs: assume}} : {}),
    }
    if (s.record) {
      const kinds = new Map(s.inputs)
      const record = Object.fromEntries(s.record.map(n => [n, kinds.get(n)!.value(n, 'r.')]))
      const plain = this.env({state: false, flags: false, queries: false})
      const rv = Object.fromEntries(Object.entries(env).filter(([n]) => queries.includes(n) || s.sums.some(([sn]) => sn === n) || n in plain))
      const pruneOrder = s.prune ? kinds.get(s.prune.order)!.vars(s.prune.order) : undefined
      if (pruneOrder && pruneOrder.length !== 1) throw new Error(`${s.name}: a history is pruned by a single-variable input`)
      m.history = {
        keep: (s.keep?.(env as never) ?? yes).c,
        record: s.record.flatMap(n => kinds.get(n)!.vars(n)),
        sums: Object.fromEntries(s.sums.map(([n, f]) => [n, termOf(f(record as never, pEnv as never))])),
        queries: Object.fromEntries(s.queries.map(([n, f]) => [n, termOf(f(record as never, plain as never))])),
        ...(s.relations ? {relations: s.relations(rv as never).map(r => ({when: r.when.c, holds: r.holds.c}))} : {}),
        ...(s.prune ? {prune: {order: pruneOrder![0]!, after: termOf(s.prune.after(pEnv as never))}} : {}),
      }
    }
    return m
  }

  // --- running it -----------------------------------------------------------------------------------------------------
  // Runtime values (numbers, booleans, choice names, null for a missing value) to the variables the machine reads.
  encodeParams(values: {[k in keyof P]: Raw}): Record<string, number> { return encode(this.spec.params, values as Record<string, Raw>) }
  encodeInput(values: {[k in keyof I]: Raw}): Record<string, number> { return encode(this.spec.inputs, values as Record<string, Raw>) }
  // Random params and inputs that meet their kinds (not the user's `pre` or `assume`, which a caller checks).
  randomParams(rand: Rand, bound: number): Record<string, number> { return Object.assign({}, ...this.spec.params.map(([n, k]) => k.random(n, rand, bound))) }
  randomInput(rand: Rand, bound: number): Record<string, number> { return Object.assign({}, ...this.spec.inputs.map(([n, k]) => k.random(n, rand, bound))) }
  // The prune order's variable, if the history is pruned (a runtime must send it nondecreasing).
  get orderedBy(): string | undefined { return this.spec.prune ? new Map(this.spec.inputs).get(this.spec.prune.order)!.vars(this.spec.prune.order)[0] : undefined }
  interpreter() { return interpret(this.machine) }
  compiled(): {init: (params: object) => State & {head?: number}, fork: (st: State) => State, step: (params: object, st: State, input: object) => State & {head?: number}} {
    return loadJs(this.machine)
  }
}
const encode = (kinds: [string, Kind<unknown>][], values: Record<string, Raw>): Record<string, number> => Object.assign({}, ...kinds.map(([n, k]) => k.encode(n, values[n])))

export const rule = (name: string): Rule => new Rule({name, params: [], inputs: [], state: [], maps: [], flags: [], pre: [], assume: [], sums: [], queries: []})

// The values a rule's callbacks receive, for helpers written outside the chain (a decision's condition, a shared law):
// `(env: DecisionEnv<typeof r>) => ...`.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyOf<R, K extends 'decide' | 'step' | 'law'> = R extends Rule<infer P, infer I, infer S, infer M, infer F, any, infer Su, infer Q> ? K extends 'decide' ? P & I : K extends 'law' ? P & S & M & Su : P & I & S & M & F & Su & Q : never
export type DecisionEnv<R> = AnyOf<R, 'decide'>
export type StepEnv<R> = AnyOf<R, 'step'>
export type LawEnv<R> = AnyOf<R, 'law'>

// --- decisions and loops ------------------------------------------------------------------------------------------

export type Decision = {name: string, rule: Rule<Obj>, given: C[], then: C, goal: Goal}

// A loop runs `body` while `while` holds, each turn with fresh inputs; it halts if a rank over the state and params
// (or a tuple of them, compared in order) drops on every turn.
export class LoopRule<P extends Obj = {}, I extends Obj = {}, S extends Obj = {}> {
  constructor(private readonly spec: {name: string, params: [string, Kind<unknown>][], inputs: [string, Kind<unknown>][], state: [string, number | ((p: never) => TermLike)][], while?: (env: never) => Cond, body?: (env: never) => Record<string, TermLike | undefined>, pre: ((p: never) => Cond)[], assume: ((env: never) => Cond)[], rank?: (env: never) => TermLike | TermLike[]}) {}
  private with(more: object): never { return new LoopRule({...this.spec, ...more}) as never }
  params<K extends Kinds>(kinds: K): LoopRule<P & ValuesOf<K>, I, S> { return this.with({params: [...this.spec.params, ...Object.entries(kinds)]}) }
  inputs<K extends Kinds>(kinds: K): LoopRule<P, I & ValuesOf<K>, S> { return this.with({inputs: [...this.spec.inputs, ...Object.entries(kinds)]}) }
  state<T extends Record<string, number | ((p: P) => TermLike)>>(init: T): LoopRule<P, I, S & {[k in keyof T]: Term}> { return this.with({state: [...this.spec.state, ...Object.entries(init)]}) }
  while(f: (env: P & S) => Cond): LoopRule<P, I, S> { return this.with({while: f}) }
  body(f: (env: P & I & S) => Partial<{[k in keyof S]: TermLike}>): LoopRule<P, I, S> { return this.with({body: f}) }
  pre(f: (p: P) => Cond): LoopRule<P, I, S> { return this.with({pre: [...this.spec.pre, f]}) }
  assume(f: (env: P & I & S) => Cond): LoopRule<P, I, S> { return this.with({assume: [...this.spec.assume, f]}) }
  rank(f: (env: P & S) => TermLike | TermLike[]): LoopRule<P, I, S> { return this.with({rank: f}) }
  law(name: string, f: (env: P & S) => Cond): Law { return {name, holds: f(this.env(false) as never).c} }
  private env(inputs = true): Record<string, unknown> {
    const out: Record<string, unknown> = {}
    for (const [n, k] of this.spec.params) out[n] = k.value(n)
    if (inputs) for (const [n, k] of this.spec.inputs) out[n] = k.value(n)
    for (const [n] of this.spec.state) out[n] = v(n)
    return out
  }
  get loop(): Loop {
    const s = this.spec, env = this.env(), pEnv = Object.fromEntries(s.params.map(([n, k]) => [n, k.value(n)]))
    if (!s.while || !s.body) throw new Error(`${s.name}: a loop needs while and body`)
    const pre = [...s.params.flatMap(([n, k]) => k.assume(n)).map(c => c.c), ...s.pre.map(f => f(pEnv as never).c)]
    const assume = [...s.inputs.flatMap(([n, k]) => k.assume(n)).map(c => c.c), ...s.assume.map(f => f(env as never).c)]
    return {
      name: s.name, params: s.params.flatMap(([n, k]) => k.vars(n)), inputs: s.inputs.flatMap(([n, k]) => k.vars(n)),
      state: Object.fromEntries(s.state.map(([n, init]) => [n, typeof init === 'number' ? termOf(init) : termOf(init(pEnv as never))])),
      while: s.while(env as never).c,
      body: Object.fromEntries(Object.entries(s.body(env as never)).filter(([, t]) => t !== undefined).map(([n, t]) => [n, termOf(t!)])),
      ...(pre.length ? {pre: pre.length === 1 ? pre[0]! : {op: 'and', xs: pre}} : {}),
      ...(assume.length ? {assume: assume.length === 1 ? assume[0]! : {op: 'and', xs: assume}} : {}),
    }
  }
  get rankTerms(): E[] {
    if (!this.spec.rank) throw new Error(`${this.spec.name}: no rank`)
    const r = this.spec.rank(this.env(false) as never)
    return (Array.isArray(r) ? r : [r]).map(termOf)
  }
  randomParams(rand: Rand, bound: number): Record<string, number> { return Object.assign({}, ...this.spec.params.map(([n, k]) => k.random(n, rand, bound))) }
  randomInput(rand: Rand, bound: number): Record<string, number> { return Object.assign({}, ...this.spec.inputs.map(([n, k]) => k.random(n, rand, bound))) }
}
export const loop = (name: string): LoopRule => new LoopRule({name, params: [], inputs: [], state: [], pre: [], assume: []})

// --- proving ---------------------------------------------------------------------------------------------------------

export type Verdict = {proven: boolean, checked: boolean, stuck?: string, goal?: string, witness?: Record<string, number>, trees?: Record<string, Tree>}
const goalsVerdict = (goals: Goal[]): Verdict => {
  const trees: Record<string, Tree> = {}
  for (const g of goals) {
    const out = grow(g)
    if (!('tree' in out)) return {proven: false, checked: false, goal: g.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {})}
    trees[g.name] = out.tree
  }
  return {proven: true, checked: goals.every(g => check(g, trees[g.name]!)), trees}
}
export function proveRule(r: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, laws: Law[]): Verdict {
  const out = proveLaws(r.machine, laws)
  return {proven: out.proven, checked: out.checked, ...(out.failed ? {goal: out.failed.goal, stuck: out.failed.stuck, ...(out.failed.witness ? {witness: out.failed.witness} : {})} : {})}
}
export const proveDecision = (d: Decision): Verdict => goalsVerdict([d.goal])
export const proveLoop = (l: LoopRule<Obj, Obj, Obj>, laws: Law[]): Verdict => goalsVerdict(loopObligations(l.loop, laws, l.rankTerms))
