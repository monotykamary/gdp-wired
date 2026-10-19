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
import {type C, type E, type Fn, type Law, type Machine, type MapUpdate, type Request, type State, carriedView, compileFunction, evalC, interpret, loadJs, numbersOf} from './machine.ts'
import {allowed, keysOf, requestEnv, watch} from './watch.ts'
import {type Goal, type Liveness, type Loop, type StepLaw, type Tree, check, loopObligations} from '../kernel/kernel.ts'
import {factsFor, grow, proveLaws, proveLiveness, proveStepLaws} from '../kernel/prove.ts'

// --- terms and conditions -------------------------------------------------------------------------------------------

const naturalConst = (v: number): number => {
  if (!Number.isSafeInteger(v) || v < 0) throw new RangeError(`${v} is not a natural`)
  return v
}
export type TermLike = Term | number
export const termOf = (t: TermLike): E => {
  if (typeof t === 'number') return {op: 'const', value: naturalConst(t)}
  if (!(t instanceof Term)) throw new TypeError('a natural is expected here; an integer or a decimal compares from its own side (x.atMost(n))')
  return t.e
}

// A natural-valued term. `minus` is truncated (a ∸ b), `times` multiplies by a constant, `mul` by another term (a
// product: the kernel proves with it, the GPU searches don't take it).
//
// Each term and condition may also carry its value (`val`, `ok`), computed beside its expression by plain JavaScript
// when every value it reads is known: what `crossCheck` compares with the expression the interpreter evaluates, so a
// builder that writes a different expression than it means is caught on concrete runs.
export class Term {
  constructor(readonly e: E, readonly val?: number) {}
  plus(b: TermLike): Term { return new Term({op: 'add', a: this.e, b: termOf(b)}, both(this.val, valOf(b), (x, y) => x + y)) }
  minus(b: TermLike): Term { return new Term({op: 'sub', a: this.e, b: termOf(b)}, both(this.val, valOf(b), (x, y) => Math.max(0, x - y))) }
  times(k: number): Term { return new Term({op: 'mul', k: naturalConst(k), a: this.e}, both(this.val, k, (x, y) => x * y)) }
  mul(b: TermLike): Term { return new Term({op: 'prod', a: this.e, b: termOf(b)}, both(this.val, valOf(b), (x, y) => x * y)) }
  lt(b: TermLike): Cond { return new Cond({op: '<', a: this.e, b: termOf(b)}, both(this.val, valOf(b), (x, y) => x < y)) }
  atMost(b: TermLike): Cond { return new Cond({op: '<=', a: this.e, b: termOf(b)}, both(this.val, valOf(b), (x, y) => x <= y)) }
  gt(b: TermLike): Cond { return new Cond({op: '<', a: termOf(b), b: this.e}, both(this.val, valOf(b), (x, y) => x > y)) }
  atLeast(b: TermLike): Cond { return new Cond({op: '<=', a: termOf(b), b: this.e}, both(this.val, valOf(b), (x, y) => x >= y)) }
  eq(b: TermLike): Cond { return new Cond({op: '=', a: this.e, b: termOf(b)}, both(this.val, valOf(b), (x, y) => x === y)) }
  ne(b: TermLike): Cond { return this.eq(b).not() }
}
const valOf = (t: TermLike): number | undefined => (typeof t === 'number' ? t : t instanceof Term ? t.val : undefined)
const both = <T>(a: number | undefined, b: number | undefined, f: (a: number, b: number) => T): T | undefined => (a === undefined || b === undefined ? undefined : f(a, b))
// Every value known, or undefined.
const known = <T>(xs: (T | undefined)[]): T[] | undefined => (xs.every(x => x !== undefined) ? xs as T[] : undefined)

export class Cond {
  constructor(readonly c: C, readonly ok?: boolean) {}
  and(...xs: Cond[]): Cond { return all(this, ...xs) }
  or(...xs: Cond[]): Cond { return any(this, ...xs) }
  not(): Cond { return new Cond({op: 'not', x: this.c}, this.ok === undefined ? undefined : !this.ok) }
  implies(b: Cond): Cond { return any(this.not(), b) }
  iff(b: Cond): Cond { return all(this.implies(b), b.implies(this)) }
}

export const lit = (v: number): Term => new Term(termOf(v), v)
export const yes = new Cond({op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}, true)
export const no = new Cond({op: '<', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}, false)
export const all = (...cs: Cond[]): Cond => (cs.length === 0 ? yes : cs.length === 1 ? cs[0]! : new Cond({op: 'and', xs: cs.map(c => c.c)}, known(cs.map(c => c.ok))?.every(x => x)))
export const any = (...cs: Cond[]): Cond => (cs.length === 0 ? no : cs.length === 1 ? cs[0]! : new Cond({op: 'or', xs: cs.map(c => c.c)}, known(cs.map(c => c.ok))?.some(x => x)))
export const not = (c: Cond): Cond => c.not()
export const min = (a: TermLike, b: TermLike): Term => new Term({op: 'min', a: termOf(a), b: termOf(b)}, both(valOf(a), valOf(b), Math.min))
export const max = (a: TermLike, b: TermLike): Term => new Term({op: 'max', a: termOf(a), b: termOf(b)}, both(valOf(a), valOf(b), Math.max))
// By cases. For a value made of several (an integer, a decimal, a choice, a string, an optional value, a condition)
// each part goes by the same case.
export function when(c: Cond, then: TermLike, otherwise: TermLike): Term
export function when(c: Cond, then: Decimal, otherwise: Decimal | number): Decimal
export function when(c: Cond, then: Decimal | number, otherwise: Decimal): Decimal
export function when(c: Cond, then: IntLike, otherwise: IntLike): Int
export function when<K extends string>(c: Cond, then: Choice<K>, otherwise: Choice<K>): Choice<K>
export function when(c: Cond, then: Str, otherwise: Str): Str
export function when<V>(c: Cond, then: Maybe<V>, otherwise: Maybe<V>): Maybe<V>
export function when(c: Cond, then: Cond, otherwise: Cond): Cond
export function when(c: Cond, then: unknown, otherwise: unknown): unknown {
  if (then instanceof Cond && otherwise instanceof Cond) return choose(c, then, otherwise)
  if (then instanceof Choice && otherwise instanceof Choice) return new Choice(when(c, then.n, otherwise.n), then.values)
  if (then instanceof Str && otherwise instanceof Str) return then.choose(c, otherwise)
  if (then instanceof Maybe && otherwise instanceof Maybe) return new Maybe(when(c, then.present, otherwise.present), when(c, then.inner as never, otherwise.inner as never))
  return pickNumbers(c, then as IntLike | Decimal, otherwise as IntLike | Decimal)
}
function pickNumbers(c: Cond, then: IntLike | Decimal, otherwise: IntLike | Decimal): Term | Int | Decimal {
  if (then instanceof Decimal || otherwise instanceof Decimal) {
    const places = (then instanceof Decimal ? then : otherwise as Decimal).places, d = new Decimal(Int.of(0), places)
    return new Decimal(when(c, d.lift(then), d.lift(otherwise)), places)
  }
  if (then instanceof Int || otherwise instanceof Int || (typeof then === 'number' && then < 0) || (typeof otherwise === 'number' && otherwise < 0)) {
    const a = Int.of(then), b = Int.of(otherwise)
    return new Int(when(c, a.pos, b.pos), when(c, a.neg, b.neg))
  }
  return new Term({op: 'if', c: c.c, then: termOf(then), else: termOf(otherwise)}, c.ok === undefined ? undefined : valOf(c.ok ? then : otherwise))
}
// A condition by cases: `then` where c holds, `otherwise` elsewhere.
export const choose = (c: Cond, then: Cond, otherwise: Cond): Cond => any(all(c, then), all(c.not(), otherwise))
// 1 where c holds, else 0: what a sum over a history adds per record.
export const count = (c: Cond): Term => when(c, 1, 0)
export const sum = (first: TermLike, ...rest: TermLike[]): Term => rest.reduce<Term>((acc, t) => acc.plus(t), typeof first === 'number' ? lit(first) : first)

// --- kinds: what a param or input may be ------------------------------------------------------------------------------

type Rand = (k: number) => number
type Raw = number | boolean | string | null | undefined

// A kind names the variables a value is encoded in, what is assumed of them, the value the builders hand out, and how
// a runtime value is encoded and drawn at random (the examples' harness draws inputs this way). A kind is what a param,
// an input and a state variable are declared by alike: `store` writes a value back as its variables' terms (a step's
// update), `decode` reads a state's variables back as the runtime value, `from` gives a state variable its start.
// `at` renames the variables a value is read at: a prefix (a second request's `b.x`, a record's `r.x`) or any renaming
// (the state after a step, `x'`).
export type At = string | ((name: string) => string)
const named = (at: At, n: string) => (typeof at === 'string' ? at + n : at(n))
const primed = (n: string) => `${n}'`
export type Init<V> = {readonly kind: Kind<V>, readonly init: Raw | ((p: never) => unknown)}
export abstract class Kind<V> {
  declare readonly _value: V
  abstract vars(name: string): string[]
  abstract assume(name: string): Cond[]
  abstract value(name: string, at?: At): V
  abstract encode(name: string, raw: Raw): Record<string, number>
  abstract random(name: string, rand: Rand, bound: number): Record<string, number>
  abstract store(name: string, value: unknown): Record<string, TermLike>
  abstract decode(name: string, vars: Record<string, number>): Raw
  // The value a fresh state variable of the kind holds (0, false, the first choice, "", none).
  abstract empty(): Raw
  // A runtime value of the kind (what encode takes), for comparing a rule with the code it describes (compare).
  sample(_rand: Rand, _bound: number): Raw { throw new Error('this kind draws no runtime values') }
  // A state variable of this kind starting at a runtime value, or at a value over the params: `.state({open: bool.from(true)})`.
  from(init: Raw | ((p: never) => unknown)): Init<V> { return {kind: this, init} }
}
const v = (name: string) => new Term({op: 'var', name}, scope?.vars[name])
// Concrete values for the builders to carry (crossCheck): variables by name, maps' cells, the keys a condition at every
// key is decided over (undefined: not decided), flags by name.
type Scope = {vars: Record<string, number>, maps: Record<string, {cells: ReadonlyMap<number, number>, dflt: number}>, keys?: number[], flags: Record<string, boolean>}
let scope: Scope | undefined
const inScope = <T>(s: Scope, f: () => T): T => { const outer = scope; scope = s; try { return f() } finally { scope = outer } }
const keyTerm = (k: number) => new Term({op: 'const', value: k}, k)
// Keys enough to decide a condition at every key as the interpreter does: these, the key past every map's cells, and
// every key up to the values in play (where a key compared with them changes).
const exactKeys = (keys: number[], values: Record<string, number>, ...states: State[]): number[] => {
  let past = 0
  for (const st of states) for (const cells of Object.values(st.maps)) for (const k of cells.keys()) past = Math.max(past, k + 1)
  const top = Math.min(64, Math.max(0, ...Object.values(values).filter(x => x <= 64)) + 2)
  return [...new Set([...keys, past, ...Array.from({length: top + 1}, (_, i) => i)])].sort((a, b) => a - b)
}
const everyOk = (ks: number[] | undefined, f: (k: number) => boolean | undefined): boolean | undefined => {
  if (!ks) return undefined
  let out = true
  for (const k of ks) { const o = f(k); if (o === undefined) return undefined; if (!o) out = false }
  return out
}

// --- integers and decimals ------------------------------------------------------------------------------------------

// An integer, kept as two naturals: its value is pos − neg. Sums and differences add the parts, a comparison compares
// pos + b.neg with b.pos + neg, so the kernel sees only naturals and nothing new is trusted. Every operation reads only
// the value, whichever two naturals hold it; one written to the state is normalized (pos ∸ neg, neg ∸ pos).
export type IntLike = Int | Term | number
const isZero = (t: Term) => t.e.op === 'const' && t.e.value === 0
const add = (a: Term, b: Term) => (isZero(b) ? a : isZero(a) ? b : a.plus(b))
export class Int {
  constructor(readonly pos: Term, readonly neg: Term) {}
  static of(x: IntLike): Int {
    if (x instanceof Int) return x
    if (typeof x !== 'number') return new Int(x, lit(0))
    if (!Number.isSafeInteger(x)) throw new RangeError(`${x} is not an integer`)
    return x >= 0 ? new Int(lit(x), lit(0)) : new Int(lit(0), lit(-x))
  }
  plus(b: IntLike): Int { const o = Int.of(b); return new Int(add(this.pos, o.pos), add(this.neg, o.neg)) }
  minus(b: IntLike): Int { const o = Int.of(b); return new Int(add(this.pos, o.neg), add(this.neg, o.pos)) }
  negate(): Int { return new Int(this.neg, this.pos) }
  times(k: number): Int {
    if (!Number.isSafeInteger(k)) throw new RangeError(`${k} is not an integer`)
    return k >= 0 ? new Int(this.pos.times(k), this.neg.times(k)) : new Int(this.neg.times(-k), this.pos.times(-k))
  }
  lt(b: IntLike): Cond { const o = Int.of(b); return add(this.pos, o.neg).lt(add(o.pos, this.neg)) }
  atMost(b: IntLike): Cond { const o = Int.of(b); return add(this.pos, o.neg).atMost(add(o.pos, this.neg)) }
  gt(b: IntLike): Cond { return Int.of(b).lt(this) }
  atLeast(b: IntLike): Cond { return Int.of(b).atMost(this) }
  eq(b: IntLike): Cond { const o = Int.of(b); return add(this.pos, o.neg).eq(add(o.pos, this.neg)) }
  ne(b: IntLike): Cond { return this.eq(b).not() }
  min(b: IntLike): Int { return when(this.atMost(b), this, b) }
  max(b: IntLike): Int { return when(this.atLeast(b), this, b) }
  get isNegative(): Cond { return this.neg.gt(this.pos) }
  // |value|, and the value where it is not negative (0 below).
  get abs(): Term { return this.pos.minus(this.neg).plus(this.neg.minus(this.pos)) }
  get clamped(): Term { return this.pos.minus(this.neg) }
}

// A decimal with a fixed number of places: an integer counting 10^-places (cents, at 2). Numbers written in it are
// scaled (12.5 at 2 places is 1250; one that needs more places is refused), and whole values are scaled up.
export type DecimalLike = Decimal | IntLike
// The same value with at most one part nonzero (what a state variable holds).
const normal = (i: Int): Int => (isZero(i.neg) || isZero(i.pos) ? i : new Int(i.pos.minus(i.neg), i.neg.minus(i.pos)))
const scaledOf = (x: number | string, places: number, what = 'a decimal'): number => {
  const text = typeof x === 'number' ? x.toFixed(places + 3) : x.trim()
  const m = /^(-?)(\d+)(?:\.(\d+))?$/.exec(text)
  if (!m) throw new RangeError(`${String(x)} is not ${what}`)
  const frac = (m[3] ?? '').replace(/0+$/, '')
  if (frac.length > places) throw new RangeError(`${String(x)} needs more than ${places} decimal places`)
  const n = Number(m[2]) * 10 ** places + Number(frac.padEnd(places, '0') || '0')
  if (!Number.isSafeInteger(n)) throw new RangeError(`${String(x)} is too large`)
  return m[1] && n !== 0 ? -n : n
}
export class Decimal {
  constructor(readonly int: Int, readonly places: number) {}
  lift(b: DecimalLike): Int {
    if (b instanceof Decimal) {
      if (b.places !== this.places) throw new Error(`decimals with ${this.places} and ${b.places} places don't mix`)
      return b.int
    }
    return typeof b === 'number' ? Int.of(scaledOf(b, this.places)) : Int.of(b).times(10 ** this.places)
  }
  private with(i: Int): Decimal { return new Decimal(i, this.places) }
  plus(b: DecimalLike): Decimal { return this.with(this.int.plus(this.lift(b))) }
  minus(b: DecimalLike): Decimal { return this.with(this.int.minus(this.lift(b))) }
  negate(): Decimal { return this.with(this.int.negate()) }
  times(k: number): Decimal { return this.with(this.int.times(k)) }
  lt(b: DecimalLike): Cond { return this.int.lt(this.lift(b)) }
  atMost(b: DecimalLike): Cond { return this.int.atMost(this.lift(b)) }
  gt(b: DecimalLike): Cond { return this.int.gt(this.lift(b)) }
  atLeast(b: DecimalLike): Cond { return this.int.atLeast(this.lift(b)) }
  eq(b: DecimalLike): Cond { return this.int.eq(this.lift(b)) }
  ne(b: DecimalLike): Cond { return this.int.ne(this.lift(b)) }
  min(b: DecimalLike): Decimal { return this.with(this.int.min(this.lift(b))) }
  max(b: DecimalLike): Decimal { return this.with(this.int.max(this.lift(b))) }
  get isNegative(): Cond { return this.int.isNegative }
}
const asNat = (name: string, raw: Raw): number => {
  if (typeof raw !== 'number' || !Number.isSafeInteger(raw) || raw < 0) throw new RangeError(`${name} must be a natural, not ${String(raw)}`)
  return raw
}

class NatKind extends Kind<Term> {
  constructor(readonly maxValue?: number) { super() }
  vars(name: string) { return [name] }
  assume(name: string) { return this.maxValue === undefined ? [] : [v(name).atMost(this.maxValue)] }
  value(name: string, at: At = '') { return v(named(at, name)) }
  store(name: string, value: unknown) { return {[name]: value as TermLike} }
  decode(name: string, vars: Record<string, number>) { return vars[name]! }
  empty() { return 0 }
  encode(name: string, raw: Raw) {
    const n = asNat(name, raw)
    if (this.maxValue !== undefined && n > this.maxValue) throw new RangeError(`${name} is at most ${this.maxValue}, not ${n}`)
    return {[name]: n}
  }
  random(name: string, rand: Rand, bound: number) { return {[name]: rand((this.maxValue ?? bound) + 1)} }
  sample(rand: Rand, bound: number) { return this.maxValue !== undefined && rand(8) === 0 ? this.maxValue : rand((this.maxValue ?? bound) + 1) }
}
export const nat: Kind<Term> = new NatKind()
// A natural known to be at most `maxValue` (a percentage, a floor number, a weekday).
export const upTo = (maxValue: number): Kind<Term> => new NatKind(naturalConst(maxValue))

// A yes/no value, encoded as 0 or 1. It is a condition; `.n` is its 0/1 term (to add or count it).
export class Bool extends Cond {
  constructor(readonly n: Term) { super({op: '=', a: n.e, b: {op: 'const', value: 1}}, n.val === undefined ? undefined : n.val === 1) }
}
class BoolKind extends Kind<Bool> {
  vars(name: string) { return [name] }
  assume(name: string) { return [v(name).atMost(1)] }
  value(name: string, at: At = '') { return new Bool(v(named(at, name))) }
  store(name: string, value: unknown) { return {[name]: typeof value === 'boolean' ? (value ? 1 : 0) : count(value as Cond)} }
  decode(name: string, vars: Record<string, number>) { return vars[name] === 1 }
  empty() { return false }
  encode(name: string, raw: Raw) {
    if (typeof raw === 'boolean') return {[name]: raw ? 1 : 0}
    if (raw === 0 || raw === 1) return {[name]: raw}
    throw new RangeError(`${name} must be a boolean, not ${String(raw)}`)
  }
  random(name: string, rand: Rand) { return {[name]: rand(2)} }
  sample(rand: Rand) { return rand(2) === 1 }
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
  value(name: string, at: At = '') { return new Choice(v(named(at, name)), this.values) }
  store(name: string, value: unknown) { return {[name]: value instanceof Choice ? value.n : this.encode(name, value as Raw)[name]!} }
  decode(name: string, vars: Record<string, number>) { return this.values[vars[name]!]! }
  empty() { return this.values[0]! }
  encode(name: string, raw: Raw) {
    const i = this.values.indexOf(raw as K)
    if (i < 0) throw new RangeError(`${name} is one of ${this.values.join(', ')}, not ${String(raw)}`)
    return {[name]: i}
  }
  random(name: string, rand: Rand) { return {[name]: rand(this.values.length)} }
  sample(rand: Rand) { return this.values[rand(this.values.length)]! }
}
export const oneOf = <const K extends string>(...values: K[]): Kind<Choice<K>> => new OneOfKind(values)

// A value that may be missing, encoded as a presence bit and the value. The value can only be read in `some`, so no
// law or step can read a missing value; the encoding leaves it unconstrained when missing, so nothing proven depends
// on it.
export class Maybe<V> {
  constructor(readonly present: Term, readonly inner: V) {}
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
  value(name: string, at: At = '') { return new Maybe(v(named(at, this.has(name))), this.of.value(name, at)) }
  // null for none, a Maybe as it is, any other value as some.
  store(name: string, value: unknown) {
    if (value === null || value === undefined) return {[this.has(name)]: 0, ...this.of.store(name, this.of.empty())}
    if (value instanceof Maybe) return {[this.has(name)]: value.present, ...this.of.store(name, value.inner)}
    return {[this.has(name)]: 1, ...this.of.store(name, value)}
  }
  decode(name: string, vars: Record<string, number>) { return vars[this.has(name)] === 1 ? this.of.decode(name, vars) : null }
  empty() { return null }
  encode(name: string, raw: Raw) {
    if (raw === null || raw === undefined) return {[this.has(name)]: 0, ...Object.fromEntries(this.of.vars(name).map(n => [n, 0]))}
    return {[this.has(name)]: 1, ...this.of.encode(name, raw)}
  }
  random(name: string, rand: Rand, bound: number) {
    return rand(4) === 0 ? {[this.has(name)]: 0, ...Object.fromEntries(this.of.vars(name).map(n => [n, rand(bound + 1)]))} : {[this.has(name)]: 1, ...this.of.random(name, rand, bound)}
  }
  sample(rand: Rand, bound: number) { return rand(4) === 0 ? null : this.of.sample(rand, bound) }
}
export const maybe = <V>(of: Kind<V>): Kind<Maybe<V>> => new MaybeKind(of)

// A string, encoded as its interned name, its length and one bit per pattern the kind declares (`like`, Cedar's glob:
// `*` any run of characters, `\*` a star): all computed from the string itself when the input is encoded, so the bits
// are the string's, not an answer someone supplies. Names come from one table per process, the empty string 0; a law
// compares strings by name. Equal strings have equal lengths and pattern bits, and `eq` says so, with a literal or with
// another string, so a law may reason from either. (Names are this process's: state that keeps them across processes
// keeps `interned()` with them, and `intern.load` restores it before any rule is built.)
const internTable = new Map<string, number>([['', 0]])
// The strings rules and laws name as literals (what random draws favor).
const literals = new Set<string>([''])
const literal = (text: string): number => (literals.add(text), intern(text))
export const intern = Object.assign((text: string): number => {
  let id = internTable.get(text)
  if (id === undefined) internTable.set(text, (id = internTable.size))
  return id
}, {load(entries: [string, number][]) { for (const [text, id] of entries) { if (internTable.has(text) && internTable.get(text) !== id) throw new Error(`"${text}" is interned as ${internTable.get(text)} already`); internTable.set(text, id) } }})
export const interned = (): [string, number][] => [...internTable]
export const globMatch = (pattern: string, text: string): boolean => {
  const parts: string[][] = [[]]
  for (let i = 0; i < pattern.length; i++) {
    if (pattern[i] === '\\' && pattern[i + 1] === '*') { parts.at(-1)!.push('*'); i++ } else if (pattern[i] === '*') parts.push([]); else parts.at(-1)!.push(pattern[i]!)
  }
  const lits = parts.map(p => p.join(''))
  if (lits.length === 1) return text === lits[0]
  if (!text.startsWith(lits[0]!) || !text.endsWith(lits.at(-1)!) || text.length < lits[0]!.length + lits.at(-1)!.length) return false
  let at = lits[0]!.length
  const end = text.length - lits.at(-1)!.length
  for (const lit of lits.slice(1, -1)) { const i = text.indexOf(lit, at); if (i < 0 || i + lit.length > end) return false; at = i + lit.length }
  return true
}
export class Str {
  constructor(readonly id: Term, readonly length: Term, private readonly bits: ReadonlyMap<string, Term>) {}
  get patterns(): string[] { return [...this.bits.keys()] }
  // This string where c holds, else `other` (the patterns both declare).
  choose(c: Cond, other: Str): Str { return new Str(when(c, this.id, other.id), when(c, this.length, other.length), new Map([...this.bits].filter(([p]) => other.bits.has(p)).map(([p, b]) => [p, when(c, b, other.bits.get(p)!)]))) }
  // The string matches `pattern`, one the kind declared.
  like(pattern: string): Cond {
    const b = this.bits.get(pattern)
    if (!b) throw new Error(`like("${pattern}"): declare the pattern on the kind (str({like: [...]})); declared: ${[...this.bits.keys()].join(', ') || 'none'}`)
    return b.eq(1)
  }
  get isEmpty(): Cond { return this.id.eq(0) }
  // A declared pattern's bit (0 or 1).
  bit(pattern: string): Term { const b = this.bits.get(pattern); if (!b) throw new Error(`no pattern "${pattern}" on this string`); return b }
  eq(b: Str | string): Cond {
    if (typeof b === 'string') return all(this.id.eq(literal(b)), this.length.eq(b.length), ...[...this.bits].map(([p, bit]) => bit.eq(globMatch(p, b) ? 1 : 0)))
    return all(this.id.eq(b.id), this.length.eq(b.length), ...[...this.bits].filter(([p]) => b.bits.has(p)).map(([p, bit]) => bit.eq(b.bits.get(p)!)))
  }
  ne(b: Str | string): Cond { return typeof b === 'string' ? this.id.ne(literal(b)) : this.id.ne(b.id) }
}
class StrKind extends Kind<Str> {
  constructor(readonly patterns: readonly string[], readonly maxLength?: number) { super() }
  private bit(name: string, i: number) { return `${name}$like${i}` }
  vars(name: string) { return [name, `${name}$len`, ...this.patterns.map((_, i) => this.bit(name, i))] }
  assume(name: string) {
    return [v(name).eq(0).iff(v(`${name}$len`).eq(0)), ...(this.maxLength === undefined ? [] : [v(`${name}$len`).atMost(this.maxLength)]),
      ...this.patterns.map((p, i) => (p.replaceAll('\\*', '').includes('*') ? v(this.bit(name, i)).atMost(1) : v(this.bit(name, i)).eq(1).iff(v(name).eq(literal(p.replaceAll('\\*', '*'))))))]
  }
  value(name: string, at: At = '') { return new Str(v(named(at, name)), v(named(at, `${name}$len`)), new Map(this.patterns.map((p, i) => [p, v(named(at, this.bit(name, i)))]))) }
  store(name: string, value: unknown) {
    if (typeof value === 'string') return {[name]: literal(value), [`${name}$len`]: value.length, ...Object.fromEntries(this.patterns.map((p, i) => [this.bit(name, i), globMatch(p, value) ? 1 : 0]))}
    const t = value as Str
    return {[name]: t.id, [`${name}$len`]: t.length, ...Object.fromEntries(this.patterns.map((p, i) => [this.bit(name, i), t.bit(p)]))}
  }
  decode(name: string, vars: Record<string, number>) { const id = vars[name]!; for (const [text, n] of internTable) if (n === id) return text; throw new Error(`${name}: no string is interned as ${id}`) }
  empty() { return '' }
  encode(name: string, raw: Raw) {
    if (typeof raw !== 'string') throw new RangeError(`${name} must be a string, not ${String(raw)}`)
    if (this.maxLength !== undefined && raw.length > this.maxLength) throw new RangeError(`${name} is at most ${this.maxLength} characters`)
    return {[name]: intern(raw), [`${name}$len`]: raw.length, ...Object.fromEntries(this.patterns.map((p, i) => [this.bit(name, i), globMatch(p, raw) ? 1 : 0]))}
  }
  // Strings drawn so each pattern matches some of them (the patterns with their stars filled), every string named
  // as a literal (what the rule and its laws compare with), and short strings over their characters.
  random(name: string, rand: Rand, bound: number) { return this.encode(name, this.sample(rand, bound)) }
  sample(rand: Rand, bound: number) {
    const chars = [...new Set(['a', 'b', ...Array.from(this.patterns.join('').replaceAll('*', ''))])]
    const pool = [...this.patterns.flatMap(p => [p.replaceAll('*', ''), p.replaceAll('*', chars[rand(chars.length)]!)]), ...literals]
    const text = rand(2) === 0 ? pool[rand(pool.length)]! : Array.from({length: rand(Math.min(bound, 4) + 1)}, () => chars[rand(chars.length)]!).join('')
    return this.maxLength === undefined ? text : text.slice(0, this.maxLength)
  }
}
export const str = (opts: {like?: readonly string[], maxLength?: number} = {}): Kind<Str> => new StrKind(opts.like ?? [], opts.maxLength)

// A signed integer, encoded as two naturals (the value and `<name>$neg`): at most one nonzero when encoded.
class IntKind extends Kind<Int> {
  vars(name: string) { return [name, `${name}$neg`] }
  assume() { return [] }
  value(name: string, at: At = '') { return new Int(v(named(at, name)), v(named(at, `${name}$neg`))) }
  store(name: string, value: unknown) { const i = normal(Int.of(value as IntLike)); return {[name]: i.pos, [`${name}$neg`]: i.neg} }
  decode(name: string, vars: Record<string, number>) { return vars[name]! - vars[`${name}$neg`]! }
  empty() { return 0 }
  encode(name: string, raw: Raw) {
    if (typeof raw !== 'number' || !Number.isSafeInteger(raw)) throw new RangeError(`${name} must be an integer, not ${String(raw)}`)
    return {[name]: Math.max(raw, 0), [`${name}$neg`]: Math.max(-raw, 0)}
  }
  random(name: string, rand: Rand, bound: number) { const x = rand(2 * bound + 1) - bound; return {[name]: Math.max(x, 0), [`${name}$neg`]: Math.max(-x, 0)} }
  sample(rand: Rand, bound: number) { return rand(2 * bound + 1) - bound }
}
export const int: Kind<Int> = new IntKind()
// A decimal with `places` places, encoded as its integer count of 10^-places: given as a number or a string ("12.50").
class DecimalKind extends Kind<Decimal> {
  constructor(readonly places: number) { super() }
  vars(name: string) { return [name, `${name}$neg`] }
  assume() { return [] }
  value(name: string, at: At = '') { return new Decimal(new Int(v(named(at, name)), v(named(at, `${name}$neg`))), this.places) }
  store(name: string, value: unknown) {
    const i = normal(typeof value === 'string' ? Int.of(scaledOf(value, this.places)) : new Decimal(Int.of(0), this.places).lift(value as DecimalLike))
    return {[name]: i.pos, [`${name}$neg`]: i.neg}
  }
  decode(name: string, vars: Record<string, number>) { return (vars[name]! - vars[`${name}$neg`]!) / 10 ** this.places }
  empty() { return 0 }
  encode(name: string, raw: Raw) {
    if (typeof raw !== 'number' && typeof raw !== 'string') throw new RangeError(`${name} must be a decimal, not ${String(raw)}`)
    const x = scaledOf(raw, this.places, `a decimal (${name})`)
    return {[name]: Math.max(x, 0), [`${name}$neg`]: Math.max(-x, 0)}
  }
  random(name: string, rand: Rand, bound: number) { return new IntKind().random(name, rand, bound) }
  sample(rand: Rand, bound: number) { return (rand(2 * bound * 10 ** this.places + 1) - bound * 10 ** this.places) / 10 ** this.places }
}
export const decimal = (places: number): Kind<Decimal> => {
  if (!Number.isInteger(places) || places < 0 || places > 8) throw new RangeError('a decimal has 0 to 8 places')
  return new DecimalKind(places)
}

// --- maps, laws, relations ------------------------------------------------------------------------------------------

// (`concrete`: the write's values as crossCheck reads them, beside the expressions.)
export type MapWrite = {readonly map: string, readonly key: E, readonly value: E, readonly concrete?: {key?: number, value?: number}}
  | {readonly map: string, readonly each: string, readonly value: E, readonly concrete?: {at: (key: Term) => TermLike}}
let boundCounter = 0
// A condition at every key: only as a whole flag (`flags: ({...}) => ({covered: everyKey(k => ...)})`), the key read
// only as a map's key. The kernel closes it (instances where it holds, a witness where it fails).
export const everyKey = (f: (key: Term) => Cond): Cond => { const key = `k$${++boundCounter}`; return new Cond({op: 'all', key, c: f(v(key)).c}, everyOk(scope?.keys, k => f(keyTerm(k)).ok)) }
// Some key where f holds, in a law or a step law's conclusion (¬∀k. ¬f(k)): proven through a witness, a term naming the
// key, given here or found by the prover among a few candidates (kernel/prove.ts).
export const someKey = (f: (key: Term) => Cond, witness?: TermLike): Cond => {
  const key = `s$${++boundCounter}`
  const none = everyOk(scope?.keys, k => f(keyTerm(k)).not().ok)
  return new Cond({op: 'not', x: {op: 'all', key, c: f(v(key)).not().c, ...(witness === undefined ? {} : {witness: termOf(witness)})}}, none === undefined ? undefined : !none)
}
// A map from naturals to naturals, every cell starting at `init`. One write per map per step.
export class MapRef {
  private readonly cells: Scope['maps'][string] | undefined
  constructor(readonly name: string, readonly init: number) { this.cells = scope?.maps[name] }
  at(key: TermLike): Term { const k = valOf(key); return new Term({op: 'get', map: this.name, key: termOf(key)}, this.cells && k !== undefined ? this.cells.cells.get(k) ?? this.cells.dflt : undefined) }
  set(key: TermLike, value: TermLike): MapWrite { return {map: this.name, key: termOf(key), value: termOf(value), concrete: {key: valOf(key), value: valOf(value)}} }
  // key's cell plus `by` where `c` holds (the counter every cap keeps).
  bump(key: TermLike, c: Cond = yes, by: TermLike = 1): MapWrite { return this.set(key, when(c, this.at(key).plus(by), this.at(key))) }
  // Every key at once: the value at each key, the key read only as a map's key (Other.at(k)).
  each(f: (key: Term) => TermLike): MapWrite { const each = `k$${++boundCounter}`; return {map: this.name, each, value: termOf(f(v(each))), concrete: {at: f}} }
  // As a set (cells 0 or 1): a member, and, as whole flags, every member of this one in another, none shared, the same.
  has(key: TermLike): Cond { return this.at(key).atLeast(1) }
  subsetOf(other: MapRef): Cond { return everyKey(k => this.at(k).atMost(other.at(k))) }
  disjointFrom(other: MapRef): Cond { return everyKey(k => this.at(k).plus(other.at(k)).atMost(1)) }
  sameAs(other: MapRef): Cond { return everyKey(k => this.at(k).eq(other.at(k))) }
  // Over a universe of n names (keys 0 .. n − 1): every key past it holds 0 (a law, or a whole flag for a set a request
  // carries), and the set's size, the sum of its cells there (exact, given `within`).
  within(n: number): Cond { naturalConst(n); return everyKey(k => k.atLeast(n).implies(this.at(k).eq(0))) }
  sizeBelow(n: number): Term { naturalConst(n); return sum(0, ...Array.from({length: n}, (_, key) => this.at(key))) }
}

// A list: a map's positions 0 .. len − 1 and its length (the state variable <name>_len), every cell past the end 0
// (`within`, a law). An operation is a write at every key (positions shift: the key read at k ∸ 1 or k + 1, which the
// runtimes decide on breakpoints) and a new length; `apply` takes several, the first whose condition holds.
export type ListOp = {readonly when: Cond, readonly at: (k: Term) => TermLike, readonly len: TermLike}
export class ListRef {
  private readonly cells: Scope['maps'][string] | undefined
  constructor(readonly name: string, readonly len: Term) { this.cells = scope?.maps[name] }
  at(i: TermLike): Term { const k = valOf(i); return new Term({op: 'get', map: this.name, key: termOf(i)}, this.cells && k !== undefined ? this.cells.cells.get(k) ?? this.cells.dflt : undefined) }
  // Conditions: x at some position; each position below the next.
  has(x: TermLike): Cond { return everyKey(k => k.lt(this.len).implies(this.at(k).ne(x))).not() }
  sorted(): Cond { return everyKey(k => k.plus(1).lt(this.len).implies(this.at(k).lt(this.at(k.plus(1))))) }
  // Operations.
  push(x: TermLike, when: Cond = yes): ListOp { return {when, at: k => when_(k.eq(this.len), x, this.at(k)), len: this.len.plus(1)} }
  pop(when: Cond = yes): ListOp { return {when, at: k => when_(k.plus(1).eq(this.len), 0, this.at(k)), len: this.len.minus(1)} }
  set(i: TermLike, x: TermLike, when: Cond = yes): ListOp { return {when, at: k => when_(k.eq(i), x, this.at(k)), len: this.len} }
  insertAt(i: TermLike, x: TermLike, when: Cond = yes): ListOp { return {when, at: k => when_(k.lt(i), this.at(k), when_(k.eq(i), x, this.at(k.minus(1)))), len: this.len.plus(1)} }
  removeAt(i: TermLike, when: Cond = yes): ListOp { return {when, at: k => when_(k.lt(i), this.at(k), this.at(k.plus(1))), len: this.len.minus(1)} }
  // The updates for the step: the first operation whose condition holds, else the list as it was.
  apply(...ops: ListOp[]): Record<string, TermLike | MapWrite> {
    const each = `k$${++boundCounter}`
    const at = (k: Term) => ops.reduceRight<Term>((acc, op) => when_(op.when, op.at(k), acc), this.at(k))
    const len = ops.reduceRight<Term>((acc, op) => when_(op.when, op.len, acc), this.len)
    return {[this.name]: {map: this.name, each, value: at(v(each)).e, concrete: {at}}, [`${this.name}_len`]: len}
  }
  // Laws: nothing past the end; positions strictly increasing (so no name twice), as one law about every two keys.
  within(): Forall { return forall(k => this.len.atMost(k).implies(this.at(k).eq(0))) }
  increasing(): Forall { return forall((i, j) => i.lt(j).and(j.lt(this.len)).implies(this.at(i).lt(this.at(j)))) }
}
const when_ = (c: Cond, then: TermLike, otherwise: TermLike): Term => new Term({op: 'if', c: c.c, then: termOf(then), else: termOf(otherwise)}, c.ok === undefined ? undefined : valOf(c.ok ? then : otherwise))

export type Forall = {readonly forall: (key: Term, ...more: Term[]) => Cond}
// A law about every key of a map: proven at a fresh key, assumed at the keys a step reads.
// With two parameters or more, about every two keys or more: forall((i, j) => i.lt(j).implies(...)).
export function forall(f: (key: Term, key2: Term, key3: Term, key4: Term) => Cond): Forall { return {forall: f as Forall['forall']} }
// The keys a law's callback names: one, or two when it takes two.
const keysFor = (out: Forall): [string, string[]] => [`key$${++keyCounter}`, Array.from({length: Math.max(0, out.forall.length - 1)}, () => `key$${++keyCounter}`)]
export type Relation = {readonly when: Cond, readonly holds: Cond}
// For histories: `holds` (a <= b, homogeneous over sums and queries) wherever `when` (params and plain inputs) holds.
export const relation = (holds: Cond, whenever: Cond = yes): Relation => ({when: whenever, holds})

// --- quantifiers anywhere ---------------------------------------------------------------------------------------------

// The kernel takes a condition at every key as a whole flag only (decided once per step, closed both ways). Written
// anywhere else in a step (inside another flag, a term's if, a write, the assumption), it is named here as a flag of its
// own, so every part downstream sees only whole flags. A per-step truth inside such a condition (another quantifier,
// or a flag) is split out by cases: ∀k. φ(k, q) is (q ∧ ∀k. φ(k, yes)) ∨ (¬q ∧ ∀k. φ(k, no)). A quantifier that reads a
// key bound outside it is two keys at once, which no flag is.
const namesIn = (t: E | C): string[] => [...JSON.stringify(t).matchAll(/"op":"var","name":"([^"]+)"/g)].map(m => m[1]!)
function swapC(c: C, from: C, to: C): C {
  if (c === from) return to
  switch (c.op) {
    case 'not': return {op: 'not', x: swapC(c.x, from, to)}
    case 'and': case 'or': return {op: c.op, xs: c.xs.map(y => swapC(y, from, to))}
    case 'all': return {op: 'all', key: c.key, c: swapC(c.c, from, to)}
    case 'flag': return c
    case '<': case '<=': case '=': return {...c, a: swapE(c.a, from, to), b: swapE(c.b, from, to)}
  }
}
function swapE(e: E, from: C, to: C): E {
  switch (e.op) {
    case 'var': case 'const': return e
    case 'mul': return {...e, a: swapE(e.a, from, to)}
    case 'if': return {op: 'if', c: swapC(e.c, from, to), then: swapE(e.then, from, to), else: swapE(e.else, from, to)}
    case 'get': return {...e, key: swapE(e.key, from, to)}
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return {...e, a: swapE(e.a, from, to), b: swapE(e.b, from, to)}
  }
}
// The first per-step truth inside c not under a quantifier of its own: a flag, or a quantifier.
type PerStep = Extract<C, {op: 'flag' | 'all'}>
function perStep(c: C): PerStep | undefined {
  switch (c.op) {
    case 'flag': case 'all': return c
    case 'not': return perStep(c.x)
    case 'and': case 'or': for (const y of c.xs) { const p = perStep(y); if (p) return p } return undefined
    case '<': case '<=': case '=': return perStepE(c.a) ?? perStepE(c.b)
  }
}
function perStepE(e: E): PerStep | undefined {
  switch (e.op) {
    case 'var': case 'const': return undefined
    case 'mul': return perStepE(e.a)
    case 'if': return perStep(e.c) ?? perStepE(e.then) ?? perStepE(e.else)
    case 'get': return perStepE(e.key)
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return perStepE(e.a) ?? perStepE(e.b)
  }
}
class Hoister {
  readonly flags: Record<string, C> = {}
  constructor(private readonly prefix: string) {}
  private n = 0
  // c with every quantifier inside it named as a flag; `bound` the keys bound outside c.
  cond(c: C, bound: string[] = []): C {
    switch (c.op) {
      case 'all': return this.quantifier(c, bound)
      case 'flag': return c
      case 'not': return {op: 'not', x: this.cond(c.x, bound)}
      case 'and': case 'or': return {op: c.op, xs: c.xs.map(y => this.cond(y, bound))}
      case '<': case '<=': case '=': return {...c, a: this.term(c.a, bound), b: this.term(c.b, bound)}
    }
  }
  term(e: E, bound: string[] = []): E {
    switch (e.op) {
      case 'var': case 'const': return e
      case 'mul': return {...e, a: this.term(e.a, bound)}
      case 'if': return {op: 'if', c: this.cond(e.c, bound), then: this.term(e.then, bound), else: this.term(e.else, bound)}
      case 'get': return {...e, key: this.term(e.key, bound)}
      case 'add': case 'sub': case 'min': case 'max': case 'prod': return {...e, a: this.term(e.a, bound), b: this.term(e.b, bound)}
    }
  }
  // A quantifier as a flag (or, with per-step truths inside, a condition over flags).
  quantifier(q: Extract<C, {op: 'all'}>, bound: string[], name?: string): C {
    const outer = bound.filter(key => namesIn(q).includes(key))
    if (outer.length) throw new Error(`a condition at every key reads ${outer[0]}, a key bound outside it: two keys at once are outside the kernel`)
    const inner = perStep(q.c)
    if (!inner) { const f = name ?? `${this.prefix}${++this.n}`; this.flags[f] = {op: 'all', key: q.key, c: q.c}; return {op: 'flag', name: f} }
    const truth = inner.op === 'flag' ? inner : this.quantifier(inner, [...bound, q.key])
    const split = (by: C) => this.quantifier({op: 'all', key: q.key, c: swapC(q.c, inner, by)}, bound)
    return {op: 'or', xs: [{op: 'and', xs: [truth, split(yes.c)]}, {op: 'and', xs: [{op: 'not', x: truth}, split(no.c)]}]}
  }
}

// A machine built by hand (or by a combinator) with quantifiers inside its conditions, terms or writes: each named as a
// flag of its own, as the builders do.
export function nameQuantifiers(m: Machine): Machine {
  const hoist = new Hoister('all$'), flags: Record<string, C> = {}
  const placed = () => { for (const [n, c] of Object.entries(hoist.flags)) if (!(n in flags)) flags[n] = c }
  for (const [n, c] of Object.entries(m.step.flags ?? {})) {
    const out = c.op === 'all' ? hoist.quantifier(c, [], n) : hoist.cond(c)
    placed()
    if (!(n in flags)) flags[n] = out
  }
  const state = Object.fromEntries(Object.entries(m.step.state ?? {}).map(([n, e]) => [n, hoist.term(e)]))
  const maps = Object.fromEntries(Object.entries(m.step.maps ?? {}).map(([n, w]) => [n, 'each' in w ? {each: w.each, value: hoist.term(w.value, [w.each])} : {key: hoist.term(w.key), value: hoist.term(w.value)}]))
  const assume = m.assume ? hoist.cond(m.assume) : undefined
  placed()
  return {...m, step: {...(Object.keys(flags).length ? {flags} : {}), ...(m.step.state ? {state} : {}), ...(m.step.maps ? {maps} : {})}, ...(assume ? {assume} : {})}
}

// A law or a step law's conclusion with quantifiers inside, each pulled out as the law's one key: ∀k. A ∧ ∀k. B is
// ∀k. A ∧ B, and p ∨ ∀k. A is ∀k. p ∨ A when p doesn't read the key. One under an or beside a part that reads the key
// is two keys at once. A quantifier under a not is some key (someKey), left for the prover's witness.
const hasForall = (c: C, positive = true): boolean => c.op === 'all' ? positive || hasForall(c.c, positive) : c.op === 'not' ? hasForall(c.x, !positive) : c.op === 'and' || c.op === 'or' ? c.xs.some(y => hasForall(y, positive)) : false
const hasAll = (c: C | E) => JSON.stringify(c).includes('"op":"all"')
function prenex(c: C, what: string, key: string): C | undefined {
  let found = false
  const walk = (d: C, positive: boolean): C => {
    switch (d.op) {
      case 'all':
        if (!positive) return d
        found = true
        return walk(substKey(d.c, d.key, key), positive)
      case 'not': return {op: 'not', x: walk(d.x, !positive)}
      case 'and': case 'or': {
        if ((d.op === 'or') === positive && d.xs.some(y => hasForall(y, positive)) && d.xs.filter(y => hasForall(y, positive) || namesIn(y).includes(key)).length > 1) throw new Error(`${what}: a condition at every key in an or beside another part that reads a key is two keys at once`)
        return {op: d.op, xs: d.xs.map(y => walk(y, positive))}
      }
      case 'flag': return d
      case '<': case '<=': case '=':
        if (hasAll(d)) throw new Error(`${what}: a condition at every key inside a term is a flag of the rule`)
        return d
    }
  }
  const out = walk(c, true)
  return found ? out : undefined
}
const substKey = (c: C, from: string, to: string): C => JSON.parse(JSON.stringify(c).replaceAll(`"op":"var","name":"${from}"`, `"op":"var","name":"${to}"`)) as C

// --- functions from outside ------------------------------------------------------------------------------------------

// A function the rule reads and never writes, defined outside it: naturals in, a natural out. The kernel knows it only by
// its facts (laws about it at every argument, assumed and never proven here: the Lean export states them as the
// hypothesis they are, and proves them where the function's Lean definition is given). `js` computes it for the
// runtimes: its source (a function of the arguments, reading nothing else). Arguments past the first are paired into one
// key (Szudzik's pairing, in the kernel's arithmetic: a product of two terms).
export type FnDef = {arity: number, js: string | ((...args: number[]) => number), lean?: string, facts?: (f: (...args: TermLike[]) => Term) => Record<string, Cond | Forall>}
export const fn = (arity: number, js: FnDef['js'], opts: {lean?: string, facts?: FnDef['facts']} = {}): FnDef => {
  if (!Number.isInteger(arity) || arity < 1) throw new Error('a function takes one argument or more')
  return {arity, js, ...opts}
}
// x / c and x mod c, rounded down, for a constant c >= 1: each with its two facts (c·q <= x < c·q + c), which Lean's omega
// proves of `x / c`.
export const divBy = (c: number): FnDef => {
  if (!Number.isSafeInteger(c) || c < 1) throw new RangeError('divBy takes a whole number at least 1')
  return fn(1, `x => Math.floor(x / ${c})`, {lean: `fun x => x / ${c}`, facts: f => ({
    [`${c}·q(x) <= x`]: forall(x => f(x).times(c).atMost(x)),
    [`x < ${c}·q(x) + ${c}`]: forall(x => x.lt(f(x).times(c).plus(c))),
  })})
}
export const modBy = (c: number): FnDef => {
  if (!Number.isSafeInteger(c) || c < 1) throw new RangeError('modBy takes a whole number at least 1')
  // x mod c is below c, and x less it is a multiple of c: x ∸ r = c·q for the q that divBy(c) gives; as facts about r
  // alone, r <= x, r < c, and r(x + c) = r(x).
  return fn(1, `x => x % ${c}`, {lean: `fun x => x % ${c}`, facts: f => ({
    [`r(x) < ${c}`]: forall(x => f(x).lt(c)),
    [`r(x) <= x`]: forall(x => f(x).atMost(x)),
    [`r(x + ${c}) = r(x)`]: forall(x => f(x.plus(c)).eq(f(x))),
  })})
}
const pairE = (a: E, b: E): E => ({op: 'if', c: {op: '<', a, b}, then: {op: 'add', a: {op: 'prod', a: b, b}, b: a}, else: {op: 'add', a: {op: 'add', a: {op: 'prod', a, b: a}, b: a}, b}})
const argsKey = (args: E[]): E => args.slice(1).reduce(pairE, args[0]!)
// A function's JavaScript as one function of its key: its arguments unpaired (left-nested, as argsKey pairs them).
const fnSource = (name: string, d: FnDef): string => {
  const src = typeof d.js === 'string' ? d.js : String(d.js)
  let f: (...args: number[]) => number
  try { f = compileFunction<() => (...args: number[]) => number>([], `return (${src})`)(); f(...Array.from({length: d.arity}, () => 0)) } catch (e) { throw new Error(`function ${name}: its js must be a function of its arguments that reads nothing else (${(e as Error).message})`) }
  if (d.arity === 1) return src
  return `k => { const u = z => { const s = Math.floor(Math.sqrt(z)); return z - s * s < s ? [z - s * s, s] : [s, z - s * s - s]; }; const a = []; let z = k; for (let i = 1; i < ${d.arity}; i++) { const [p, q] = u(z); a.unshift(q); z = p; } a.unshift(z); return (${src})(...a); }`
}
const fnTerm = (name: string, d: FnDef) => (...args: TermLike[]): Term => {
  if (args.length !== d.arity) throw new Error(`function ${name} takes ${d.arity} argument${d.arity === 1 ? '' : 's'}`)
  const vals = known(args.map(valOf))
  return new Term({op: 'get', map: name, key: argsKey(args.map(termOf))}, vals && fnValueOf(d)(...vals))
}
// A function's JavaScript on its arguments themselves (not through the pairing the kernel reads them by).
const fnValues = new WeakMap<FnDef, (...args: number[]) => number>()
const fnValueOf = (d: FnDef) => {
  let f = fnValues.get(d)
  if (!f) { f = typeof d.js === 'function' ? d.js : compileFunction<() => (...args: number[]) => number>([], `return (${d.js})`)(); fnValues.set(d, f) }
  return f
}

// --- rules: machines -----------------------------------------------------------------------------------------------

type Kinds = Record<string, Kind<unknown>>
type ValuesOf<K extends Kinds> = {[n in keyof K]: K[n] extends Kind<infer V> ? V : never}
type Obj = object
// What a step may write to a state variable of each kind.
type Writes<V> = V extends Decimal ? DecimalLike | string : V extends Int ? IntLike : V extends Cond ? Cond | boolean : V extends Choice<infer K> ? Choice<K> | K : V extends Maybe<infer W> ? Maybe<W> | Writes<W> | null : V extends Str ? Str | string : TermLike
type Update<S extends Obj, M extends Obj> = Partial<{[k in keyof S]: Writes<S[k]>} & {[k in keyof M]: MapWrite}>
let keyCounter = 0
// The callbacks each law, step law and decision was built from, for crossCheck to run again on concrete values.
type Sources = {law?: (env: never) => Cond | Forall, step?: {then: (before: never, after: never) => Cond | Forall, when?: (before: never) => Cond}, decision?: {given: (env: never) => Cond | Cond[], then: (env: never) => Cond, own: number}}
const sources = new WeakMap<object, Sources>()
const withSource = <T extends object>(x: T, src: Sources): T => (sources.set(x, src), x)
// A k-step law's later requests are built over marked names (j:name, which no rule can declare: ':' is reserved); the
// kernel reads them as name@j.
const markedName = (name: string) => { const m = /^(\d+):(.*)$/.exec(name); return m ? `${m[2]}@${m[1]}` : name }
const markedE = (e: E): E => {
  switch (e.op) {
    case 'var': return {op: 'var', name: markedName(e.name)}
    case 'const': return e
    case 'mul': return {...e, a: markedE(e.a)}
    case 'if': return {op: 'if', c: marked(e.c), then: markedE(e.then), else: markedE(e.else)}
    case 'get': return {op: 'get', map: e.map, key: markedE(e.key)}
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return {...e, a: markedE(e.a), b: markedE(e.b)}
  }
}
const marked = (c: C): C => c.op === 'flag' ? c : c.op === 'all' ? {op: 'all', key: c.key, c: marked(c.c)} : c.op === 'not' ? {op: 'not', x: marked(c.x)} : c.op === 'and' || c.op === 'or' ? {op: c.op, xs: c.xs.map(marked)} : {...c, a: markedE(c.a), b: markedE(c.b)}

type Spec = {
  name: string
  params: [string, Kind<unknown>][]
  inputs: [string, Kind<unknown>][]
  state: [string, number | ((p: never) => TermLike)][]
  maps: [string, number][]
  lists?: string[]
  // State variables declared by a kind: each a value over the kind's variables (in `state`, one entry each).
  kinded?: [string, Kind<unknown>][]
  carried?: string[]
  fns?: [string, FnDef][]
  facts?: ((env: never) => Record<string, Cond | Forall>)[]
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
  // Each variable starts at a natural or at a term over the params, or is declared by a kind and starts where `from`
  // says: `.state({balance: int.from(-5), status: oneOf('open', 'closed').from('open'), note: maybe(nat).from(null)})`.
  state<T extends Record<string, number | ((p: P) => TermLike) | Init<unknown>>>(init: T): Rule<P, I, S & {[k in keyof T]: T[k] extends Init<infer V> ? V : Term}, M, F, R, Su, Q> {
    const entries: [string, number | ((p: never) => TermLike)][] = [], kinded: [string, Kind<unknown>][] = []
    for (const [n, x] of Object.entries(init)) {
      if (typeof x === 'number' || typeof x === 'function') { entries.push([n, x as number | ((p: never) => TermLike)]); continue }
      const {kind, init: start} = x as Init<unknown>
      kinded.push([n, kind])
      if (typeof start === 'function') { const parts = (p: never) => kind.store(n, (start as (p: never) => unknown)(p)); for (const part of kind.vars(n)) entries.push([part, p => parts(p)[part]!]) }
      else { const enc = kind.encode(n, start); for (const part of kind.vars(n)) entries.push([part, enc[part]!]) }
    }
    return this.with({state: [...this.spec.state, ...entries], kinded: [...(this.spec.kinded ?? []), ...kinded]})
  }
  maps<T extends Record<string, number>>(init: T): Rule<P, I, S, M & {[k in keyof T]: MapRef}, F, R, Su, Q> { return this.with({maps: [...this.spec.maps, ...Object.entries(init)]}) }
  // Integers (Int), each starting at an integer or at one over the params; kept as two naturals, <name> and <name>$neg.
  ints<T extends Record<string, number | ((p: P) => IntLike)>>(init: T): Rule<P, I, S & {[k in keyof T]: Int}, M, F, R, Su, Q> {
    return this.state(Object.fromEntries(Object.entries(init).map(([n, x]) => [n, int.from(x as Raw)]))) as never
  }
  // Decimals with `places` places (Decimal), each starting at a number, a string ("12.50") or one over the params.
  decimals<T extends Record<string, number | string | ((p: P) => DecimalLike)>>(places: number, init: T): Rule<P, I, S & {[k in keyof T]: Decimal}, M, F, R, Su, Q> {
    const kind = decimal(places)
    return this.state(Object.fromEntries(Object.entries(init).map(([n, x]) => [n, kind.from(x as Raw)]))) as never
  }
  // Lists, each empty at the start: a map of positions and its length <name>_len (ListRef).
  lists<const N extends string>(...names: N[]): Rule<P, I, S & {[k in N as `${k}_len`]: Term}, M & {[k in N]: ListRef}, F, R, Su, Q> {
    return this.with({maps: [...this.spec.maps, ...names.map(n => [n, 0] as [string, number])], state: [...this.spec.state, ...names.map(n => [`${n}_len`, 0] as [string, number])], lists: [...(this.spec.lists ?? []), ...names]})
  }
  // Functions defined outside the rule (fn, divBy, modBy), read like params that take arguments: f(x).
  fns<T extends Record<string, FnDef>>(defs: T): Rule<P & {[k in keyof T]: (...args: TermLike[]) => Term}, I, S, M, F, R, Su, Q> {
    return this.with({fns: [...(this.spec.fns ?? []), ...Object.entries(defs)]})
  }
  // What is given about the functions (with their own facts): laws over the params and functions, each by name.
  facts(f: (p: P) => Record<string, Cond | Forall>): Rule<P, I, S, M, F, R, Su, Q> { return this.with({facts: [...(this.spec.facts ?? []), f as (env: never) => Record<string, Cond | Forall>]}) }
  // Maps each request carries whole (a set of names, say: cells 0 or 1), every cell past them 0; read like any map.
  carries<const N extends string>(...names: N[]): Rule<P, I & {[k in N]: MapRef}, S, M, F, R, Su, Q> { return this.with({carried: [...(this.spec.carried ?? []), ...names]}) }
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
  law(name: string, f: (env: P & S & M & Su) => Cond | Forall): Law { return withSource(this.lawOf(name, f(this.env({flags: false, inputs: false, queries: false}) as never)), {law: f as never}) }
  private lawOf(name: string, out: Cond | Forall): Law {
    const key = `key$${++keyCounter}`
    if (out instanceof Cond) { const p = prenex(out.c, `law ${name}`, key); return p ? {name, forall: key, holds: p} : {name, holds: out.c} }
    const [k1, more] = keysFor(out), holds = out.forall(v(k1), ...more.map(v)).c
    return more.length ? {name, forall: k1, keys: more, holds} : {name, forall: k1, holds: prenex(holds, `law ${name}`, k1) ?? holds}
  }

  // A law about one step, for every request the rule allows: `then(before, after)` relates what the step reads (params,
  // the request, state, maps, flags, sums, queries) to the state, maps and sums after it. `when` narrows the requests.
  //   counter.stepLaw('never goes back', ({used}, after) => used.atMost(after.used))
  stepLaw(name: string, then: (before: P & I & S & M & F & Su & Q, after: S & M & Su) => Cond | Forall, when?: (before: P & I & S & M & F & Su & Q) => Cond): StepLaw {
    const env = this.env() as never
    const after = this.afterEnv()
    const out = then(env, after as never), w = when ? {when: when(env).c} : {}
    const key = `key$${++keyCounter}`, src: Sources = {step: {then: then as never, ...(when ? {when: when as never} : {})}}
    if (out instanceof Cond) { const p = prenex(out.c, `step law ${name}`, key); return withSource(p ? {name, forall: key, then: p, ...w} : {name, then: out.c, ...w}, src) }
    const [k1, more] = keysFor(out), c = out.forall(v(k1), ...more.map(v)).c
    return withSource(more.length ? {name, forall: k1, keys: more, then: c, ...w} : {name, forall: k1, then: prenex(c, `step law ${name}`, k1) ?? c, ...w}, src)
  }

  // A law about k steps in a row (k from 2 to 16): `then(first, last, requests)` relates what the first step reads to the
  // state, maps and sums after the last, with each step's request and queries (requests[0] is the first's); `when(before,
  // j)` narrows the j-th step's request (j from 0), read at the state that step starts from.
  //   meter.stepsLaw('two requests spend at most 2m', 2, ({spent, m}, after) => after.spent.atMost(spent.plus(m).plus(m)))
  stepsLaw(name: string, k: number, then: (first: P & I & S & M & F & Su & Q, last: S & M & Su, requests: (I & Q)[]) => Cond | Forall, when?: (before: P & I & S & M & F & Su & Q, j: number) => Cond | undefined): StepLaw {
    const env = this.env() as never
    const after = this.afterEnv()
    // The j-th request's values over marked names, renamed to the kernel's input@j once built.
    const mark = (j: number) => `${j}:`
    const requests = Array.from({length: k}, (_, j) => {
      if (j === 0) return Object.fromEntries([...this.spec.inputs.map(([n]) => n), ...this.spec.queries.map(([n]) => n)].map(n => [n, (env as Record<string, unknown>)[n]]))
      return Object.fromEntries([...this.spec.inputs.map(([n, kind]) => [n, kind.value(n, mark(j + 1))]), ...this.spec.queries.map(([n]) => [n, v(`${mark(j + 1)}${n}`)])])
    })
    const out = then(env, after as never, requests as never)
    const whens = when ? Array.from({length: k}, (_, j) => when(env, j)) : []
    while (whens.length && whens.at(-1) === undefined) whens.pop()
    const w = whens.length ? {when: whens.map(c => (c ?? lit(0).atMost(0)).c)} : {}
    const key = `key$${++keyCounter}`
    if (out instanceof Cond) { const p = prenex(out.c, `step law ${name}`, key); return p ? {name, steps: k, forall: key, then: marked(p), ...w} : {name, steps: k, then: marked(out.c), ...w} }
    const [k1, more] = keysFor(out), c = out.forall(v(k1), ...more.map(v)).c
    return more.length ? {name, steps: k, forall: k1, keys: more, then: marked(c), ...w} : {name, steps: k, forall: k1, then: marked(prenex(c, `step law ${name}`, k1) ?? c), ...w}
  }

  // "Whenever `from` holds, `to` holds later", in every run that takes each helpful request infinitely often: proven by
  // a rank (a natural over the state and params, or several compared in order) that no step raises while `from` holds
  // and `to` doesn't, except by reaching `to`, and that each helpful request lowers (or it reaches `to`). A helpful
  // request names some inputs by terms over the state and params, the rest left free; with several, each comes with the
  // region where it helps (`when`), some region always holds, and a step that keeps the rank keeps its region.
  //   queue.leadsTo('every ticket is served', {from: ({t, next, served}) => t.lt(next).and(served.atMost(t)), to: ({t, served}) => served.gt(t),
  //     rank: ({t, served}) => t.plus(1).minus(served), helpful: () => ({op: 1})})
  //   batches.leadsTo('every batch is done', {from: () => yes, to: ({waiting, items}) => waiting.eq(0).and(items.eq(0)),
  //     rank: ({waiting, items}) => [waiting, items], helpful: [{when: ({items}) => items.gt(0), request: () => ({op: 1})}, {when: ({items}) => items.eq(0), request: () => ({op: 0})}]})
  leadsTo(name: string, spec: {from: (env: P & S & M & Su) => Cond, to: (env: P & S & M & Su) => Cond, rank: (env: P & S & M & Su) => TermLike | TermLike[],
    helpful: ((env: P & S & M & Su) => Record<string, TermLike>) | {when?: (env: P & S & M & Su) => Cond, request: (env: P & S & M & Su) => Record<string, TermLike>}[]}): Liveness {
    const env = this.env({flags: false, inputs: false, queries: false}) as never
    const req = (f: (env: never) => Record<string, TermLike>) => Object.fromEntries(Object.entries(f(env)).map(([n, t]) => [n, termOf(t)]))
    const r = spec.rank(env), rank = Array.isArray(r) ? r.map(termOf) : termOf(r)
    const base = {name, from: spec.from(env).c, to: spec.to(env).c, rank}
    return typeof spec.helpful === 'function' ? {...base, request: req(spec.helpful)} : {...base, helpful: spec.helpful.map(h => ({...(h.when ? {when: h.when(env).c} : {}), request: req(h.request)}))}
  }

  // A decision: whenever the params and the request meet `given`, `then` holds. Decisions don't read the state; the
  // functions' facts are assumed at the arguments the decision reads them at.
  decide(name: string, given: (env: P & I) => Cond | Cond[], then: (env: P & I) => Cond): Decision {
    const env = this.env({flags: false, state: false, queries: false}) as never
    const g = given(env), hyps = [...this.kindAssumptions(), ...this.spec.pre.map(f => f(env as never).c), ...this.spec.assume.map(f => f(env as never).c), ...(Array.isArray(g) ? g : [g]).map(c => c.c)]
    const t = then(env).c, goal: Goal = {name, hyps: [...hyps, {op: 'not', x: t}]}
    const facts = this.spec.fns?.length || this.spec.facts?.length ? factsFor(this.machine, goal) : []
    return withSource({name, rule: this as Rule<Obj>, given: hyps, then: t, goal: {name, hyps: [...facts, ...goal.hyps]}}, {decision: {given: given as never, then: then as never, own: Array.isArray(g) ? g.length : 1}})
  }
  // A decision about two requests under the same params (noninterference, say: requests that differ only in a secret
  // are decided alike). `given` and `then` read both; the second request's inputs are named b.<input> in a witness.
  //   r.relate('the secret is irrelevant', (a, b) => a.user.eq(b.user), (a, b) => a.allowed.iff(b.allowed))
  relate(name: string, given: (a: P & I, b: P & I) => Cond | Cond[], then: (a: P & I, b: P & I) => Cond): Decision {
    const s = this.spec, b = (n: string) => `b.${n}`, own = [...s.inputs.map(([n]) => n), ...(s.carried ?? [])]
    const second = (env: Record<string, unknown>) => ({...env, ...Object.fromEntries(own.map(n => [n, env[b(n)]]))}) as never
    const pair = new Rule({...s, inputs: [...s.inputs, ...s.inputs.map(([n, k]) => [b(n), k] as [string, Kind<unknown>])], carried: [...(s.carried ?? []), ...(s.carried ?? []).map(b)],
      assume: [...s.assume, ...s.assume.map(f => (env: never) => f(second(env)))], flags: [], step: undefined, record: undefined, sums: [], queries: [], keep: undefined, relations: undefined, prune: undefined})
    return pair.decide(name, env => given(env as never, second(env)), env => then(env as never, second(env)))
  }

  // --- what it compiles to ------------------------------------------------------------------------------------------
  private kindAssumptions(which: 'params' | 'inputs' | 'both' = 'both'): C[] {
    const ps = which === 'inputs' ? [] : this.spec.params.flatMap(([n, k]) => k.assume(n))
    const is = which === 'params' ? [] : this.spec.inputs.flatMap(([n, k]) => k.assume(n))
    return [...ps, ...is].map(c => c.c)
  }
  // The state after a step, as a step law reads it: every state variable, sum, map and list, primed.
  private afterEnv(): Record<string, unknown> {
    const after: Record<string, unknown> = {}
    for (const [n] of this.spec.state) after[n] = v(`${n}'`)
    for (const [n] of this.spec.sums) after[n] = v(`${n}'`)
    for (const [n, init] of this.spec.maps) after[n] = new MapRef(`${n}'`, init)
    for (const n of this.spec.lists ?? []) after[n] = new ListRef(`${n}'`, v(`${n}_len'`))
    for (const [n, k] of this.spec.kinded ?? []) { for (const part of k.vars(n)) delete after[part]; after[n] = k.value(n, primed) }
    return after
  }
  // The values handed to the builders' callbacks.
  private env(parts: {inputs?: boolean, state?: boolean, flags?: boolean, queries?: boolean} = {}): Record<string, unknown> {
    this.distinct()
    const out: Record<string, unknown> = {}
    for (const [n, k] of this.spec.params) out[n] = k.value(n)
    for (const [n, d] of this.spec.fns ?? []) out[n] = fnTerm(n, d)
    if (parts.inputs !== false) { for (const [n, k] of this.spec.inputs) out[n] = k.value(n); for (const n of this.spec.carried ?? []) out[n] = new MapRef(n, 0) }
    if (parts.state !== false) {
      for (const [n] of this.spec.state) out[n] = v(n)
      for (const [n, init] of this.spec.maps) out[n] = new MapRef(n, init)
      for (const n of this.spec.lists ?? []) out[n] = new ListRef(n, v(`${n}_len`))
      for (const [n] of this.spec.sums) out[n] = v(n)
      for (const [n, k] of this.spec.kinded ?? []) { for (const part of k.vars(n)) delete out[part]; out[n] = k.value(n) }
    }
    if (parts.queries !== false) for (const [n] of this.spec.queries) out[n] = v(n)
    if (parts.flags !== false) for (const f of this.spec.flags) for (const n of Object.keys(f(out as never))) {
      if (n in out && !(out[n] instanceof Cond && (out[n] as Cond).c.op === 'flag')) throw new Error(`${this.spec.name}: ${n} is a flag and ${this.whatIs(n)}`)
      out[n] = new Cond({op: 'flag', name: n}, scope?.flags[n])
    }
    return out
  }
  // Every name the rule declares is declared once (a flag named again replaces the earlier one, so flags are checked as
  // they are defined): an input and a state variable sharing a name would hand the callbacks only one of them.
  private names(): [string, string][] {
    const s = this.spec
    return [...s.params.map(([n]) => [n, 'a param']), ...(s.fns ?? []).map(([n]) => [n, 'a function']), ...s.inputs.map(([n]) => [n, 'an input']), ...(s.carried ?? []).map(n => [n, 'a carried map']),
      ...s.state.map(([n]) => [n, 'a state variable']), ...s.maps.map(([n]) => [n, 'a map']), ...s.sums.map(([n]) => [n, 'a sum']), ...s.queries.map(([n]) => [n, 'a query']),
    ] as [string, string][]
  }
  private whatIs(n: string): string { return this.names().find(([m]) => m === n)?.[1] ?? 'something else' }
  private distinct(): void {
    const seen = new Map<string, string>()
    for (const [n, what] of this.names()) {
      const had = seen.get(n)
      if (had) throw new Error(`${this.spec.name}: ${n} is ${had} and ${had === what ? 'declared again' : what}; give each a name of its own`)
      seen.set(n, what)
    }
  }
  get machine(): Machine {
    const s = this.spec
    const params = s.params.flatMap(([n, k]) => k.vars(n)), queries = s.queries.map(([n]) => n)
    const inputs = [...s.inputs.flatMap(([n, k]) => k.vars(n)), ...queries]
    const pEnv = this.env({inputs: false, state: false, flags: false, queries: false})
    const env: Record<string, unknown> = this.env({flags: false})
    const declared: Record<string, C> = {}
    for (const f of s.flags) for (const [n, c] of Object.entries(f(env as never))) {
      if (n in env && !(n in declared)) throw new Error(`${s.name}: ${n} is a flag and ${this.whatIs(n)}`)
      declared[n] = c.c; env[n] = new Cond({op: 'flag', name: n}) // a name again: replaced in place
    }
    // Quantifiers anywhere, named as flags: each placed before the flag that reads it.
    const hoist = new Hoister('all$'), flags: Record<string, C> = {}
    const placed = () => { for (const [n, c] of Object.entries(hoist.flags)) if (!(n in flags)) flags[n] = c }
    for (const [n, c] of Object.entries(declared)) {
      const out = c.op === 'all' ? hoist.quantifier(c, [], n) : hoist.cond(c)
      placed()
      if (!(n in flags)) flags[n] = out
    }
    const updates: Record<string, unknown> = {...s.step?.(env as never)}
    // A kinded variable's update, as its variables' terms.
    for (const [n, k] of s.kinded ?? []) {
      const u = updates[n]
      if (u === undefined) continue
      delete updates[n]
      Object.assign(updates, k.store(n, u))
    }
    const state: Record<string, E> = {}, maps: Record<string, MapUpdate> = {}
    for (const [n, u] of Object.entries(updates) as [string, TermLike | MapWrite | undefined][]) {
      if (u === undefined) continue
      if (typeof u === 'object' && 'map' in u) {
        if (u.map !== n) throw new Error(`${s.name}: the step writes map ${u.map} under the name ${n}`)
        maps[n] = 'each' in u ? {each: u.each, value: hoist.term(u.value, [u.each])} : {key: hoist.term(u.key), value: hoist.term(u.value)}
      } else state[n] = hoist.term(termOf(u))
    }
    const pre = [...this.kindAssumptions('params'), ...s.pre.map(f => f(pEnv as never).c)]
    const assume = [...this.kindAssumptions('inputs'), ...s.assume.map(f => hoist.cond(f(env as never).c))]
    placed()
    // Functions, and their facts: each function's own (named after it), then the rule's.
    const fns: Record<string, Fn> = Object.fromEntries((s.fns ?? []).map(([n, d]) => [n, {js: fnSource(n, d), ...(d.lean ? {lean: d.lean} : {})}]))
    const facts: Law[] = [
      ...(s.fns ?? []).flatMap(([n, d]) => Object.entries(d.facts?.(fnTerm(n, d)) ?? {}).map(([name, f]) => this.lawOf(`${n}: ${name}`, f))),
      ...(s.facts ?? []).flatMap(f => Object.entries(f(pEnv as never)).map(([name, out]) => this.lawOf(name, out))),
    ]
    const m: Machine = {
      name: s.name, params, inputs,
      state: Object.fromEntries(s.state.map(([n, init]) => [n, typeof init === 'number' ? termOf(init) : termOf(init(pEnv as never))])),
      ...(s.maps.length ? {maps: Object.fromEntries(s.maps)} : {}),
      ...(s.carried?.length ? {inputMaps: s.carried} : {}),
      step: {...(Object.keys(flags).length ? {flags} : {}), ...(Object.keys(state).length ? {state} : {}), ...(Object.keys(maps).length ? {maps} : {})},
      ...(pre.length ? {pre: pre.length === 1 ? pre[0]! : {op: 'and', xs: pre}} : {}),
      ...(assume.length ? {assume: assume.length === 1 ? assume[0]! : {op: 'and', xs: assume}} : {}),
      ...(Object.keys(fns).length ? {fns} : {}),
      ...(facts.length ? {facts} : {}),
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

  // --- the builders checked ------------------------------------------------------------------------------------------
  // The builders against what they built, on concrete runs: random params and requests by their kinds (`pre` and
  // `assume` met), and at every state each law's callback, each step law's, every flag and the step itself run again
  // with every value known, so each answer is the builders' own arithmetic (`val`, `ok`), against the expressions the
  // interpreter evaluates (core/watch.ts's verdicts, over the same keys). A law that says something other than its
  // callback, or a step that writes something other than it means, is reported with the state it shows at.
  crossCheck(laws: Law[], stepLaws: StepLaw[] = [], opts: {trials?: number, depth?: number, bound?: number, rand?: Rand} = {}): {checked: number, failure?: string} {
    const s = this.spec, m = this.machine, run = interpret(m), bound = opts.bound ?? 4, rand = opts.rand ?? seeded(7)
    let checked = 0
    const at = (what: string, params: object, st: State, input?: Request) => `${what}: params ${JSON.stringify(params)}, state ${JSON.stringify(this.decode(st))}${input ? `, request ${JSON.stringify(numbersOf(input))}` : ''}`
    const mapsOf = (st: State) => Object.fromEntries(Object.entries(st.maps).map(([n, cells]) => [n, {cells, dflt: st.defaults?.[n] ?? m.maps?.[n] ?? 0}]))
    for (let trial = 0; trial < (opts.trials ?? 100); trial++) {
      const params = this.randomParams(rand, bound)
      if (m.pre && !evalC(m.pre, params, {scalars: {}, maps: {}}, m)) continue
      let st = run.init(params)
      for (let d = 0, tries = 0; d <= (opts.depth ?? 8) && tries < 200; tries++) {
        // The laws at this state.
        const keys = keysOf(bound, st), lawScope: Scope = {vars: {...params, ...st.scalars}, maps: mapsOf(st), keys, flags: {}}
        for (const law of laws) {
          const f = sources.get(law)?.law
          if (!f) continue
          const ok = inScope(lawScope, () => this.verdict(f(this.env({flags: false, inputs: false, queries: false}) as never), keys))
          if (ok === undefined) continue
          checked++
          if (ok !== watch(m, run, law, params, bound).start(st)) return {checked, failure: at(`law "${law.name}": its callback says ${ok}, the law proven says ${!ok}`, params, st)}
        }
        if (d === (opts.depth ?? 8)) break
        const input = this.randomInput(rand, bound)
        if (s.prune || !allowed(m, run, params, st, input)) continue
        d++
        const next = run.step(params, st, input)
        if (!s.record) {
          const failure = this.crossStep(params, st, input, next, stepLaws, bound, () => checked++)
          if (failure) return {checked, failure: at(failure, params, st, input)}
        }
        st = next
      }
    }
    return {checked}
  }
  // A condition's value, or a law about every key's at every tuple of these keys (undefined when not every value is known).
  private verdict(out: Cond | Forall, keys: number[]): boolean | undefined {
    if (out instanceof Cond) return out.ok
    const go = (i: number, picked: Term[]): boolean | undefined => (i === out.forall.length ? out.forall(...(picked as [Term])).ok : everyOk(keys, k => go(i + 1, [...picked, keyTerm(k)])))
    return go(0, [])
  }
  // One step: the flags, the updates and the step laws, each against what the interpreter computed.
  private crossStep(params: Record<string, number>, st: State, input: Request, next: State, stepLaws: StepLaw[], bound: number, count: () => void): string | undefined {
    const s = this.spec, m = this.machine, run = interpret(m), seen = carriedView(m, st, input), req = requestEnv(m, run, params, st, input)
    const keys = keysOf(bound, seen, next), vars = {...params, ...st.scalars, ...req}
    const sc: Scope = {vars, maps: Object.fromEntries(Object.entries(seen.maps).map(([n, cells]) => [n, {cells, dflt: seen.defaults?.[n] ?? m.maps?.[n] ?? 0}])), keys: exactKeys(keys, vars, seen, next), flags: {}}
    // Flags: every callback in order, each name's last definition winning, until the values settle (a name defined
    // again replaces the first in place, so the flags between read the new one).
    const names = Object.keys(m.step.flags ?? {})
    for (let pass = 0; pass <= s.flags.length; pass++) {
      const values: Record<string, boolean> = {}
      inScope(sc, () => {
        const env = this.env({flags: false})
        for (const f of s.flags) for (const [n, c] of Object.entries(f(env as never))) { env[n] = new Cond({op: 'flag', name: n}, sc.flags[n]); if (c.ok !== undefined) values[n] = c.ok }
      })
      const settled = Object.keys(values).every(n => sc.flags[n] === values[n])
      sc.flags = values
      if (settled) break
    }
    for (const n of names) {
      if (sc.flags[n] === undefined || n.startsWith('all$')) continue
      count()
      if (sc.flags[n] !== (req[`?${n}`] === 1)) return `flag ${n}: its callback says ${sc.flags[n]}, the step decides ${req[`?${n}`] === 1}`
    }
    // The updates: every state variable as its value is written (a kinded one through its kind's `store`, as the
    // machine is built) or kept, and each map write.
    const updates = inScope(sc, () => s.step?.(this.env() as never) ?? {}) as Record<string, unknown>
    const written: Record<string, unknown> = {...updates}
    inScope(sc, () => { for (const [n, k] of s.kinded ?? []) if (updates[n] !== undefined) { delete written[n]; Object.assign(written, k.store(n, updates[n])) } })
    for (const n of Object.keys(st.scalars)) {
      const u = written[n], got = next.scalars[n]!, want = u === undefined ? st.scalars[n] : valOf(u as TermLike)
      if (want === undefined) continue
      count()
      if (want !== got) return `the step writes ${n} = ${want} by its callback, ${got} by the machine`
    }
    for (const [n] of s.maps) {
      const u = updates[n] as MapWrite | undefined, cell = (k: number) => next.maps[n]?.get(k) ?? next.defaults?.[n] ?? m.maps![n]!
      if (!u?.concrete) continue
      if ('at' in u.concrete) {
        const f = u.concrete.at
        for (const k of sc.keys!) { const want = inScope(sc, () => valOf(f(keyTerm(k)))); if (want === undefined) continue; count(); if (want !== cell(k)) return `the step writes ${n}[${k}] = ${want} by its callback, ${cell(k)} by the machine` }
      } else if (u.concrete.key !== undefined && u.concrete.value !== undefined) {
        count()
        if (u.concrete.value !== cell(u.concrete.key)) return `the step writes ${n}[${u.concrete.key}] = ${u.concrete.value} by its callback, ${cell(u.concrete.key)} by the machine`
      }
    }
    // Step laws (one step each): `when` and `then` on the state before and after.
    for (const sl of stepLaws) {
      const src = sources.get(sl)?.step
      if (!src || (sl.steps ?? 1) > 1) continue
      const after: Scope = {...sc, keys, vars: {...sc.vars, ...Object.fromEntries(Object.entries(next.scalars).map(([n, x]) => [`${n}'`, x]))},
        maps: {...sc.maps, ...Object.fromEntries(Object.entries(next.maps).map(([n, cells]) => [`${n}'`, {cells, dflt: next.defaults?.[n] ?? m.maps?.[n] ?? 0}]))}}
      const ok = inScope(after, () => {
        const env = this.env(), afterEnv = this.afterEnv()
        const w = src.when ? src.when(env as never).ok : true
        return w === undefined ? undefined : w ? this.verdict(src.then(env as never, afterEnv as never), keys) : true
      })
      if (ok === undefined) continue
      count()
      if (ok !== watch(m, run, sl, params, bound).step(st, input, next)) return `step law "${sl.name}": its callback says ${ok}, the law proven says ${!ok}`
    }
    return undefined
  }

  // Against the code it describes, step by step: `reference.init(params)` and `reference.step(params, state, request)`,
  // with requests drawn by their kinds (or `draw`), must hold the same values as the compiled rule (decoded: integers and
  // decimals as numbers) for every field the reference's state has, after every step of `trials` runs of `depth`.
  compare<St extends Record<string, number>>(reference: {init: (params: {[k in keyof P]: Raw}) => St, step: (params: {[k in keyof P]: Raw}, st: St, request: {[k in keyof I]: Raw}) => St},
    opts: Draws<{[k in keyof I]: Raw}> & {params?: (rand: Rand) => {[k in keyof P]: Raw}, depth?: number} = {}): Agreement {
    const s = this.spec, rand = opts.rand ?? seeded(5), bound = opts.bound ?? 100, gen = this.compiled()
    let checked = 0
    const sample = (kinds: [string, Kind<unknown>][]) => Object.fromEntries(kinds.map(([n, k]) => [n, k.sample(rand, bound)]))
    for (let trial = 0; trial < (opts.trials ?? 200); trial++) {
      const params = (opts.params?.(rand) ?? sample(s.params)) as {[k in keyof P]: Raw}, ps = this.encodeParams(params)
      let ours = gen.init(ps), theirs = reference.init(params)
      const edges = trial === 0 ? opts.edges ?? [] : []
      for (let d = 0; d < (opts.depth ?? 10) + edges.length; d++) {
        const request = edges[d] ?? opts.draw?.(rand) ?? sample(s.inputs) as {[k in keyof I]: Raw}
        ours = gen.step(ps, ours, this.encodeInput(request as never)); theirs = reference.step(params, theirs, request)
        const got = this.decode(ours)
        for (const [field, want] of Object.entries(theirs)) {
          checked++
          if (got[field] !== want) return {checked, failure: `${s.name}, params ${JSON.stringify(params)}, after ${JSON.stringify(request)}: ${field} is ${got[field]} here, ${want} in the code it describes`}
        }
      }
    }
    return {checked}
  }

  // --- running it -----------------------------------------------------------------------------------------------------
  // Runtime values (numbers, booleans, choice names, null for a missing value) to the variables the machine reads.
  encodeParams(values: {[k in keyof P]: Raw}): Record<string, number> { return encode(this.spec.params, values as Record<string, Raw>) }
  // A carried map is a Set of keys (each cell 1), an array of them, or a Map of key to natural.
  encodeInput(values: {[k in keyof I]: I[k] extends MapRef ? ReadonlySet<number> | readonly number[] | ReadonlyMap<number, number> : Raw}): Request {
    const out: Request = encode(this.spec.inputs, values as Record<string, Raw>)
    for (const n of this.spec.carried ?? []) {
      const given = (values as Record<string, unknown>)[n]
      out[n] = given instanceof Map ? new Map(given as Map<number, number>) : new Map([...(given as Iterable<number>)].map(key => [key, 1] as const))
    }
    return out
  }
  // Random params and inputs that meet their kinds (not the user's `pre` or `assume`, which a caller checks).
  randomParams(rand: Rand, bound: number): Record<string, number> { return Object.assign({}, ...this.spec.params.map(([n, k]) => k.random(n, rand, bound))) }
  randomInput(rand: Rand, bound: number): Request {
    const out: Request = Object.assign({}, ...this.spec.inputs.map(([n, k]) => k.random(n, rand, bound)))
    for (const n of this.spec.carried ?? []) out[n] = new Map(Array.from({length: bound + 1}, (_, key) => [key, rand(2)] as const).filter(([, cell]) => cell === 1))
    return out
  }
  // The state's scalars as runtime values: each kinded variable as its kind decodes it (an integer as one signed
  // number, a decimal as its number, a choice by name, a string as itself, none as null).
  decode(st: State): Record<string, Raw> {
    const out: Record<string, Raw> = {...st.scalars}
    for (const [n, k] of this.spec.kinded ?? []) { for (const part of k.vars(n)) delete out[part]; out[n] = k.decode(n, st.scalars) }
    return out
  }
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

// A function: arguments in, a result out, each field of the result a term or a condition over the arguments, the
// params and the functions it reads. Its laws are decisions about the same terms it computes, so what is proven is what
// runs (`run`, the compiled one-step rule whose state after the step is the result).
//   const reserve = fun('reserve').inputs({left: nat, used: nat}).returns(({left, used}) => ({granted: left.gt(0), left: left.minus(1), used: used.plus(1)}))
//   reserve.law('an empty budget grants nothing', ({left}) => left.eq(0), out => out.granted.not())
type Result<T> = {[k in keyof T]: T[k] extends Cond ? Cond : T[k] extends Decimal ? Decimal : T[k] extends Int ? Int : T[k] extends Choice<infer K> ? Choice<K> : T[k] extends Str ? Str : Term}
type Value<T> = {[k in keyof T]: T[k] extends Cond ? boolean : T[k] extends Choice<infer K> ? K : T[k] extends Str ? string : number}
type Field = Term | Cond | Int | Decimal | Choice<string> | Str
// The kind a result field is kept in.
const kindOf = (t: Field): Kind<unknown> => (t instanceof Cond ? bool : t instanceof Int ? int : t instanceof Decimal ? decimal(t.places) : t instanceof Choice ? oneOf(...t.values) : t instanceof Str ? str({like: t.patterns}) : nat)
export class Fun<P extends Obj = {}, I extends Obj = {}, O extends Obj = {}> {
  constructor(private readonly r: Rule<P, I>, private readonly out?: (env: never) => Record<string, TermLike | Field>) {}
  get name() { return this.r.name }
  params<K extends Kinds>(kinds: K): Fun<P & ValuesOf<K>, I, O> { return new Fun(this.r.params(kinds), this.out) as never }
  inputs<K extends Kinds>(kinds: K): Fun<P, I & ValuesOf<K>, O> { return new Fun(this.r.inputs(kinds), this.out) as never }
  fns<T extends Record<string, FnDef>>(defs: T): Fun<P & {[k in keyof T]: (...args: TermLike[]) => Term}, I, O> { return new Fun(this.r.fns(defs), this.out) as never }
  facts(f: (p: P) => Record<string, Cond | Forall>): Fun<P, I, O> { return new Fun(this.r.facts(f), this.out) }
  pre(f: (p: P) => Cond): Fun<P, I, O> { return new Fun(this.r.pre(f), this.out) }
  assume(f: (env: P & I) => Cond): Fun<P, I, O> { return new Fun(this.r.assume(f as never), this.out) }
  // The result (replaces an earlier one, so a variant is one call away).
  returns<T extends Record<string, TermLike | Field>>(f: (env: P & I) => T): Fun<P, I, Result<T>> { return new Fun(this.r, f as never) as never }

  private result(env: unknown): Record<string, Field> {
    if (!this.out) throw new Error(`${this.name}: no result (returns)`)
    return Object.fromEntries(Object.entries(this.out(env as never)).map(([k, t]) => [k, typeof t === 'number' ? lit(t) : t]))
  }
  // Whenever the arguments (and the result) meet `given`, the result meets `then`.
  law(name: string, given: (env: P & I, out: O) => Cond | Cond[], then: (out: O, env: P & I) => Cond): Decision {
    return lawOfFun(this, this.r.decide(name, env => given(env, this.result(env) as never), env => then(this.result(env) as never, env)))
  }
  // A law about two calls under the same params: `then(outA, outB, a, b)` given `given(a, b)` (noninterference, say).
  relate(name: string, given: (a: P & I, b: P & I) => Cond | Cond[], then: (outA: O, outB: O, a: P & I, b: P & I) => Cond): Decision {
    return lawOfFun(this, this.r.relate(name, given, (a, b) => then(this.result(a) as never, this.result(b) as never, a, b)))
  }

  // Against the code it describes: `reference` called with the same arguments (drawn by their kinds, or by `draw`, the
  // `edges` first) must return the same value for every field it returns (a field it leaves out is not compared). The
  // check for an encoding: that the terms here are what the real function computes, on its real inputs.
  //   cap.compare(({left, local}) => ({out: realCap(left, local)}), {edges: [{left: 2 ** 32 + 5, local: 10}]})
  compare(reference: (values: {[k in keyof I]: Raw}, params: {[k in keyof P]: Raw}) => Partial<Value<O>>, opts: Draws<{[k in keyof I]: Raw}> & {params?: {[k in keyof P]: Raw}} = {}): Agreement {
    const rand = opts.rand ?? seeded(5), bound = opts.bound ?? 1000, params = (opts.params ?? {}) as {[k in keyof P]: Raw}, kinds = this.r['spec'].inputs
    let checked = 0
    const draws = [...(opts.edges ?? []), ...Array.from({length: opts.trials ?? 2000}, () => opts.draw?.(rand) ?? Object.fromEntries(kinds.map(([n, k]) => [n, k.sample(rand, bound)])) as {[k in keyof I]: Raw})]
    for (const values of draws) {
      const ours = this.run(values, params) as Record<string, unknown>, theirs = reference(values, params) as Record<string, unknown>
      for (const [field, want] of Object.entries(theirs)) {
        checked++
        if (ours[field] !== want) return {checked, failure: `${this.name} at ${JSON.stringify(values)}: ${field} is ${String(ours[field])} here, ${String(want)} in the code it describes`}
      }
    }
    return {checked}
  }
  // The one-step rule it compiles to: the result's fields are its state (named out.<field>, apart from the arguments).
  get rule(): Rule<P, I> {
    const fields = Object.entries(this.result(this.r['env']({flags: false, state: false, queries: false})))
    const name = (k: string) => `out.${k}`
    return this.r.state(Object.fromEntries(fields.map(([k, t]) => { const kind = kindOf(t); return [name(k), kind.from(kind.empty())] })))
      .step(env => Object.fromEntries(Object.entries(this.result(env)).map(([k, t]) => [name(k), t])) as never) as never
  }
  private compiledRule?: {rule: Rule<P, I>, gen: ReturnType<Rule['compiled']>}
  // The result at these arguments (and params), from the compiled rule: numbers, and booleans for the conditions.
  run(values: {[k in keyof I]: Raw}, params: {[k in keyof P]?: Raw} = {}): Value<O> {
    this.compiledRule ??= (rule => ({rule, gen: rule.compiled()}))(this.rule)
    const {rule, gen} = this.compiledRule, ps = rule.encodeParams(params as never)
    const kinds = Object.entries(this.result(this.r['env']({flags: false, state: false, queries: false})))
    const st = rule.decode(gen.step(ps, gen.init(ps), rule.encodeInput(values as never)))
    return Object.fromEntries(kinds.map(([k]) => [k, st[`out.${k}`]])) as never
  }
}
export const fun = (name: string): Fun => new Fun(rule(name))
// The function a law was stated about. Variants of one function share its arguments, so a law's terms alone don't say
// which result it is about; a guard (gdp.ts) takes only laws stated about the function it runs.
const lawsOfFuns = new WeakMap<Decision, Fun<Obj, Obj, Obj>>()
const lawOfFun = (f: Fun<Obj, Obj, Obj>, d: Decision): Decision => { lawsOfFuns.set(d, f); return d }
export const funOf = (d: Decision): Fun<Obj, Obj, Obj> | undefined => lawsOfFuns.get(d)
// One disagreement between a rule and the code it describes, or none: what compare returns.
export type Agreement = {checked: number, failure?: string}
type Draws<T> = {trials?: number, bound?: number, rand?: Rand, edges?: T[], draw?: (rand: Rand) => T}

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

export type Verdict = {proven: boolean, checked: boolean, stuck?: string, goal?: string, witness?: Record<string, number>, why?: string, trees?: Record<string, Tree>}
const goalsVerdict = (goals: Goal[]): Verdict => {
  const trees: Record<string, Tree> = {}
  for (const g of goals) {
    const out = grow(g)
    if (!('tree' in out)) return {proven: false, checked: false, goal: g.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {}), ...(out.why ? {why: out.why} : {})}
    trees[g.name] = out.tree
  }
  return {proven: true, checked: goals.every(g => check(g, trees[g.name]!)), trees}
}
export function proveRule(r: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, laws: Law[]): Verdict {
  const out = proveLaws(r.machine, laws)
  return {proven: out.proven, checked: out.checked, ...(out.failed ? {goal: out.failed.goal, stuck: out.failed.stuck, ...(out.failed.witness ? {witness: out.failed.witness} : {}), ...(out.failed.why ? {why: out.failed.why} : {})} : {})}
}
export function proveSteps(r: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, laws: Law[], stepLaws: StepLaw[]): Verdict {
  const out = proveStepLaws(r.machine, laws, stepLaws)
  return {proven: out.proven, checked: out.checked, ...(out.failed ? {goal: out.failed.goal, stuck: out.failed.stuck, ...(out.failed.witness ? {witness: out.failed.witness} : {}), ...(out.failed.why ? {why: out.failed.why} : {})} : {})}
}
export type {StepLaw}
export type {Liveness}
export function proveLeadsTo(r: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, laws: Law[], l: Liveness): Verdict {
  const out = proveLiveness(r.machine, laws, l)
  return {proven: out.proven, checked: out.checked, ...(out.failed ? {goal: out.failed.goal, stuck: out.failed.stuck, ...(out.failed.witness ? {witness: out.failed.witness} : {}), ...(out.failed.why ? {why: out.failed.why} : {})} : {})}
}
export const proveDecision = (d: Decision): Verdict => goalsVerdict([d.goal])
const seeded = (seed: number): Rand => { let x = seed; return k => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) } }
// A decision's callbacks against its condition, on random params and requests: `given` and `then` each run with every
// value known, against what the interpreter evaluates of the decision built from them.
export function crossCheckDecision(d: Decision, opts: {trials?: number, bound?: number, rand?: Rand} = {}): {checked: number, failure?: string} {
  const src = sources.get(d)?.decision
  if (!src) return {checked: 0}
  const r = d.rule, m = r.machine, bound = opts.bound ?? 4, rand = opts.rand ?? seeded(11), own = d.given.slice(d.given.length - src.own)
  let checked = 0
  for (let i = 0; i < (opts.trials ?? 500); i++) {
    const input = r.randomInput(rand, bound), values = {...r.randomParams(rand, bound), ...numbersOf(input)}
    const st: State = {scalars: {}, maps: Object.fromEntries(Object.entries(input).filter((e): e is [string, ReadonlyMap<number, number>] => typeof e[1] !== 'number').map(([n, cells]) => [n, new Map(cells)]))}
    const keys = exactKeys(keysOf(bound, st), values, st)
    const sc: Scope = {vars: values, maps: Object.fromEntries(Object.entries(st.maps).map(([n, cells]) => [n, {cells, dflt: 0}])), keys, flags: {}}
    const [g, t] = inScope(sc, () => { const env = r['env']({flags: false, state: false, queries: false}) as never, g = src.given(env); return [all(...(Array.isArray(g) ? g : [g])).ok, src.then(env).ok] })
    for (const [what, ok, c] of [['given', g, own], ['then', t, [d.then]]] as const) {
      if (ok === undefined) continue
      checked++
      const want = c.every(x => evalC(x, values, st, m))
      if (ok !== want) return {checked, failure: `decision "${d.name}": its ${what} callback says ${ok}, the decision proven says ${want}, at ${JSON.stringify(values)}`}
    }
  }
  return {checked}
}
export const proveLoop = (l: LoopRule<Obj, Obj, Obj>, laws: Law[]): Verdict => goalsVerdict(loopObligations(l.loop, laws, l.rankTerms))
