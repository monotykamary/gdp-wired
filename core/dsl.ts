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
import {type C, type E, type Fn, type Law, type Recurrence, type Machine, type MapUpdate, type Request, type State, carriedView, compileFunction, divName, divisor, divisorsIn, evalC, evalE, interpret, isArithmetic, loadJs, modName, numbersOf, pairedArgs, withArithmetic} from './machine.ts'
import {allowed, keysOf, requestEnv, watch} from './watch.ts'
import {someHolds, substVars} from './exists.ts'
import {type Fold, type Goal, type Liveness, type Loop, type StepLaw, type Tree, check, foldObligations, loopObligations} from '../kernel/kernel.ts'
import {certLoop, factsFor, grow, proveLaws, proveLiveness, proveStepLaws, usualProof, withDeadline} from '../kernel/prove.ts'
import {type Translated, type UsualProof, certCyclic, certOn, crossCyclic, cyclicOn, foldNodes, proveCyclic, quietly, recurNodes, translatedProof, uncovered} from './cyclic.ts'
import {discover} from './discover.ts'
import {inferLaws} from './infer.ts'
import {cycleLemmas, findLeadsTo, findRank} from './cycles.ts'

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
  // x div k and x mod k, rounded down, for a constant k >= 1: the rule's functions div$k and mod$k at x, which the
  // kernel knows by x = k·(x div k) + x mod k and x mod k < k (machine.ts's arithmetic). Division by a term that isn't a
  // constant has no such fact in linear arithmetic (x = y·q + r is a product of two unknowns), so it isn't offered.
  modBy(k: number): Term { divisor(k, 'modBy'); return new Term({op: 'get', map: modName(k), key: this.e}, this.val === undefined ? undefined : this.val % k) }
  divBy(k: number): Term { divisor(k, 'divBy'); return new Term({op: 'get', map: divName(k), key: this.e}, this.val === undefined ? undefined : Math.floor(this.val / k)) }
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
  // `ex`: the existentials (exists) inside, each with whether it reads as "there exists" where it sits (under no not, or
  // an even number of them): a law, the assumption or a precondition pulls each such one out as ∃ before the whole.
  constructor(readonly c: C, readonly ok?: boolean, readonly ex?: readonly Bound[]) {}
  and(...xs: Cond[]): Cond { return all(this, ...xs) }
  or(...xs: Cond[]): Cond { return any(this, ...xs) }
  not(): Cond { return new Cond({op: 'not', x: this.c}, this.ok === undefined ? undefined : !this.ok, this.ex?.map(b => ({...b, pos: !b.pos}))) }
  implies(b: Cond): Cond { return any(this.not(), b) }
  iff(b: Cond): Cond { return all(this.implies(b), b.implies(this)) }
}

export const lit = (v: number): Term => new Term(termOf(v), v)
export const yes = new Cond({op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}, true)
export const no = new Cond({op: '<', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}, false)
const exOf = (cs: Cond[]): readonly Bound[] | undefined => (cs.some(c => c.ex?.length) ? cs.flatMap(c => c.ex ?? []) : undefined)
export const all = (...cs: Cond[]): Cond => (cs.length === 0 ? yes : cs.length === 1 ? cs[0]! : new Cond({op: 'and', xs: cs.map(c => c.c)}, known(cs.map(c => c.ok))?.every(x => x), exOf(cs)))
export const any = (...cs: Cond[]): Cond => (cs.length === 0 ? no : cs.length === 1 ? cs[0]! : new Cond({op: 'or', xs: cs.map(c => c.c)}, known(cs.map(c => c.ok))?.some(x => x), exOf(cs)))
export const not = (c: Cond): Cond => c.not()
export const min = (a: TermLike, b: TermLike): Term => new Term({op: 'min', a: termOf(a), b: termOf(b)}, both(valOf(a), valOf(b), Math.min))
export const max = (a: TermLike, b: TermLike): Term => new Term({op: 'max', a: termOf(a), b: termOf(b)}, both(valOf(a), valOf(b), Math.max))
// By cases. For a value made of several (an integer, a decimal, a choice, a string, an optional value, a condition)
// each part goes by the same case.
export function when(c: Cond, then: TermLike, otherwise: TermLike): Term
export function when(c: Cond, then: Decimal, otherwise: Decimal | number): Decimal
export function when(c: Cond, then: Decimal | number, otherwise: Decimal): Decimal
export function when(c: Cond, then: IntLike, otherwise: IntLike): Int
export function when<K extends string>(c: Cond, then: Choice<K> | NoInfer<K>, otherwise: Choice<K>): Choice<K>
export function when<K extends string>(c: Cond, then: Choice<K>, otherwise: Choice<K> | NoInfer<K>): Choice<K>
export function when(c: Cond, then: Str, otherwise: Str): Str
export function when<V>(c: Cond, then: Maybe<V>, otherwise: Maybe<V>): Maybe<V>
export function when(c: Cond, then: Cond, otherwise: Cond): Cond
export function when<C extends Cases, T extends string>(c: Cond, then: Variant<C, T>, otherwise: Variant<C, T>): Variant<C, T>
export function when<T extends Record<string, unknown>>(c: Cond, then: T, otherwise: T): T
export function when(c: Cond, then: unknown, otherwise: unknown): unknown {
  if (then instanceof Cond && otherwise instanceof Cond) return choose(c, then, otherwise)
  if (then instanceof Variant && otherwise instanceof Variant) {
    if (then.kind.names.join() !== otherwise.kind.names.join()) throw new Error('when: variants of other cases')
    return new Variant(when(c, then.tag, otherwise.tag), Object.fromEntries(then.kind.names.map(k => [k, when(c, then.cases[k] as never, otherwise.cases[k] as never)])) as never, then.kind)
  }
  if (isRecord(then) && isRecord(otherwise)) {
    if (Object.keys(then).sort().join() !== Object.keys(otherwise).sort().join()) throw new Error('when: records of other fields')
    return Object.fromEntries(Object.keys(then).map(f => [f, when(c, then[f] as never, otherwise[f] as never)]))
  }
  // A choice's name beside a choice is that choice's value: when(closing, 'closed', status).
  if (then instanceof Choice && typeof otherwise === 'string') return when(c, then, then.of(otherwise))
  if (typeof then === 'string' && otherwise instanceof Choice) return when(c, otherwise.of(then), otherwise)
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
// A record's value: a plain object of its fields' values (not a term, a condition or another value of a kind).
const isRecord = (x: unknown): x is Record<string, unknown> => typeof x === 'object' && x !== null && Object.getPrototypeOf(x) === Object.prototype
// The same value, part by part: numbers equal, conditions both or neither, choices and strings alike, an optional value
// missing in both or present in both and the same, a variant in the same case with the same fields, a record field by
// field.
export function same(a: unknown, b: unknown): Cond {
  if (a instanceof Cond && b instanceof Cond) return a.iff(b)
  if (a instanceof Choice && b instanceof Choice) return a.n.eq(b.n)
  if (a instanceof Str && b instanceof Str) return a.eq(b)
  if (a instanceof Decimal) return a.eq(b as DecimalLike)
  if (b instanceof Decimal) return b.eq(a as DecimalLike)
  if (a instanceof Int) return a.eq(b as IntLike)
  if (b instanceof Int) return b.eq(a as IntLike)
  if (a instanceof Maybe && b instanceof Maybe) return all(a.present.eq(b.present), a.isNone.or(same(a.inner, b.inner)))
  if (a instanceof Variant && b instanceof Variant) {
    if (a.kind.names.join() !== b.kind.names.join()) throw new Error('same: variants of other cases')
    return all(a.tag.eq(b.tag), ...a.kind.names.filter(k => Object.keys(a.cases[k]!).length).map(k => a.is(k).implies(same(a.cases[k], b.cases[k]))))
  }
  if (isRecord(a) && isRecord(b)) {
    if (Object.keys(a).sort().join() !== Object.keys(b).sort().join()) throw new Error('same: records of other fields')
    return all(...Object.keys(a).map(f => same(a[f], b[f])))
  }
  if ((a instanceof Term || typeof a === 'number') && (b instanceof Term || typeof b === 'number')) return (typeof a === 'number' ? lit(a) : a).eq(b)
  throw new Error('same: two values of one kind')
}
// 1 where c holds, else 0: what a sum over a history adds per record.
export const count = (c: Cond): Term => when(c, 1, 0)
export const sum = (first: TermLike, ...rest: TermLike[]): Term => rest.reduce<Term>((acc, t) => acc.plus(t), typeof first === 'number' ? lit(first) : first)

// --- kinds: what a param or input may be ------------------------------------------------------------------------------

type Rand = (k: number) => number
// A runtime value: a number, a boolean, a string, null for a missing value, or an object (a record, a variant's case).
export type Raw = number | boolean | string | null | undefined | RawObject | readonly Raw[]
export type RawObject = {readonly [field: string]: Raw}

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
  // The value over its variables' terms, each part's from `get` (the variable named so, or a term written for it).
  abstract build(name: string, get: (part: string) => Term): V
  value(name: string, at: At = ''): V { return this.build(name, part => v(named(at, part))) }
  // What every value a step writes keeps true of its variables (a flag is 0 or 1, a choice or a case in range, a
  // presence bit 0 or 1), unlike a bound such as upTo's, which a step may pass: the laws a rule's state and cells of the
  // kind are proven to keep (Rule.kindLaws).
  invariant(_value: V): Cond[] { return [] }
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
  // x mod k and x div k for a constant k >= 1, as SMT-LIB and Lean's Int read them for k > 0: x = k·(x div k) + x mod k
  // with 0 <= x mod k < k (so -7 div 2 is -4 and -7 mod 2 is 1). Over the naturals: pos + (k − 1)·neg is x + k·neg,
  // the same remainder, and its quotient is x div k + neg, so both are the natural division of that one natural.
  modBy(k: number): Term { divisor(k, 'modBy'); return add(this.pos, this.neg.times(k - 1)).modBy(k) }
  divBy(k: number): Int { divisor(k, 'divBy'); return new Int(add(this.pos, this.neg.times(k - 1)).divBy(k), this.neg) }
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
  if (typeof raw !== 'number' || !Number.isSafeInteger(raw) || raw < 0) throw new RangeError(`${name} must be a natural, not ${shown(raw)}`)
  return raw
}

class NatKind extends Kind<Term> {
  constructor(readonly maxValue?: number) { super() }
  vars(name: string) { return [name] }
  assume(name: string) { return this.maxValue === undefined ? [] : [v(name).atMost(this.maxValue)] }
  build(name: string, get: (part: string) => Term) { return get(name) }
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
  build(name: string, get: (part: string) => Term) { return new Bool(get(name)) }
  override invariant(b: Bool) { return [b.n.atMost(1)] }
  store(name: string, value: unknown) { return {[name]: typeof value === 'boolean' ? (value ? 1 : 0) : count(value as Cond)} }
  decode(name: string, vars: Record<string, number>) { return vars[name] === 1 }
  empty() { return false }
  encode(name: string, raw: Raw) {
    if (typeof raw === 'boolean') return {[name]: raw ? 1 : 0}
    if (raw === 0 || raw === 1) return {[name]: raw}
    throw new RangeError(`${name} must be a boolean, not ${shown(raw)}`)
  }
  random(name: string, rand: Rand) { return {[name]: rand(2)} }
  sample(rand: Rand) { return rand(2) === 1 }
}
export const bool: Kind<Bool> = new BoolKind()

// One of a few named values, encoded as its index. `match` takes every case (TypeScript checks none is missing).
export class Choice<K extends string> {
  constructor(readonly n: Term, readonly values: readonly K[]) {}
  is(k: K): Cond { return this.n.eq(this.indexOf(k)) }
  // The value named k, of this choice's kind (to write: when(c, status.of('closed'), status)).
  of(k: K): Choice<K> { return new Choice(lit(this.indexOf(k)), this.values) }
  // Its index among the values, in the order declared (oneOf('new', 'paid'): new is 0), as a term.
  get index(): Term { return this.n }
  // The same value as a name, another choice of the kind, or an index (a number or a natural term): status.eq('paid'),
  // a.phase.eq(b.phase), phase.eq(3), phase.eq(when(c, 2, phase.index)).
  eq(o: K | Choice<K> | number | Term): Cond { return typeof o === 'string' ? this.is(o) : o instanceof Choice ? this.n.eq(o.n) : this.n.eq(o) }
  ne(o: K | Choice<K> | number | Term): Cond { return this.eq(o).not() }
  private indexOf(k: K): number {
    const i = this.values.indexOf(k)
    if (i < 0) throw new Error(`${k} is not one of ${this.values.join(', ')}`)
    return i
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
  build(name: string, get: (part: string) => Term) { return new Choice(get(name), this.values) }
  override invariant(c: Choice<K>) { return [c.n.lt(this.values.length)] }
  store(name: string, value: unknown) { return {[name]: value instanceof Choice ? value.n : this.encode(name, value as Raw)[name]!} }
  decode(name: string, vars: Record<string, number>) { return this.values[vars[name]!]! }
  empty() { return this.values[0]! }
  encode(name: string, raw: Raw) {
    const i = this.values.indexOf(raw as K)
    if (i < 0) throw new RangeError(`${name} is one of ${this.values.join(', ')}, not ${shown(raw)}`)
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
  build(name: string, get: (part: string) => Term) { return new Maybe(get(this.has(name)), this.of.build(name, get)) }
  override invariant(m: Maybe<V>) { return [m.present.atMost(1), ...this.of.invariant(m.inner)] }
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
// A value present where c holds and missing elsewhere (a function's result that may be missing, say).
export const optional = <V>(c: Cond, value: V): Maybe<V> => new Maybe(count(c), value)

// A record: named fields, each of its own kind, its variables each field's (<name>.<field>). Its value is a plain object
// of the fields' values, so a callback destructures it (`({pay}) => pay.amount.atMost(limit)`), and `when` and `same`
// go field by field. A runtime value is an object with exactly these fields.
type Fields = Record<string, Kind<unknown>>
const fieldName = (name: string, f: string) => `${name}.${f}`
const plainFields = (what: string, names: string[]) => { for (const f of names) if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(f)) throw new Error(`${what}: ${f} is not a plain field name`) }
const rawObject = (name: string, raw: Raw, what: string): RawObject => {
  if (raw === null || typeof raw !== 'object' || Array.isArray(raw)) throw new RangeError(`${name} must be ${what}, not ${String(raw)}`)
  return raw as RawObject
}
// Runtime values alike: objects field by field.
const sameRaw = (a: unknown, b: unknown): boolean => {
  if (a === b) return true
  if (typeof a !== 'object' || typeof b !== 'object' || a === null || b === null) return false
  const ka = Object.keys(a), kb = Object.keys(b)
  return ka.length === kb.length && ka.every(k => sameRaw((a as Record<string, unknown>)[k], (b as Record<string, unknown>)[k]))
}
const shown = (x: unknown): string => (typeof x === 'object' && x !== null ? JSON.stringify(x) : String(x))
// r.<field> is a history record's field to the runtimes.
const composite = (name: string) => { if (name === 'r') throw new Error('r names a history record; give the record or variant another name') }
const merged = (parts: Record<string, number>[]): Record<string, number> => Object.assign({}, ...parts)
class RecordKind<K extends Fields> extends Kind<ValuesOf<K>> {
  readonly names: string[]
  constructor(readonly fields: K) {
    super()
    this.names = Object.keys(fields)
    if (this.names.length === 0) throw new Error('a record has a field')
    plainFields('record', this.names)
  }
  private each<T>(f: (field: string, kind: Kind<unknown>) => T): T[] { return this.names.map(n => f(n, this.fields[n]!)) }
  vars(name: string) { composite(name); return this.each((f, k) => k.vars(fieldName(name, f))).flat() }
  assume(name: string) { return this.each((f, k) => k.assume(fieldName(name, f))).flat() }
  build(name: string, get: (part: string) => Term) { return Object.fromEntries(this.each((f, k) => [f, k.build(fieldName(name, f), get)])) as ValuesOf<K> }
  override invariant(r: ValuesOf<K>) { return this.each((f, k) => k.invariant((r as Record<string, unknown>)[f])).flat() }
  store(name: string, value: unknown) {
    const o = value as Record<string, unknown>
    if (o === null || typeof o !== 'object') throw new Error(`${name}: a record is written as an object of its fields`)
    for (const f of Object.keys(o)) if (!(f in this.fields)) throw new Error(`${name}: the record has no field ${f}`)
    return Object.assign({}, ...this.each((f, k) => { if (!(f in o)) throw new Error(`${name}: the write leaves out the field ${f}`); return k.store(fieldName(name, f), o[f]) })) as Record<string, TermLike>
  }
  decode(name: string, vars: Record<string, number>) { return Object.fromEntries(this.each((f, k) => [f, k.decode(fieldName(name, f), vars)])) }
  empty() { return Object.fromEntries(this.each((f, k) => [f, k.empty()])) }
  encode(name: string, raw: Raw) {
    const o = rawObject(name, raw, `an object with the fields ${this.names.join(', ')}`)
    for (const f of Object.keys(o)) if (!(f in this.fields)) throw new RangeError(`${name} has no field ${f}`)
    return merged(this.each((f, k) => k.encode(fieldName(name, f), o[f])))
  }
  random(name: string, rand: Rand, bound: number) { return merged(this.each((f, k) => k.random(fieldName(name, f), rand, bound))) }
  sample(rand: Rand, bound: number) { return Object.fromEntries(this.each((f, k) => [f, k.sample(rand, bound)])) }
}
export const record = <const K extends Fields>(fields: K): Kind<ValuesOf<K>> => new RecordKind(fields)

// A tagged union: one of a few cases, each with fields of its own (a payment by card with its last four digits, or in
// cash), encoded as the case's index and every case's fields (<name>.<case>.<field>). A case's fields can only be read in
// `match`, so no law or step reads the fields of a case the value isn't in; there they are left unconstrained, so nothing
// proven depends on them. A runtime value is an object whose `tag` names the case, beside that case's fields:
// {tag: 'card', last4: 4242}.
type Cases = Record<string, Fields>
type CaseValues<C extends Cases> = {[k in keyof C]: ValuesOf<C[k]>}
type MatchCases<C extends Cases, T> = {[k in keyof C]: (fields: ValuesOf<C[k]>) => T}
export class Variant<C extends Cases = Cases, T extends string = 'tag'> {
  constructor(readonly tag: Term, readonly cases: CaseValues<C>, readonly kind: VariantKind<C, T>) {}
  is(k: keyof C & string): Cond { return this.tag.eq(this.kind.index(k)) }
  // One function per case, each given its fields: every case returns a condition, or every case a value of one kind.
  match(cases: MatchCases<C, Cond>): Cond
  match(cases: MatchCases<C, TermLike>): Term
  match<T>(cases: MatchCases<C, T>): T
  match(cases: MatchCases<C, unknown>): unknown {
    const results = this.kind.names.map(k => [k, cases[k]!(this.cases[k]!)] as const)
    if (results.every(([, r]) => r instanceof Cond)) return any(...results.map(([k, r]) => all(this.is(k), r as Cond)))
    // The last case is what's left: the kind's assumption says the index is below the number of cases.
    return results.slice(0, -1).reduceRight<unknown>((acc, [k, r]) => when(this.is(k), r as never, acc as never), results.at(-1)![1])
  }
}
export type VariantWrite<C extends Cases, T extends string = 'tag'> = {[k in keyof C]: {[f in T | keyof C[k]]: f extends T ? k : C[k][f] extends Kind<infer V> ? Writes<V> : never}}[keyof C]
export class VariantKind<C extends Cases, T extends string = 'tag'> extends Kind<Variant<C, T>> {
  readonly names: (keyof C & string)[]
  constructor(readonly cases: C, readonly tagKey: T) {
    super()
    this.names = Object.keys(cases)
    if (this.names.length === 0) throw new Error('a variant has a case')
    plainFields('variant', this.names)
    for (const k of this.names) { plainFields(`variant case ${k}`, Object.keys(cases[k]!)); if (tagKey in cases[k]!) throw new Error(`variant case ${k}: ${tagKey} names the case, not a field`) }
  }
  index(k: string): number {
    const i = this.names.indexOf(k)
    if (i < 0) throw new Error(`${k} is not a case of ${this.names.join(', ')}`)
    return i
  }
  private payload(k: string) { return new RecordKind(this.cases[k]!) }
  private filled(k: string) { return Object.keys(this.cases[k]!).length > 0 }
  private at(name: string, k: string) { return fieldName(name, k) }
  vars(name: string) { composite(name); return [name, ...this.names.filter(k => this.filled(k)).flatMap(k => this.payload(k).vars(this.at(name, k)))] }
  assume(name: string) { return [v(name).lt(this.names.length), ...this.names.filter(k => this.filled(k)).flatMap(k => this.payload(k).assume(this.at(name, k)))] }
  build(name: string, get: (part: string) => Term) {
    return new Variant(get(name), Object.fromEntries(this.names.map(k => [k, this.filled(k) ? this.payload(k).build(this.at(name, k), get) : {}])) as CaseValues<C>, this)
  }
  // The value of a case with these fields (terms, values or runtime values), to compare, match or pass to `when`:
  //   when(held, At.make({tag: 'holding', amount, since: now}), at)
  override invariant(x: Variant<C, T>) { return [x.tag.lt(this.names.length), ...this.names.filter(k => this.filled(k)).flatMap(k => this.payload(k).invariant(x.cases[k] as never))] }
  make(write: VariantWrite<C, T>): Variant<C, T> {
    const parts = this.store('$', write)
    return this.build('$', part => { const t = parts[part]!; return typeof t === 'number' ? lit(t) : t })
  }
  // A Variant of this kind as it is, or {tag: case, ...fields} (fields as values or runtime values): the other cases'
  // fields are written empty.
  store(name: string, value: unknown) {
    if (value instanceof Variant) {
      if (value.kind.names.join() !== this.names.join()) throw new Error(`${name}: a variant of other cases is written`)
      return {[name]: value.tag, ...Object.assign({}, ...this.names.filter(k => this.filled(k)).map(k => this.payload(k).store(this.at(name, k), value.cases[k])))} as Record<string, TermLike>
    }
    const o = value as Record<string, unknown>, k = o?.[this.tagKey]
    if (typeof k !== 'string') throw new Error(`${name}: a variant is written as {${this.tagKey}: case, ...fields}`)
    const {[this.tagKey]: _, ...fields} = o
    return {[name]: this.index(k), ...Object.assign({}, ...this.names.filter(c => this.filled(c)).map(c => this.payload(c).store(this.at(name, c), c === k ? fields : this.payload(c).empty())))} as Record<string, TermLike>
  }
  decode(name: string, vars: Record<string, number>) {
    const k = this.names[vars[name]!]!
    return {[this.tagKey]: k, ...(this.filled(k) ? this.payload(k).decode(this.at(name, k), vars) : {})}
  }
  empty() { const k = this.names[0]!; return {[this.tagKey]: k, ...(this.filled(k) ? this.payload(k).empty() : {})} }
  encode(name: string, raw: Raw) {
    const o = rawObject(name, raw, `an object whose ${this.tagKey} is one of ${this.names.join(', ')}`), k = o[this.tagKey]
    if (typeof k !== 'string' || !this.names.includes(k)) throw new RangeError(`${name}.${this.tagKey} is one of ${this.names.join(', ')}, not ${shown(k)}`)
    const {[this.tagKey]: _, ...fields} = o
    if (!this.filled(k) && Object.keys(fields).length) throw new RangeError(`${name}: the case ${k} has no fields`)
    const zeros = (c: string) => Object.fromEntries(this.payload(c).vars(this.at(name, c)).map(n => [n, 0]))
    return {[name]: this.index(k), ...merged(this.names.filter(c => this.filled(c)).map(c => (c === k ? this.payload(c).encode(this.at(name, c), fields) : zeros(c))))}
  }
  random(name: string, rand: Rand, bound: number) {
    const i = rand(this.names.length)
    return {[name]: i, ...merged(this.names.filter(c => this.filled(c)).map(c => this.payload(c).random(this.at(name, c), rand, bound)))}
  }
  sample(rand: Rand, bound: number) { const k = this.names[rand(this.names.length)]!; return {[this.tagKey]: k, ...(this.filled(k) ? this.payload(k).sample(rand, bound) as RawObject : {})} }
}
// The key that names the case in a runtime value is `tag`, or the one given: variant({...}, {tag: 'kind'}).
export function variant<const C extends Cases>(cases: C): VariantKind<C>
export function variant<const C extends Cases, const T extends string>(cases: C, opts: {tag: T}): VariantKind<C, T>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export function variant(cases: Cases, opts: {tag?: string} = {}): VariantKind<any, any> {
  if (opts.tag !== undefined && !/^[A-Za-z_][A-Za-z0-9_]*$/.test(opts.tag)) throw new Error(`variant: ${opts.tag} is not a plain key`)
  return new VariantKind(cases, opts.tag ?? 'tag')
}

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
  build(name: string, get: (part: string) => Term) { return new Str(get(name), get(`${name}$len`), new Map(this.patterns.map((p, i) => [p, get(this.bit(name, i))]))) }
  store(name: string, value: unknown) {
    if (typeof value === 'string') return {[name]: literal(value), [`${name}$len`]: value.length, ...Object.fromEntries(this.patterns.map((p, i) => [this.bit(name, i), globMatch(p, value) ? 1 : 0]))}
    const t = value as Str
    return {[name]: t.id, [`${name}$len`]: t.length, ...Object.fromEntries(this.patterns.map((p, i) => [this.bit(name, i), t.bit(p)]))}
  }
  decode(name: string, vars: Record<string, number>) { const id = vars[name]!; for (const [text, n] of internTable) if (n === id) return text; throw new Error(`${name}: no string is interned as ${id}`) }
  empty() { return '' }
  encode(name: string, raw: Raw) {
    if (typeof raw !== 'string') throw new RangeError(`${name} must be a string, not ${shown(raw)}`)
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
  build(name: string, get: (part: string) => Term) { return new Int(get(name), get(`${name}$neg`)) }
  store(name: string, value: unknown) { const i = normal(Int.of(value as IntLike)); return {[name]: i.pos, [`${name}$neg`]: i.neg} }
  decode(name: string, vars: Record<string, number>) { return vars[name]! - vars[`${name}$neg`]! }
  empty() { return 0 }
  encode(name: string, raw: Raw) {
    if (typeof raw !== 'number' || !Number.isSafeInteger(raw)) throw new RangeError(`${name} must be an integer, not ${shown(raw)}`)
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
  build(name: string, get: (part: string) => Term) { return new Decimal(new Int(get(name), get(`${name}$neg`)), this.places) }
  store(name: string, value: unknown) {
    const i = normal(typeof value === 'string' ? Int.of(scaledOf(value, this.places)) : new Decimal(Int.of(0), this.places).lift(value as DecimalLike))
    return {[name]: i.pos, [`${name}$neg`]: i.neg}
  }
  decode(name: string, vars: Record<string, number>) { return (vars[name]! - vars[`${name}$neg`]!) / 10 ** this.places }
  empty() { return 0 }
  encode(name: string, raw: Raw) {
    if (typeof raw !== 'number' && typeof raw !== 'string') throw new RangeError(`${name} must be a decimal, not ${shown(raw)}`)
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
// only as a map's key. The kernel closes it (instances where it holds, a witness where it fails). With two parameters
// or more, at every two keys or more (`everyKey((i, j) => i.lt(j).implies(At.at(i).atMost(At.at(j))))`): each key read
// on its own, and compared with another only plainly (i < j, i <= j, i = j); the runtimes decide it on every tuple of
// a few keys per breakpoint, so it costs the square of the cells (the cube, over three keys).
export const everyKey = (f: (key: Term, key2: Term, key3: Term) => Cond): Cond => {
  const names = Array.from({length: Math.max(1, f.length)}, () => `k$${++boundCounter}`), g = f as (...ks: Term[]) => Cond
  const ok = (picked: Term[]): boolean | undefined => (picked.length === names.length ? g(...picked).ok : everyOk(scope?.keys, k => ok([...picked, keyTerm(k)])))
  return new Cond({op: 'all', key: names[0]!, ...(names.length > 1 ? {keys: names.slice(1)} : {}), c: g(...names.map(v)).c}, ok([]))
}
// Some key where f holds, in a law or a step law's conclusion (¬∀k. ¬f(k)): proven through a witness, a term naming the
// key, given here or found by the prover among a few candidates (kernel/prove.ts).
export const someKey = (f: (key: Term) => Cond, witness?: TermLike): Cond => {
  const key = `s$${++boundCounter}`
  const none = everyOk(scope?.keys, k => f(keyTerm(k)).not().ok)
  return new Cond({op: 'not', x: {op: 'all', key, c: f(v(key)).not().c, ...(witness === undefined ? {} : {witness: termOf(witness)})}}, none === undefined ? undefined : !none)
}
// There exists a value of `kind` (nat by default; int, bool, upTo(k)...) where f holds (core/exists.ts): in a law,
// "∃ x. f(x)" wherever it reads so (under no not), proven through a witness the prover finds (a term of the state, or
// a ghost: a value carried along the run, from the start and through each step) or the one given: a value of the kind
// over the state (a term witness), or {start, step}, a ghost (start over the params, step over the witness before and
// the step's own values: the request, the state before, the flags). In the assumption (over the request and the
// params) or a precondition (over the params), a value the request or the params bring along: the runtimes find it
// (encodeInput, encodeParams) where it is one natural or integer f reads linearly.
export type ExistsWitness<V> = V | number | {start: V | number, step: (before: V, env: never) => V | number}
// An existential a condition carries: its naturals, its body over them, whether it reads as "there exists", the
// witness given.
type Bound = {vars: string[], body: C, pos: boolean, terms?: Record<string, E>, start?: Record<string, E>, step?: (env: Record<string, unknown>) => Record<string, E>}
export function exists(f: (x: Term) => Cond, witness?: ExistsWitness<Term>): Cond
export function exists<V>(kind: Kind<V>, f: (x: V) => Cond, witness?: ExistsWitness<V>): Cond
export function exists(a: unknown, b?: unknown, c?: unknown): Cond {
  const [kind, f, w] = (a instanceof Kind ? [a, b, c] : [nat, a, b]) as [Kind<unknown>, (x: unknown) => Cond, unknown]
  const name = `some$${++boundCounter}`, value = kind.value(name), body = all(...kind.assume(name), f(value))
  const store = (x: unknown): Record<string, E> => Object.fromEntries(Object.entries(kind.store(name, x)).map(([n, t]) => [n, termOf(t)]))
  const ghost = typeof w === 'object' && w !== null && 'step' in w && 'start' in w && typeof (w as {step: unknown}).step === 'function'
  const given = w === undefined ? {} : ghost
    ? {start: store((w as {start: unknown}).start), step: (env: Record<string, unknown>) => store((w as {step: (b: unknown, e: never) => unknown}).step(value, env as never))}
    : {terms: store(w)}
  return new Cond(body.c, undefined, [...(body.ex ?? []), {vars: kind.vars(name), body: body.c, pos: true, ...given}])
}
// A condition's existentials pulled out before it (each reading as "there exists"), their naturals renamed `${prefix}0`,
// `${prefix}1`, ... (an integer's second part keeping $neg), so a machine built again names them alike.
function pulledOut(cs: Cond[], what: string, prefix?: string): {cs: C[], vars: string[], bodies: {vars: string[], body: C}[]} {
  const bs = cs.flatMap(c => c.ex ?? [])
  if (bs.some(b => !b.pos)) throw new Error(`${what}: exists(...) under a not (or on the left of implies) says "for every value"; state it as a law about every value of a param instead`)
  const ren: Record<string, E> = {}
  if (prefix !== undefined) bs.forEach((b, i) => b.vars.forEach(n => { ren[n] = {op: 'var', name: n.endsWith('$neg') ? `${prefix}${i}$neg` : `${prefix}${i}`} }))
  const r = (c: C) => (prefix === undefined ? c : substVars(c, ren))
  const vars = bs.flatMap(b => b.vars.map(n => (prefix === undefined ? n : (ren[n] as {name: string}).name)))
  const out = cs.map(c => r(c.c)), stray = out.flatMap(c => namesIn(c)).filter(n => n.startsWith('some$') && !vars.includes(n) && !/^some\$[ap]\d/.test(n))
  if (stray.length) throw new Error(`${what}: ${stray[0]} is bound by an exists(...) whose condition was taken apart; keep it whole (and, or, not, implies)`)
  return {cs: out, vars, bodies: bs.map(b => ({vars: b.vars.map(n => (prefix === undefined ? n : (ren[n] as {name: string}).name)), body: r(b.body)}))}
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
// A sequence of naturals as positions and a length (a path's segments, as interned names): `at(i)` its value at i,
// `len` its length. Comparing two is a condition about every position below a length (the array property fragment,
// decidable), so a law about prefixes needs no induction. One a request carries (`carriesSeq`), or a row of a table of
// them (`carriesSeqs`), its positions read from its row's offset in the table's one map.
export class SeqRef {
  constructor(private readonly map: MapRef, readonly len: Term, private readonly base?: Term) {}
  at(i: TermLike): Term { return this.map.at(!this.base ? i : typeof i === 'number' ? this.base.plus(i) : i.plus(this.base)) }
  // The same values at every position below `upTo` (both have them).
  private agree(o: SeqRef, upTo: Term): Cond { return everyKey(k => k.lt(upTo).implies(this.at(k).eq(o.at(k)))) }
  // This one is where o starts; o is where this one starts; the same; o followed by `by` more; x at some position.
  prefixOf(o: SeqRef): Cond { return this.len.atMost(o.len).and(this.agree(o, this.len)) }
  startsWith(o: SeqRef): Cond { return o.prefixOf(this) }
  equals(o: SeqRef): Cond { return this.len.eq(o.len).and(this.agree(o, this.len)) }
  extends(o: SeqRef, by: TermLike): Cond { return o.prefixOf(this).and(this.len.eq(o.len.plus(by))) }
  has(x: TermLike): Cond { return everyKey(k => k.lt(this.len).implies(this.at(k).ne(x))).not() }
}
// A table of sequences a request carries (each grant's path, say): `row(r)` is row r's sequence, `rows` how many. Rows
// are read by their number as a map's key, so a condition about every row reads a row only there (`everyBelow(T.rows,
// r => ...)`).
export class SeqTable {
  constructor(readonly name: string, readonly rows: Term) {}
  row(r: TermLike): SeqRef { return new SeqRef(new MapRef(this.name, 0), new MapRef(`${this.name}_len`, 0).at(r), new MapRef(`${this.name}_base`, 0).at(r)) }
}
// f at every key below n: what bookkeeping a request carries meets, row by row (where each grant went, say).
export const everyBelow = (n: TermLike, f: (key: Term) => Cond): Cond => everyKey(k => k.lt(n).implies(f(k)))
const when_ = (c: Cond, then: TermLike, otherwise: TermLike): Term => new Term({op: 'if', c: c.c, then: termOf(then), else: termOf(otherwise)}, c.ok === undefined ? undefined : valOf(c.ok ? then : otherwise))

// Writes to the maps a map or a list of a kind is kept in (one per variable of the kind), as the step returns them under
// the map's own name.
export type PartsWrite = {readonly parts: Record<string, MapWrite>}
const isPartsWrite = (u: unknown): u is PartsWrite => typeof u === 'object' && u !== null && 'parts' in u
// The parts of a value written at a cell, by the names of the maps they go to.
const partsOf = (kind: Kind<unknown>, name: string, value: unknown): Record<string, TermLike> => kind.store(name, value)

// A map whose cells hold values of a kind (a record, a variant, a choice...): one map per variable of the kind
// (<name>.<field>, and the case's index as <name> for a variant), every cell starting at the kind's value given by
// `from`. `at(k)` is the value at k, read as the kind's value is; `set` and `each` write whole values.
//   .maps({Acct: record({limit: nat, blocked: bool}).from({limit: 0, blocked: false})})
//   .step(({who, Acct}) => ({Acct: Acct.set(who, {limit: 10, blocked: false})}))
export class CellsRef<V> {
  constructor(readonly name: string, readonly kind: Kind<V>, private readonly map: (part: string) => MapRef) {}
  at(key: TermLike): V { return this.kind.build(this.name, part => this.map(part).at(key)) }
  set(key: TermLike, value: Writes<V>): PartsWrite {
    const parts = partsOf(this.kind, this.name, value)
    return {parts: Object.fromEntries(this.kind.vars(this.name).map(part => [part, this.map(part).set(key, parts[part]!)]))}
  }
  // Every key at once (the key read only as a map's key).
  each(f: (key: Term) => Writes<V>): PartsWrite {
    return {parts: Object.fromEntries(this.kind.vars(this.name).map(part => [part, this.map(part).each(k => partsOf(this.kind, this.name, f(k))[part]!)]))}
  }
}

// A list whose items are values of a kind: one list per variable of the kind, all of one length <name>_len, each cell
// past the end 0 (the kind's empty value, for every kind). The same operations as a list of names, each taking a whole
// value; `apply` takes several, the first whose condition holds.
export type ItemsOp = {readonly when: Cond, readonly parts: Record<string, ListOp>, readonly len: TermLike}
// A list of values of a kind a request carries (an invoice's lines, a batch of transfers): its items one carried map per
// variable of the kind (<name>.<field>), every cell past the length 0, its length the input <name>_len, and each fold a
// carried map of the fold's running values (<name>$<fold>: the start at 0, and at i + 1 the step from the value at i and
// the i-th item). The encoding computes the folds from the items, and every request is assumed to meet their equations
// (a request that doesn't is not allowed), so `fold.<name>`, the value at the length, is what the fold computes.
// A lemma about the folds is a law of their running values at every prefix (and its length i): proven by induction when
// the rule is built (the folds run as a machine over items that are any functions), then assumed of every request at
// every prefix, which the runtimes check as they check the equations.
// A fold's start and step may read the rule's params (`p`, those declared before the list), as its lemmas may.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type ListFold<V, P = any> = {from: number | ((p: P) => TermLike), step: (acc: Term, item: V, p: P) => TermLike}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type ListLemma<P = any> = (acc: Record<string, Term>, i: Term, p: P) => Cond
const fromOf = <V>(d: ListFold<V>, p: Record<string, unknown>): TermLike => (typeof d.from === 'number' ? d.from : d.from(p))
// The keys a condition reads any of these maps at, as terms.
function keysRead(cs: C[], maps: string[]): Term[] {
  const out: Term[] = []
  const e = (t: E): void => {
    if (t.op === 'get') { if (maps.includes(t.map)) out.push(new Term(t.key)); e(t.key) }
    else if (t.op === 'if') { c(t.c); e(t.then); e(t.else) }
    else if (t.op === 'mul') e(t.a)
    else if (t.op === 'add' || t.op === 'sub' || t.op === 'min' || t.op === 'max' || t.op === 'prod') { e(t.a); e(t.b) }
  }
  const c = (x: C): void => {
    if (x.op === 'not') c(x.x)
    else if (x.op === 'and' || x.op === 'or') x.xs.forEach(c)
    else if (x.op === 'all') c(x.c)
    else if (x.op !== 'flag') { e(x.a); e(x.b) }
  }
  cs.forEach(c)
  return out
}
const uniqueTerms = (ts: Term[]): Term[] => [...new Map(ts.map(t => [JSON.stringify(t.e), t])).values()]
export class CarriedList<V, Fd extends string = never> {
  readonly fold: Record<Fd, Term>
  // `params`: the params' values the folds read (by their kinds: terms for the kernel, constants to encode a request),
  // undefined where none are given; `paramKinds`, the params themselves, for the lemmas' induction.
  constructor(readonly name: string, readonly kind: Kind<V>, readonly len: Term, readonly folds: Record<Fd, ListFold<V>>, private readonly map: (part: string) => MapRef,
    readonly lemmas: Record<string, ListLemma> = {}, private readonly params?: Record<string, unknown>, private readonly paramKinds: [string, Kind<unknown>][] = []) {
    this.fold = Object.fromEntries(Object.keys(folds).map(f => [f, map(`${name}$${f}`).at(len)])) as Record<Fd, Term>
  }
  at(i: TermLike): V { return this.kind.build(this.name, part => this.map(part).at(i)) }
  // The running value of a fold after the first i items.
  after(fold: Fd, i: TermLike): Term { return this.map(`${this.name}$${fold}`).at(i) }
  every(f: (item: V, i: Term) => Cond): Cond { return everyKey(k => k.lt(this.len).implies(f(this.at(k), k))) }
  some(f: (item: V, i: Term) => Cond): Cond { return this.every((x, i) => f(x, i).not()).not() }
  has(x: V): Cond { return this.some(y => same(y, x)) }
  // Each item's `by` below the next one's (so no two alike).
  increasing(by: (item: V) => Term): Cond { return everyKey(k => k.plus(1).lt(this.len).implies(by(this.at(k)).lt(by(this.at(k.plus(1)))))) }
  // What every request is assumed to meet: each fold's start, and at every key one condition (the item's own laws and
  // each fold's step below the length, each lemma up to it), so the prover closes one quantifier, not one per part.
  equations(): Cond[] { return [...this.starts(), ...(this.keyed ? [everyKey(k => this.atKey(k))] : [])] }
  // The same at the keys given, without the quantifier: what a decision assumes of the list (Rule.decide).
  equationsAt(keys: Term[]): Cond[] { return [...this.starts(), ...(this.keyed ? keys.map(k => this.atKey(k)) : [])] }
  private starts(): Cond[] { return (Object.entries(this.folds) as [string, ListFold<V>][]).map(([f, d]) => this.map(`${this.name}$${f}`).at(0).eq(fromOf(d, this.p()))) }
  private get keyed(): boolean { return this.kind.invariant(this.kind.value(this.name)).length + Object.keys(this.folds).length + Object.keys(this.lemmas).length > 0 }
  private atKey(k: Term): Cond {
    const folds = Object.entries(this.folds) as [string, ListFold<V>][], lemmas = Object.values(this.lemmas)
    const x = this.at(k), steps = folds.map(([f, d]) => this.map(`${this.name}$${f}`).at(k.plus(1)).eq(d.step(this.map(`${this.name}$${f}`).at(k), x, this.p())))
    const below = [...this.kind.invariant(x), ...steps]
    return all(...(below.length ? [k.lt(this.len).implies(all(...below))] : []), ...(lemmas.length ? [k.atMost(this.len).implies(all(...lemmas.map(l => l(this.running(k), k, this.p()))))] : []))
  }
  // Whether a fold reads the params (its start a function, or its step taking them).
  private get readsParams(): boolean { return (Object.values(this.folds) as ListFold<V>[]).some(d => typeof d.from === 'function' || d.step.length > 2) }
  private p(): Record<string, unknown> {
    if (this.params) return this.params
    if (this.readsParams) throw new RangeError(`${this.name}'s folds read the params: give them (encodeInput(values, params))`)
    return {}
  }
  private running(k: Term): Record<string, Term> { return Object.fromEntries(Object.keys(this.folds).map(f => [f, this.after(f as Fd, k)])) }
  // The lemmas, proven: the folds as a machine counting i up from 0 over items that are functions of i known only by
  // the kind's own laws, each lemma a law of it (so it holds after every prefix of every list).
  prove(): Verdict {
    if (!Object.keys(this.lemmas).length) return {proven: true, checked: true}
    const parts = this.kind.vars(this.name), fname = (p: string) => `item$${p.replaceAll('.', '$')}`
    const item = (i: Term) => this.kind.build(this.name, p => new Term({op: 'get', map: fname(p), key: i.e}))
    // Every item is a value of the kind (its own laws, as a fact of the first part's function).
    const kindFact: Record<string, Cond | Forall> = this.kind.invariant(this.kind.value(this.name)).length ? {'every item is a value of its kind': forall(k => all(...this.kind.invariant(item(k))))} : {}
    const fns = Object.fromEntries(parts.map((p, j) => [fname(p), fn(1, 'x => 0', j === 0 ? {facts: () => kindFact} : {})]))
    const folds = Object.entries(this.folds) as [string, ListFold<V>][]
    const r: LooseRule = (rule(`${this.name}'s folds, by induction`) as LooseRule).params(Object.fromEntries(this.paramKinds)).fns(fns).inputs({})
      .state({i: 0, ...Object.fromEntries(folds.map(([f, d]) => [`acc$${f}`, typeof d.from === 'number' ? d.from : (p: never) => (d.from as (p: never) => TermLike)(p)]))})
      .step((env: Record<string, Term>) => ({i: env.i!.plus(1), ...Object.fromEntries(folds.map(([f, d]) => [`acc$${f}`, d.step(env[`acc$${f}`]!, item(env.i!), env)]))}))
    const accs = (env: Record<string, Term>) => Object.fromEntries(folds.map(([f]) => [f, env[`acc$${f}`]!]))
    return proveRule(r as never, Object.entries(this.lemmas).map(([n, l]) => r.law(n, (env: Record<string, Term>) => l(accs(env), env.i!, env))), {search: false})
  }
  // Every carried map it is kept in: the items' parts, then each fold's.
  get maps(): string[] { return [...this.kind.vars(this.name), ...Object.keys(this.folds).map(f => `${this.name}$${f}`)] }
  // A request's list as those maps and its length: each fold computed by its step, as the builders compute it.
  encode(raw: Raw): {maps: Record<string, Map<number, number>>, len: number} {
    if (!Array.isArray(raw)) throw new RangeError(`${this.name} must be a list, not ${shown(raw)}`)
    const items = (raw as readonly Raw[]).map(x => this.kind.encode(this.name, x))
    const maps: Record<string, Map<number, number>> = Object.fromEntries(this.maps.map(m => [m, new Map<number, number>()]))
    items.forEach((enc, i) => { for (const [part, x] of Object.entries(enc)) if (x !== 0) maps[part]!.set(i, x) })
    for (const [f, d] of Object.entries(this.folds) as [string, ListFold<V>][]) {
      const acc = maps[`${this.name}$${f}`]!, p = this.p()
      let value = valOf(fromOf(d, p))!
      if (value !== 0) acc.set(0, value)
      items.forEach((enc, i) => {
        const item = this.kind.build(this.name, part => new Term({op: 'const', value: enc[part]!}, enc[part]!))
        const next = valOf(d.step(new Term({op: 'const', value}, value), item, p))
        if (next === undefined || !Number.isSafeInteger(next) || next < 0) throw new RangeError(`${this.name}'s fold ${f} reads more than its items`)
        value = next
        if (value !== 0) acc.set(i + 1, value)
      })
    }
    return {maps, len: items.length}
  }
}

export class ItemsRef<V> {
  constructor(readonly name: string, readonly kind: Kind<V>, readonly len: Term, private readonly list: (part: string) => ListRef) {}
  private get names() { return this.kind.vars(this.name) }
  at(i: TermLike): V { return this.kind.build(this.name, part => this.list(part).at(i)) }
  // x at some position.
  has(x: V): Cond { return everyKey(k => k.lt(this.len).implies(same(this.at(k), x).not())).not() }
  private op(when: Cond, len: TermLike, f: (l: ListRef, part: string) => ListOp): ItemsOp { return {when, len, parts: Object.fromEntries(this.names.map(part => [part, f(this.list(part), part)]))} }
  push(x: Writes<V>, when: Cond = yes): ItemsOp { const p = partsOf(this.kind, this.name, x); return this.op(when, this.len.plus(1), (l, part) => l.push(p[part]!, when)) }
  pop(when: Cond = yes): ItemsOp { return this.op(when, this.len.minus(1), l => l.pop(when)) }
  set(i: TermLike, x: Writes<V>, when: Cond = yes): ItemsOp { const p = partsOf(this.kind, this.name, x); return this.op(when, this.len, (l, part) => l.set(i, p[part]!, when)) }
  insertAt(i: TermLike, x: Writes<V>, when: Cond = yes): ItemsOp { const p = partsOf(this.kind, this.name, x); return this.op(when, this.len.plus(1), (l, part) => l.insertAt(i, p[part]!, when)) }
  removeAt(i: TermLike, when: Cond = yes): ItemsOp { return this.op(when, this.len.minus(1), l => l.removeAt(i, when)) }
  apply(...ops: ItemsOp[]): Record<string, TermLike | PartsWrite> {
    const parts: Record<string, MapWrite> = {}
    for (const part of this.names) parts[part] = this.list(part).apply(...ops.map(op => op.parts[part]!))[part] as MapWrite
    return {[this.name]: {parts}, [`${this.name}_len`]: ops.reduceRight<Term>((acc, op) => when_(op.when, op.len, acc), this.len)}
  }
  // Laws: nothing past the end; the items in strictly increasing order of `by`.
  within(): Forall { return forall(k => this.len.atMost(k).implies(all(...this.names.map(part => this.list(part).at(k).eq(0))))) }
  increasing(by: (x: V) => Term): Forall { return forall((i, j) => i.lt(j).and(j.lt(this.len)).implies(by(this.at(i)).lt(by(this.at(j))))) }
}

// A tree (or a forest, or a list of lists) in a rule's state, as a table of nodes that only grows: node 0 the empty
// tree, nodes 1 .. <name>_size each a value of a kind and its children (named; each an earlier node, or 0), made one a
// step from nodes already there, never changed after. Each fold is a value of every node from its own value and its
// children's (a child 0 has the fold's `empty`), kept with the node when it is made, so a law about a whole subtree is a
// law about its root's folds: one node at a time, no induction over the tree. Maps: <name>.<part> for the values,
// <name>^<child> for the children, <name>$<fold> for the folds; laws that every node's children are earlier, its folds
// are its children's, and nothing is past the end are the table's own (Rule.kindLaws), proven beside the rule's.
//   .nodes('Tree', record({key: nat}), ['left', 'right'], {lo: {empty: 0, node: (x, kids) => when(kids.left.empty, x.key, kids.left.fold.lo)}})
export type NodeRef<V, C extends string, Fd extends string> = {readonly index: Term, readonly empty: Cond, readonly value: V, readonly fold: Record<Fd, Term>, readonly kids: Record<C, Term>}
// A fold's node may read the tables declared before its own (`tables`, by name): a row's total over the cells its value
// names, say. Their nodes never change, so a fold read from them stays theirs; a node made before the one it reads is
// refused by the table's laws, which the kernel proves only if the step makes it after.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type NodeFold<V, C extends string, Fd extends string = string, T = Record<string, NodeTable<any, any, any>>> = {empty: number, node: (value: V, kids: Record<C, NodeRef<V, C, Fd>>, tables: T) => TermLike}
// The tables among a rule's maps.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type TablesOf<M> = {[k in keyof M as M[k] extends NodeTable<any, any, any> ? k : never]: M[k]}
export class NodeTable<V, C extends string = string, Fd extends string = string> {
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  constructor(readonly name: string, readonly kind: Kind<V>, readonly children: C[], readonly folds: Record<Fd, NodeFold<V, C, Fd>>, readonly size: Term, private readonly map: (part: string) => MapRef, private readonly tables: Record<string, NodeTable<any, any, any>> = {}) {}
  // The node at n (0, or past the end: the empty tree).
  node(n: TermLike): NodeRef<V, C, Fd> {
    const index = termAt(n)
    return {index, empty: index.eq(0), value: this.kind.build(this.name, part => this.map(part).at(index)),
      fold: Object.fromEntries(Object.keys(this.folds).map(f => [f, this.map(`${this.name}$${f}`).at(index)])) as Record<Fd, Term>,
      kids: Object.fromEntries(this.children.map(c => [c, this.map(`${this.name}^${c}`).at(index)])) as Record<C, Term>}
  }
  at(n: TermLike): V { return this.node(n).value }
  // Whether nodes can be made from these children (each 0 or a node already there).
  fits(kids: Record<C, TermLike>): Cond { return all(...this.children.map(c => termAt(kids[c]).atMost(this.size))) }
  // Node size + 1, from a value and children already there, when `when` holds (and they fit): its value, children and
  // folds written, the size grown.
  make(value: Writes<V>, kids: Record<C, TermLike>, when: Cond = yes): Record<string, TermLike | PartsWrite> {
    const n = this.size.plus(1), go = when.and(this.fits(kids)), parts = partsOf(this.kind, this.name, value)
    const val = this.kind.build(this.name, part => termAt(parts[part]!))
    const kidRefs = Object.fromEntries(this.children.map(c => [c, this.node(termAt(kids[c]))])) as Record<C, NodeRef<V, C, Fd>>
    const writes: Record<string, MapWrite> = {}
    const put = (part: string, x: TermLike) => { writes[part] = this.map(part).set(n, when_(go, x, this.map(part).at(n))) }
    for (const part of this.kind.vars(this.name)) put(part, parts[part]!)
    for (const c of this.children) put(`${this.name}^${c}`, kids[c])
    for (const [f, d] of Object.entries(this.folds) as [string, NodeFold<V, C, Fd>][]) put(`${this.name}$${f}`, d.node(val, kidRefs, this.tables))
    return {[this.name]: {parts: writes}, [`${this.name}_size`]: when_(go, n, this.size)}
  }
  // The table's own laws: every node's children are earlier nodes and its folds are its children's, and node 0 and every
  // key past the end hold nothing (each fold's empty).
  laws(): [string, Forall][] {
    const inside = (k: Term) => k.atLeast(1).and(k.atMost(this.size))
    const folds = Object.entries(this.folds) as [string, NodeFold<V, C, Fd>][]
    return [
      ...(this.children.length ? [[`every ${this.name} node's children are earlier nodes`, forall(k => inside(k).implies(all(...this.children.map(c => this.node(k).kids[c].lt(k)))))] as [string, Forall]] : []),
      ...(folds.length ? [[`every ${this.name} node's folds are its children's`, forall(k => inside(k).implies(all(...folds.map(([f, d]) => {
        const x = this.node(k)
        return x.fold[f as Fd].eq(d.node(x.value, Object.fromEntries(this.children.map(c => [c, this.node(x.kids[c])])) as Record<C, NodeRef<V, C, Fd>>, this.tables))
      }))))] as [string, Forall]] : []),
      [`nothing in ${this.name} past its end`, forall(k => k.eq(0).or(this.size.lt(k)).implies(all(...this.kind.vars(this.name).map(part => this.map(part).at(k).eq(0)),
        ...this.children.map(c => this.node(k).kids[c].eq(0)), ...folds.map(([f, d]) => this.node(k).fold[f as Fd].eq(d.empty)))))],
    ]
  }
}
const termAt = (t: TermLike): Term => (t instanceof Term ? t : lit(t))

export type Forall = {readonly forall: (key: Term, ...more: Term[]) => Cond}
// A law about every key of a map: proven at a fresh key, assumed at the keys a step reads.
// With two parameters or more, about every two keys or more: forall((i, j) => i.lt(j).implies(...)).
export function forall(f: (key: Term, key2: Term, key3: Term, key4: Term, key5: Term, key6: Term) => Cond): Forall { return {forall: f as Forall['forall']} }
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
    case 'all': return {...c, c: swapC(c.c, from, to)}
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
    if (outer.length) throw new Error(`a condition at every key reads ${outer[0]}, a key bound outside it: two keys at once are named together (everyKey((i, j) => ...))`)
    const inner = perStep(q.c), keys = q.keys?.length ? {keys: q.keys} : {}
    if (!inner) { const f = name ?? `${this.prefix}${++this.n}`; this.flags[f] = {op: 'all', key: q.key, ...keys, c: q.c}; return {op: 'flag', name: f} }
    const truth = inner.op === 'flag' ? inner : this.quantifier(inner, [...bound, q.key, ...(q.keys ?? [])])
    const split = (by: C) => this.quantifier({op: 'all', key: q.key, ...keys, c: swapC(q.c, inner, by)}, bound)
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
        if (d.keys?.length) throw new Error(`${what}: a condition at every two keys in a law is the law's own keys (forall((i, j) => ...))`)
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
// key ((a + b)² + b, in the kernel's arithmetic: one product, and no case to split, since s = a + b is the floor of its
// square root and b at most s).
// `uses`: the functions it reads (a recurrence's), each a function of the rule too, named <name>.<use>; its facts read
// them through `uses` (the second argument of `facts`).
export type FnDef = {arity: number, js: string | ((...args: number[]) => number), lean?: string, facts?: (f: (...args: TermLike[]) => Term, uses?: Record<string, (...args: TermLike[]) => Term>) => Record<string, Cond | Forall>, recur?: Recurrence, uses?: Record<string, FnDef>}
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

// A function defined by a recurrence on its first argument, and lemmas about it proven by induction: f(0, a..) = zero
// and f(x + 1, a..) = next(x, f(x, a..), a..), the further arguments `args` fixed along the recursion, each term the
// kernel's own (+, ∸, × by a constant, products, min, max, if) or a read of a function in `fns` (in `next`). Its facts are
// the two equations and the lemmas, all proven here when the function is made (a lemma that isn't proven throws
// Unproven, with the verdict: its witness an induction step, not necessarily a value of f, since a lemma that isn't
// inductive alone needs another beside it):
//   - `lemmas`: a law about every x and f(x), all together by induction on x (the recurrence run as a machine from
//     x = 0, each lemma a law of it, so one may lean on another, and on the facts of the functions `next` reads);
//   - `between`: a law about every x <= y and f(x), f(y) (monotone, say), by induction on y from x, with the lemmas.
// The runtimes compute f by the recurrence (x steps); the Lean export defines it by the same recurrence and proves its
// facts of that definition.
//   const delay = recur('delay', {zero: 1, next: (_, d) => min(d.times(2), 64)}, {
//     'at most 64': (_, d) => d.atMost(64),
//   }, {
//     'never shrinks': (_, d, __, e) => d.atMost(e),
//   })
type FnTerm = (...args: TermLike[]) => Term
type RecurEnv<A extends string, U> = {[a in A]: Term} & {[u in keyof U]: FnTerm}
export type RecurDef<A extends string, U extends Record<string, FnDef>> = {
  args?: readonly A[]
  fns?: U
  zero: TermLike | ((env: RecurEnv<A, U>) => TermLike)
  next: (x: Term, prev: Term, env: RecurEnv<A, U>) => TermLike
}
const reservedInRecur = ['x', 'fx', 'y', 'fy', 'prev', 'x0', 'fx0']
// The machines a recurrence is proven by, built over plain environments.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type LooseRule = any
export const recur = <const A extends string = never, U extends Record<string, FnDef> = {}>(name: string, def: RecurDef<A, U>,
  lemmas: Record<string, (x: Term, fx: Term, env: RecurEnv<A, U>) => Cond> = {},
  between: Record<string, (x: Term, fx: Term, y: Term, fy: Term, env: RecurEnv<A, U>) => Cond> = {}): FnDef & {verdict: Verdict} => {
  const plain = /^[A-Za-z][A-Za-z0-9_]*$/
  if (!plain.test(name)) throw new Error(`recur: ${name} is not a plain name (it names the Lean definition)`)
  const args: string[] = [...(def.args ?? [])], uses = Object.entries(def.fns ?? {}) as [string, FnDef][]
  for (const n of [...args, ...uses.map(([u]) => u)]) if (!plain.test(n) || reservedInRecur.includes(n) || n === name) throw new Error(`recur ${name}: ${n} can't name an argument or a function here (${reservedInRecur.join(', ')} and ${name} are taken)`)
  distinctNames(`recur ${name}`, [...args, ...uses.map(([u]) => u)])
  // A rule reads the function at its arguments paired, which the kernel multiplies out: with five further arguments that
  // is a polynomial of degree 32, past what it can hold.
  if (args.length > 4) throw new Error(`recur ${name}: at most four further arguments`)
  const named = (n: string) => new Term({op: 'var', name: n})
  const argsAt = (ts: Term[]) => Object.fromEntries(args.map((a, i) => [a, ts[i]!])) as {[a in A]: Term}
  const usesAt = (at: (u: string) => string) => Object.fromEntries(uses.map(([u, d]) => [u, fnTerm(at(u), d)])) as {[u in keyof U]: FnTerm}
  const envAt = (ts: Term[], at: (u: string) => string = u => u) => ({...argsAt(ts), ...usesAt(at)}) as RecurEnv<A, U>
  const zeroAt = (ts: Term[], at: (u: string) => string = u => u) => (typeof def.zero === 'function' ? def.zero(envAt(ts, at)) : def.zero)
  // The recurrence over named variables (x, prev, the arguments; lemmas over x and fx; laws between over x, fx, y, fy),
  // the functions it reads by their own names: what the runtimes and the Lean export are made from.
  const own = args.map(named)
  const zero = termOf(zeroAt(own)), next = termOf(def.next(named('x'), named('prev'), envAt(own)))
  const only = (what: string, t: E | C, names: string[], maps: string[]) => {
    if (JSON.stringify(t).includes('"op":"all"') || JSON.stringify(t).includes('"op":"flag"')) throw new Error(`recur ${name}: ${what} takes no quantifier`)
    for (const n of namesIn(t)) if (!names.includes(n)) throw new Error(`recur ${name}: ${what} reads ${n}`)
    for (const m of [...JSON.stringify(t).matchAll(/"op":"get","map":"([^"]+)"/g)].map(x => x[1]!)) if (!maps.includes(m)) throw new Error(`recur ${name}: ${what} reads a function or a map it isn't given (${m})`)
  }
  only('zero', zero, args, uses.map(([u]) => u)); only('next', next, ['x', 'prev', ...args], uses.map(([u]) => u))
  const stated = Object.entries(lemmas).map(([n, f]) => { const holds = f(named('x'), named('fx'), envAt(own)).c; only(`lemma "${n}"`, holds, ['x', 'fx', ...args], uses.map(([u]) => u)); return {name: n, holds} })
  const pairs = Object.entries(between).map(([n, f]) => { const holds = f(named('x'), named('fx'), named('y'), named('fy'), envAt(own)).c; only(`law between "${n}"`, holds, ['x', 'fx', 'y', 'fy', ...args], uses.map(([u]) => u)); return {name: n, holds} })
  const argKinds = Object.fromEntries(args.map(a => [a, nat])) as Kinds
  // The recurrence as a cyclic proof's instance (core/cyclic.ts, GDP_CYCLIC=1): the facts of the functions it reads, from
  // a rule that reads them.
  const recurCase = (between: {name: string, holds: C}[]) => ({name, args, zero, next, lemmas: stated, between,
    facts: uses.length ? ((rule(`${name}'s functions`) as LooseRule).fns(def.fns ?? {}).inputs({}).state({z: 0}).step((env: Record<string, Term>) => ({z: env.z!}) as never) as Rule).machine.facts ?? [] : []})
  const failed = (what: string, v: Verdict) => { if (!(v.proven && v.checked)) throw new Unproven(`${name}'s ${what}`, v) }
  // The lemmas: x counting up from 0 and fx its value, each lemma a law of that machine.
  let verdict: Verdict = {proven: true, checked: true}
  const proofs: NonNullable<Recurrence['proofs']> = {}
  // The usual proofs, to translate (core/cyclic.ts's recurNodes): the lemmas' machine's, the laws between's.
  let lemmaProof: UsualProof | undefined
  const translatedRecur = (u: {lemmas?: UsualProof, between?: UsualProof}): Translated | undefined => (u.lemmas || !stated.length)
    ? st => translatedProof(() => JSON.stringify(['recurrence', recurCase(u.between ? pairs : [])]), () => recurNodes(recurCase(u.between ? pairs : []), u, st), st) : undefined
  if (stated.length) {
    // A start that reads a function is a param given as that start by a fact (a start reads the params alone).
    const zeroReads = JSON.stringify(zero).includes('"op":"get"')
    let r0: LooseRule = (rule(`${name}, by induction`) as LooseRule).params({...argKinds, ...(zeroReads ? {fx0: nat} : {})}).fns(def.fns ?? {}).inputs({})
    if (zeroReads) r0 = r0.facts((p: Record<string, Term>) => ({[`fx0 is ${name}(0)`]: p.fx0!.eq(zeroAt(args.map(a => p[a]!)))}))
    const r: LooseRule = r0.state({x: 0, fx: ((p: Record<string, Term>) => (zeroReads ? p.fx0! : zeroAt(args.map(a => p[a]!)))) as never})
      .step((env: Record<string, Term>) => ({x: env.x!.plus(1), fx: def.next(env.x!, env.fx!, envAt(args.map(a => env[a]!)))}) as never)
    const laws: Law[] = Object.entries(lemmas).map(([n, f]) => r.law(n, (env: Record<string, Term>) => f(env.x!, env.fx!, envAt(args.map(a => env[a]!)))))
    // (Its machine's proof timed alone: the recurrence is compared below as its own instance.)
    const t0 = performance.now()
    usualProof.last = undefined
    verdict = quietly(() => proveRule(r as never, laws, {search: false}))
    lemmaProof = usualProof.last
    if (cyclicOn()) crossCyclic('recurrence', name, verdict.proven && verdict.checked, () => { const {facts, specs} = recurNodes(recurCase([])); return proveCyclic(facts, specs) }, performance.now() - t0, translatedRecur({lemmas: lemmaProof}))
    // (the usual trees checked already, inside quietly: where no cyclic proof is made they are the certificate)
    if (certOn() && verdict.proven && verdict.checked) { const c = certCyclic('recurrence', name, translatedRecur({lemmas: lemmaProof}), () => { const {facts, specs} = recurNodes(recurCase([])); return proveCyclic(facts, specs) }, performance.now() - t0); if (!c.checked) uncovered('recurrence', name, c.why) }
    failed('lemmas', verdict)
    proofs.lemmas = {machine: (r as Rule).machine, laws}
  }
  const js = recurJs(name, args, zero, next, uses)
  const recurrence: Recurrence = {args, zero, next, lemmas: stated, between: pairs, uses: Object.fromEntries(uses.map(([u, d]) => [u, {arity: d.arity, ...(d.lean ? {lean: d.lean} : {})}])), proofs}
  // A law about every n keys (forall counts them by the callback's own parameters).
  const keysOf = (n: number) => (f: (...ks: Term[]) => Cond): Cond | Forall => {
    if (n === 0) return f()
    // A law's keys are counted by its callback's parameters: this one takes n.
    const by = (...ks: Term[]) => f(...ks)
    Object.defineProperty(by, 'length', {value: n})
    return forall(by as never)
  }
  const facts = (withBetween: boolean): FnDef['facts'] => (f, at = {}) => {
    const env = (ts: Term[]) => ({...argsAt(ts), ...Object.fromEntries(uses.map(([u, d]) => [u, at[u] ?? fnTerm(u, d)]))}) as RecurEnv<A, U>
    return {
      [`${name}(0)`]: keysOf(args.length)((...as) => f(0, ...as).eq(typeof def.zero === 'function' ? def.zero(env(as)) : def.zero)),
      [`${name}(x + 1)`]: keysOf(1 + args.length)((k, ...as) => f(k.plus(1), ...as).eq(def.next(k, f(k, ...as), env(as)))),
      ...Object.fromEntries(Object.entries(lemmas).map(([n, l]) => [n, keysOf(1 + args.length)((k, ...as) => l(k, f(k, ...as), env(as)))])),
      ...(withBetween ? Object.fromEntries(Object.entries(between).map(([n, l]) => [n, keysOf(2 + args.length)((k, j, ...as) => k.atMost(j).implies(l(k, f(k, ...as), j, f(j, ...as), env(as))))])) : {}),
    } as Record<string, Cond | Forall>
  }
  const base = {arity: 1 + args.length, js, lean: `Recur.${name}`, recur: recurrence, ...(uses.length ? {uses: def.fns as Record<string, FnDef>} : {})}
  // The laws between two points: y counting up from x and fy from fx, a value at x that meets the lemmas (as f(x)
  // does: they are given of it, as facts of the params), each law a law of that machine beside the lemmas at y. What
  // holds there for every such fx holds for f(x), and fy is f(y) by the recurrence; the machine reads no f at all.
  if (pairs.length) {
    const at = (env: Record<string, Term>) => args.map(a => env[a]!)
    let r0: LooseRule = (rule(`${name}, between`) as LooseRule).params({...argKinds, x: nat, fx: nat}).fns(def.fns ?? {}).inputs({})
    if (stated.length) r0 = r0.facts((p: Record<string, Term>) => Object.fromEntries(Object.entries(lemmas).map(([n, l]) => [`${n} at x`, l(p.x!, p.fx!, envAt(at(p)))])))
    const r: LooseRule = r0.state({y: ((p: Record<string, Term>) => p.x!) as never, fy: ((p: Record<string, Term>) => p.fx!) as never})
      .step((env: Record<string, Term>) => ({y: env.y!.plus(1), fy: def.next(env.y!, env.fy!, envAt(at(env)))}) as never)
    const laws = [...Object.entries(lemmas).map(([n, l]) => r.law(`${n} at y`, (env: Record<string, Term>) => l(env.y!, env.fy!, envAt(at(env))))),
      ...Object.entries(between).map(([n, l]) => r.law(n, (env: Record<string, Term>) => l(env.x!, env.fx!, env.y!, env.fy!, envAt(at(env)))))]
    usualProof.last = undefined
    const t0 = performance.now(), v = quietly(() => proveRule(r as never, laws, {search: false})), usualMs = performance.now() - t0, betweenProof = usualProof.last
    if (cyclicOn()) crossCyclic('recurrence, between', name, v.proven && v.checked, () => { const {facts, specs} = recurNodes(recurCase(pairs)); return proveCyclic(facts, specs) }, usualMs, betweenProof && translatedRecur({lemmas: lemmaProof, between: betweenProof}))
    if (certOn() && v.proven && v.checked) { const c = certCyclic('recurrence, between', name, betweenProof && translatedRecur({lemmas: lemmaProof, between: betweenProof}), () => { const {facts, specs} = recurNodes(recurCase(pairs)); return proveCyclic(facts, specs) }, usualMs); if (!c.checked) uncovered('recurrence, between', name, c.why) }
    failed('laws between two points', v)
    proofs.between = {machine: (r as Rule).machine, laws}
    verdict = {proven: true, checked: verdict.checked && v.checked}
  }
  const out = {...base, verdict, facts: facts(true)}
  recurDefs.set(out, {name, def: def as RecurDef<string, Record<string, FnDef>>, lemmas: lemmas as never, between: between as never})
  return out
}
// What each recurrence was made from, so core/discover.ts can make it again with lemmas it found.
type RecurLemma = (x: Term, fx: Term, env: Record<string, Term>) => Cond
type RecurBetween = (x: Term, fx: Term, y: Term, fy: Term, env: Record<string, Term>) => Cond
const recurDefs = new WeakMap<FnDef, {name: string, def: RecurDef<string, Record<string, FnDef>>, lemmas: Record<string, RecurLemma>, between: Record<string, RecurBetween>}>()
export const recurOf = (d: FnDef) => recurDefs.get(d)
const distinctNames = (what: string, names: string[]) => { if (new Set(names).size !== names.length) throw new Error(`${what}: a name given twice`) }
// A recurrence as JavaScript: a function of its arguments, the functions it reads inlined (each called on its arguments,
// as the runtimes call it).
const recurJs = (name: string, args: string[], zero: E, next: E, uses: [string, FnDef][]): string => {
  const fns = new Map(uses.map(([u], i) => [u, `$f${i}`]))
  const js = (e: E): string => {
    switch (e.op) {
      case 'var': return e.name
      case 'const': return String(e.value)
      case 'add': return `(${js(e.a)} + ${js(e.b)})`
      case 'sub': return `Math.max(0, ${js(e.a)} - ${js(e.b)})`
      case 'mul': return `(${e.k} * ${js(e.a)})`
      case 'prod': return `(${js(e.a)} * ${js(e.b)})`
      case 'min': return `Math.min(${js(e.a)}, ${js(e.b)})`
      case 'max': return `Math.max(${js(e.a)}, ${js(e.b)})`
      case 'if': return `(${jc(e.c)} ? ${js(e.then)} : ${js(e.else)})`
      case 'get': {
        const i = uses.findIndex(([u]) => u === e.map), args = uses[i]![1].arity > 1 ? pairedArgs(e.key, uses[i]![1].arity) : undefined
        return args ? `$g${i}(${args.map(js).join(', ')})` : `${fns.get(e.map)!}(${js(e.key)})`
      }
    }
  }
  const jc = (c: C): string => {
    switch (c.op) {
      case '<': return `(${js(c.a)} < ${js(c.b)})`
      case '<=': return `(${js(c.a)} <= ${js(c.b)})`
      case '=': return `(${js(c.a)} === ${js(c.b)})`
      case 'and': return c.xs.length ? `(${c.xs.map(jc).join(' && ')})` : 'true'
      case 'or': return c.xs.length ? `(${c.xs.map(jc).join(' || ')})` : 'false'
      case 'not': return `(!${jc(c.x)})`
      case 'flag': case 'all': throw new Error('a recurrence takes no flag or quantifier')
    }
  }
  const inlined = uses.map(([u, d], i) => `const $f${i} = (${fnSource(u, d)}); ${d.arity > 1 ? `const $g${i} = (${jsOf(d)}); ` : ''}`).join('')
  // The last value computed at each tuple of further arguments is kept, so reading f at x after f at a smaller x takes
  // only the steps between (a rule that reads f at a count that grows costs one step a request).
  return `(() => { ${inlined}const $memo = new Map(); return (x, ${args.map(a => `${a}, `).join('')}) => { const $k = ${args.length ? `[${args.join(', ')}].join()` : "''"}; let $at = $memo.get($k); if (!$at || $at[0] > x) $at = [0, ${js(zero)}]; let x0 = $at[0], prev = $at[1]; for (; x0 < x; x0++) { prev = ((x, prev) => ${js(next)})(x0, prev); if (!Number.isSafeInteger(prev)) throw new RangeError(${JSON.stringify(`${name} passes the safe integers`)}); } if ($memo.size > 4096) $memo.clear(); $memo.set($k, [x, prev]); return prev; }; })()`
}
// Functions with the functions they read, those first (named <function>.<use>), each with the terms its facts read them by.
const flatFns = (defs: [string, FnDef][]): [string, FnDef, Record<string, FnTerm>][] => defs.flatMap(([n, d]) => {
  const uses = Object.entries(d.uses ?? {}).map(([u, ud]) => [`${n}.${u}`, ud] as [string, FnDef])
  return [...flatFns(uses), [n, d, Object.fromEntries(uses.map(([un, ud]) => [un.slice(n.length + 1), fnTerm(un, ud)]))] as [string, FnDef, Record<string, FnTerm>]]
})
const pairE = (a: E, b: E): E => { const s: E = {op: 'add', a, b}; return {op: 'add', a: {op: 'prod', a: s, b: s}, b} }
const argsKey = (args: E[]): E => args.slice(1).reduce(pairE, args[0]!)
// A function's JavaScript as one function of its key: its arguments unpaired (left-nested, as argsKey pairs them).
const jsOf = (d: FnDef): string => (typeof d.js === 'string' ? d.js : String(d.js))
const fnSource = (name: string, d: FnDef): string => {
  const src = jsOf(d)
  let f: (...args: number[]) => number
  try { f = compileFunction<() => (...args: number[]) => number>([], `return (${src})`)(); f(...Array.from({length: d.arity}, () => 0)) } catch (e) { throw new Error(`function ${name}: its js must be a function of its arguments that reads nothing else (${(e as Error).message})`) }
  if (d.arity === 1) return src
  return `(() => { const $fn = (${src}); return k => { const u = z => { let s = Math.floor(Math.sqrt(z)); while (s * s > z) s--; while ((s + 1) * (s + 1) <= z) s++; return [s - (z - s * s), z - s * s]; }; const a = []; let z = k; for (let i = 1; i < ${d.arity}; i++) { const [p, q] = u(z); a.unshift(q); z = p; } a.unshift(z); return $fn(...a); }; })()`
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
type Writes<V> = V extends Decimal ? DecimalLike | string : V extends Int ? IntLike : V extends Cond ? Cond | boolean : V extends Choice<infer K> ? Choice<K> | K : V extends Maybe<infer W> ? Maybe<W> | Writes<W> | null : V extends Str ? Str | string : V extends Variant<infer C, infer T> ? Variant<C, T> | VariantWrite<C, T> : V extends Term ? TermLike : V extends Record<string, unknown> ? {[k in keyof V]: Writes<V[k]>} : TermLike
type Update<S extends Obj, M extends Obj> = Partial<{[k in keyof S]: Writes<S[k]>} & {[k in keyof M]: M[k] extends CellsRef<unknown> | ItemsRef<unknown> ? PartsWrite : MapWrite}>
let keyCounter = 0
// The callbacks each law, step law and decision was built from, for crossCheck to run again on concrete values.
type Sources = {law?: (env: never) => Cond | Forall, step?: {then: (before: never, after: never) => Cond | Forall, when?: (before: never) => Cond}, decision?: {given: (env: never) => Cond | Cond[], then: (env: never) => Cond, own: number}}
const sources = new WeakMap<object, Sources>()
// A rule's existentials in its precondition and assumption (core/exists.ts): what encodeParams and encodeInput find.
const skolemsOf = new WeakMap<object, {params: {vars: string[], body: C}[], inputs: {vars: string[], body: C}[]}>()
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
const marked = (c: C): C => c.op === 'flag' ? c : c.op === 'all' ? {...c, c: marked(c.c)} : c.op === 'not' ? {op: 'not', x: marked(c.x)} : c.op === 'and' || c.op === 'or' ? {op: c.op, xs: c.xs.map(marked)} : {...c, a: markedE(c.a), b: markedE(c.b)}

type Spec = {
  name: string
  params: [string, Kind<unknown>][]
  inputs: [string, Kind<unknown>][]
  state: [string, number | ((p: never) => TermLike)][]
  maps: [string, number][]
  lists?: string[]
  // Maps and lists of a kind: their parts are in `maps` (and the length in `state`).
  cells?: [string, Kind<unknown>][]
  items?: [string, Kind<unknown>][]
  nodes?: [string, Kind<unknown>, string[], Record<string, NodeFold<unknown, string>>][]
  // State variables declared by a kind: each a value over the kind's variables (in `state`, one entry each).
  kinded?: [string, Kind<unknown>][]
  carried?: string[]
  // Sequences a request carries (in `carried`, each length an input <name>_len), and tables of them (in `carried` with
  // <name>_base and <name>_len, the number of rows an input <name>_rows).
  seqs?: string[]
  seqTables?: string[]
  // Lists of a kind a request carries, each with its folds (their maps are carried too).
  lists2?: [string, Kind<unknown>, Record<string, ListFold<unknown>>, Record<string, ListLemma>][]
  fns?: [string, FnDef][]
  facts?: ((env: never) => Record<string, Cond | Forall>)[]
  // The divisors the rule's laws, step laws, liveness and decisions divide by (modBy, divBy): the machine declares
  // div$k and mod$k for each, beside those its own terms read. Shared by every rule made from this one.
  arith?: Set<number>
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
  // For core/discover.ts: the functions and carried lists the rule reads, and the same rule with functions made again
  // and lemmas added to its lists' folds (each proven here, as carriesList proves its own).
  get parts(): {params: [string, Kind<unknown>][], fns: [string, FnDef][], lists: [string, Kind<unknown>, Record<string, ListFold<unknown>>, Record<string, ListLemma>][]} {
    return {params: this.spec.params, fns: this.spec.fns ?? [], lists: this.spec.lists2 ?? []}
  }
  withParts(fns: Record<string, FnDef>, listLemmas: Record<string, Record<string, ListLemma>> = {}): this {
    const lists = (this.spec.lists2 ?? []).map(([n, k, fs, ls]) => [n, k, fs, {...ls, ...(listLemmas[n] ?? {})}] as [string, Kind<unknown>, Record<string, ListFold<unknown>>, Record<string, ListLemma>])
    for (const [n, k, fs, ls] of lists) if (listLemmas[n]) {
      const v2 = new CarriedList(n, k, v(`${n}_len`), fs, part => new MapRef(part, 0), ls, undefined, this.spec.params).prove()
      if (!(v2.proven && v2.checked)) throw new Unproven(`${n}'s fold lemmas`, v2)
    }
    return this.with({fns: (this.spec.fns ?? []).map(([n, d]) => [n, fns[n] ?? d] as [string, FnDef]), lists2: lists})
  }

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
  // A map of naturals starts every cell at a natural; a map of a kind at the kind's value: `record({...}).from({...})`.
  maps<T extends Record<string, number | Init<unknown>>>(init: T): Rule<P, I, S, M & {[k in keyof T]: T[k] extends Init<infer V> ? CellsRef<V> : MapRef}, F, R, Su, Q> {
    const maps: [string, number][] = [], cells: [string, Kind<unknown>][] = []
    for (const [n, x] of Object.entries(init)) {
      if (typeof x === 'number') { maps.push([n, x]); continue }
      const {kind, init: start} = x as Init<unknown>
      if (typeof start === 'function') throw new Error(`map ${n}: every cell starts at one value (not a term over the params)`)
      const enc = kind.encode(n, start)
      cells.push([n, kind])
      for (const part of kind.vars(n)) maps.push([part, enc[part]!])
    }
    return this.with({maps: [...this.spec.maps, ...maps], cells: [...(this.spec.cells ?? []), ...cells]})
  }
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
  // Lists whose items are values of a kind, each empty at the start: one list per variable of the kind, of one length
  // <name>_len (ItemsRef).
  items<T extends Record<string, Kind<unknown>>>(kinds: T): Rule<P, I, S & {[k in keyof T & string as `${k}_len`]: Term}, M & {[k in keyof T]: ItemsRef<T[k] extends Kind<infer V> ? V : never>}, F, R, Su, Q> {
    const entries = Object.entries(kinds)
    return this.with({maps: [...this.spec.maps, ...entries.flatMap(([n, k]) => k.vars(n).map(part => [part, 0] as [string, number]))],
      state: [...this.spec.state, ...entries.map(([n]) => [`${n}_len`, 0] as [string, number])], items: [...(this.spec.items ?? []), ...entries]})
  }
  // A table of nodes, empty at the start (NodeTable): a tree in the state, made one node a step.
  nodes<const N extends string, V, const C extends string, Fd extends string = never>(name: N, of: Kind<V>, children: readonly C[], folds: {[f in Fd]: NodeFold<V, C, Fd, TablesOf<M>>} = {} as {[f in Fd]: NodeFold<V, C, Fd, TablesOf<M>>}):
    Rule<P, I, S & {[k in N as `${k}_size`]: Term}, M & {[k in N]: NodeTable<V, C, Fd>}, F, R, Su, Q> {
    for (const c of children) if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(c) || c === 'value') throw new Error(`${name}: ${c} can't name a child`)
    for (const f of Object.keys(folds)) if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(f)) throw new Error(`${name}: ${f} is not a plain fold name`)
    distinctNames(name, [...children])
    const maps: [string, number][] = [...of.vars(name).map(part => [part, 0] as [string, number]), ...children.map(c => [`${name}^${c}`, 0] as [string, number]),
      ...Object.entries(folds).map(([f, d]) => [`${name}$${f}`, (d as NodeFold<V, C, Fd>).empty] as [string, number])]
    return this.with({maps: [...this.spec.maps, ...maps], state: [...this.spec.state, [`${name}_size`, 0]], nodes: [...(this.spec.nodes ?? []), [name, of, [...children], folds as never]]})
  }
  // Functions defined outside the rule (fn, divBy, modBy), read like params that take arguments: f(x).
  fns<T extends Record<string, FnDef>>(defs: T): Rule<P & {[k in keyof T]: (...args: TermLike[]) => Term}, I, S, M, F, R, Su, Q> {
    return this.with({fns: [...(this.spec.fns ?? []), ...Object.entries(defs)]})
  }
  // What is given about the functions (with their own facts): laws over the params and functions, each by name.
  facts(f: (p: P) => Record<string, Cond | Forall>): Rule<P, I, S, M, F, R, Su, Q> { return this.with({facts: [...(this.spec.facts ?? []), f as (env: never) => Record<string, Cond | Forall>]}) }
  // Maps each request carries whole (a set of names, say: cells 0 or 1), every cell past them 0; read like any map.
  carries<const N extends string>(...names: N[]): Rule<P, I & {[k in N]: MapRef}, S, M, F, R, Su, Q> { return this.with({carried: [...(this.spec.carried ?? []), ...names]}) }
  // Sequences each request carries (SeqRef): `.carriesSeq('Path')`, then `Path.at(i)`, `Path.len`, `A.prefixOf(B)`; the
  // request gives each as an array of naturals.
  carriesSeq<const N extends string>(...names: N[]): Rule<P, I & {[k in N]: SeqRef}, S, M, F, R, Su, Q> {
    return this.with({carried: [...(this.spec.carried ?? []), ...names], inputs: [...this.spec.inputs, ...names.map(n => [`${n}_len`, nat] as [string, Kind<unknown>])], seqs: [...(this.spec.seqs ?? []), ...names]})
  }
  // Tables of sequences each request carries (SeqTable): `.carriesSeqs('Paths')`, then `Paths.row(r)`, `Paths.rows`; the
  // request gives each as an array of arrays of naturals.
  carriesSeqs<const N extends string>(...names: N[]): Rule<P, I & {[k in N]: SeqTable}, S, M, F, R, Su, Q> {
    return this.with({carried: [...(this.spec.carried ?? []), ...names.flatMap(n => [n, `${n}_base`, `${n}_len`])], inputs: [...this.spec.inputs, ...names.map(n => [`${n}_rows`, nat] as [string, Kind<unknown>])], seqTables: [...(this.spec.seqTables ?? []), ...names]})
  }
  // A list of values of a kind each request carries, with folds over it and lemmas about the folds (CarriedList):
  //   .carriesList('Lines', record({amount: nat}), {total: {from: 0, step: (acc, line) => acc.plus(line.amount)}})
  // Each fold's start and step, and each lemma, may read the params declared before it.
  carriesList<const N extends string, V, Fd extends string = never>(name: N, of: Kind<V>, folds: Record<Fd, ListFold<V, P>> = {} as Record<Fd, ListFold<V, P>>,
    lemmas: Record<string, (acc: Record<Fd, Term>, i: Term, p: P) => Cond> = {}): Rule<P, I & {[k in N]: CarriedList<V, Fd>}, S, M, F, R, Su, Q> {
    const entries = [[name, of, folds, lemmas]] as unknown as [string, Kind<unknown>, Record<string, ListFold<unknown>>, Record<string, ListLemma>][]
    for (const [n, , fs] of entries) for (const f of Object.keys(fs)) if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(f)) throw new Error(`${n}: ${f} is not a plain fold name`)
    // The folds' lemmas, proven now (a lemma that isn't throws, with the verdict).
    for (const [n, k, fs, ls] of entries) {
      const v2 = new CarriedList(n, k, v(`${n}_len`), fs, part => new MapRef(part, 0), ls, undefined, this.spec.params).prove()
      if (!(v2.proven && v2.checked)) throw new Unproven(`${n}'s fold lemmas`, v2)
    }
    for (const [n, , fs] of entries) for (const f of Object.keys(fs)) if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(f)) throw new Error(`${n}: ${f} is not a plain fold name`)
    const maps = entries.flatMap(([n, k, fs]) => [...k.vars(n), ...Object.keys(fs).map(f => `${n}$${f}`)])
    return this.with({carried: [...(this.spec.carried ?? []), ...maps], inputs: [...this.spec.inputs, ...entries.map(([n]) => [`${n}_len`, nat] as [string, Kind<unknown>])], lists2: [...(this.spec.lists2 ?? []), ...entries]})
  }
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
    if (out instanceof Cond) { const p = prenex(out.c, `law ${name}`, key); return this.divides(this.someOf(name, out, p ? {name, forall: key, holds: p} : {name, holds: out.c})) }
    const [k1, more] = keysFor(out), inner = out.forall(v(k1), ...more.map(v)), holds = inner.c
    return this.divides(this.someOf(name, inner, more.length ? {name, forall: k1, keys: more, holds} : {name, forall: k1, holds: prenex(holds, `law ${name}`, k1) ?? holds}))
  }
  // A law's existentials (exists), pulled out before it: `some` its naturals, `witness` the ones given (a ghost's step
  // read with the step's own values).
  private someOf(name: string, out: Cond, law: Law): Law {
    if (!out.ex?.length) return law
    const {vars} = pulledOut([out], `law ${name}`), bs = out.ex
    const terms = Object.assign({}, ...bs.map(b => b.terms ?? {})) as Record<string, E>
    const ghost: Record<string, {start: E, step: E}> = {}
    const env = bs.some(b => b.step) ? this.env({}) : {}
    for (const b of bs) if (b.start && b.step) { const st = b.step(env); for (const n of b.vars) ghost[n] = {start: b.start[n] ?? {op: 'const', value: 0}, step: st[n] ?? {op: 'var', name: n}} }
    const witness = {...(Object.keys(terms).length ? {terms} : {}), ...(Object.keys(ghost).length ? {ghost} : {})}
    return {...law, some: vars, ...(Object.keys(witness).length ? {witness} : {})}
  }
  // What a law, a step law or a decision divides by, noted so the machine declares it (Spec.arith).
  private divides<T extends object>(x: T): T { if (this.spec.arith) divisorsIn([x as never], this.spec.arith); return x }
  // Divide by these too (inferLaws' candidates): the machine declares div$k and mod$k for each.
  dividesBy(...ks: number[]): this { for (const k of ks) (this.spec.arith ??= new Set()).add(divisor(k, 'dividesBy')); return this }
  // The same rule dividing by these too, its own divisors left as they are.
  withDivisors(...ks: number[]): this { return this.with({arith: new Set([...(this.spec.arith ?? []), ...ks.map(k => divisor(k, 'withDivisors'))])}) }

  // What the kinds keep true of the state and of the maps and lists of a kind (Kind.invariant: a flag 0 or 1, a choice or
  // a case in range, a presence bit 0 or 1), as laws: proveRule, proveSteps and proveLeadsTo prove them beside the laws
  // they are given, so a law may lean on "the hold is idle, holding or released" without stating it; give them to
  // toLean (or the kernel) with the rest.
  kindLaws(): Law[] {
    const out: Law[] = []
    const of = (env: unknown, n: string) => (env as Record<string, unknown>)[n]
    for (const [n, k] of this.spec.kinded ?? []) if (k.invariant(k.value(n)).length) out.push(this.law(`${n} is a value of its kind`, env => all(...k.invariant(of(env, n)))))
    for (const [n, k] of [...this.spec.cells ?? [], ...this.spec.items ?? []]) if (k.invariant(k.value(n)).length) {
      out.push(this.law(`every ${n} cell is a value of its kind`, env => forall(key => all(...k.invariant((of(env, n) as CellsRef<unknown>).at(key))))))
    }
    for (const [n, k] of this.spec.nodes ?? []) {
      if (k.invariant(k.value(n)).length) out.push(this.law(`every ${n} node is a value of its kind`, env => forall(key => all(...k.invariant((of(env, n) as NodeTable<unknown>).at(key))))))
      for (const [name] of (this.env({flags: false, inputs: false, queries: false})[n] as NodeTable<unknown>).laws()) out.push(this.law(name, env => (of(env, n) as NodeTable<unknown>).laws().find(([m]) => m === name)![1]))
    }
    return out
  }

  // A law about one step, for every request the rule allows: `then(before, after)` relates what the step reads (params,
  // the request, state, maps, flags, sums, queries) to the state, maps and sums after it. `when` narrows the requests.
  //   counter.stepLaw('never goes back', ({used}, after) => used.atMost(after.used))
  stepLaw(name: string, then: (before: P & I & S & M & F & Su & Q, after: S & M & Su) => Cond | Forall, when?: (before: P & I & S & M & F & Su & Q) => Cond): StepLaw {
    const env = this.env() as never
    const after = this.afterEnv()
    const out = then(env, after as never), w = when ? {when: when(env).c} : {}
    const key = `key$${++keyCounter}`, src: Sources = {step: {then: then as never, ...(when ? {when: when as never} : {})}}
    if (out instanceof Cond) { const p = prenex(out.c, `step law ${name}`, key); return withSource(this.divides(p ? {name, forall: key, then: p, ...w} : {name, then: out.c, ...w}), src) }
    const [k1, more] = keysFor(out), c = out.forall(v(k1), ...more.map(v)).c
    return withSource(this.divides(more.length ? {name, forall: k1, keys: more, then: c, ...w} : {name, forall: k1, then: prenex(c, `step law ${name}`, k1) ?? c, ...w}), src)
  }

  // A law about k steps in a row (k from 2 to 64): `then(first, last, requests)` relates what the first step reads to the
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
    if (out instanceof Cond) { const p = prenex(out.c, `step law ${name}`, key); return this.divides(p ? {name, steps: k, forall: key, then: marked(p), ...w} : {name, steps: k, then: marked(out.c), ...w}) }
    const [k1, more] = keysFor(out), c = out.forall(v(k1), ...more.map(v)).c
    return this.divides(more.length ? {name, steps: k, forall: k1, keys: more, then: marked(c), ...w} : {name, steps: k, forall: k1, then: marked(prenex(c, `step law ${name}`, k1) ?? c), ...w})
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
  // With no rank, proveLeadsTo finds one from the rule's runs (core/cycles.ts's findLeadsTo).
  leadsTo(name: string, spec: {from: (env: P & S & M & Su) => Cond, to: (env: P & S & M & Su) => Cond, rank?: (env: P & S & M & Su) => TermLike | TermLike[],
    helpful: ((env: P & S & M & Su) => Record<string, TermLike>) | {when?: (env: P & S & M & Su) => Cond, request: (env: P & S & M & Su) => Record<string, TermLike>}[]}): Liveness {
    const env = this.env({flags: false, inputs: false, queries: false}) as never
    const req = (f: (env: never) => Record<string, TermLike>) => Object.fromEntries(Object.entries(f(env)).map(([n, t]) => [n, termOf(t)]))
    const r = spec.rank ? spec.rank(env) : [], rank = Array.isArray(r) ? r.map(termOf) : termOf(r)
    const base = {name, from: spec.from(env).c, to: spec.to(env).c, rank}
    return this.divides(typeof spec.helpful === 'function' ? {...base, request: req(spec.helpful)} : {...base, helpful: spec.helpful.map(h => ({...(h.when ? {when: h.when(env).c} : {}), request: req(h.request)}))})
  }

  // A decision: whenever the params and the request meet `given`, `then` holds. Decisions don't read the state; the
  // functions' facts are assumed at the arguments the decision reads them at, and a carried list's equations (each
  // fold's start, its step and its lemmas) at the list's end, the key before it and every key the decision reads it at.
  // A condition about every key (`everyKey`, `subsetOf`, ...) in `given` or `then` makes the decision a step law of
  // this rule (its conditions as flags, the step left as it is): the flags' quantifiers are what the kernel closes.
  decide(name: string, given: (env: P & I) => Cond | Cond[], then: (env: P & I) => Cond): Decision {
    const env = this.env({flags: false, state: false, queries: false}) as never
    const g = given(env), hyps = [...this.kindAssumptions(), ...this.spec.pre.map(f => f(env as never).c), ...this.spec.assume.map(f => f(env as never).c), ...(Array.isArray(g) ? g : [g]).map(c => c.c)]
    const t = then(env).c
    const lists = (this.spec.lists2 ?? []).map(([n]) => (env as Record<string, unknown>)[n] as CarriedList<unknown>)
    const listed = lists.flatMap(l => l.equationsAt(uniqueTerms([l.len, l.len.minus(1), ...keysRead([...hyps, t], l.maps)])).map(c => c.c))
    const goal: Goal = this.divides({name, hyps: [...listed, ...hyps, {op: 'not', x: t}]})
    const facts = this.spec.fns?.length || this.spec.facts?.length || this.spec.arith?.size ? factsFor(this.machine, goal) : []
    const d: Decision = {name, rule: this as Rule<Obj>, given: hyps, then: t, goal: {name, hyps: [...facts, ...goal.hyps]}}
    if ([...(Array.isArray(g) ? g : [g]).map(c => c.c), t].some(quantifiedIn)) {
      const conds = (e: never) => { const own = given(e); return {given$: all(...(Array.isArray(own) ? own : [own])), then$: then(e)} }
      const r = (this.spec.step ? this : this.step(() => ({}) as never)).flags(conds as never) as unknown as Rule<Obj>
      const flag = (f: string) => (env: object) => (env as Record<string, Cond>)[f]!
      d.steps = {rule: r, law: r.stepLaw(name, flag('then$'), flag('given$'))}
    }
    return withSource(d, {decision: {given: given as never, then: then as never, own: Array.isArray(g) ? g.length : 1}})
  }
  // A decision about two requests under the same params (noninterference, say: requests that differ only in a secret
  // are decided alike). `given` and `then` read both; the second request's inputs are named b.<input> in a witness.
  //   r.relate('the secret is irrelevant', (a, b) => a.user.eq(b.user), (a, b) => a.allowed.iff(b.allowed))
  relate(name: string, given: (a: P & I, b: P & I) => Cond | Cond[], then: (a: P & I, b: P & I) => Cond): Decision {
    const s = this.spec, b = (n: string) => `b.${n}`, own = [...s.inputs.map(([n]) => n), ...(s.carried ?? [])]
    if (s.lists2?.length) throw new Error(`${s.name}: a decision about two requests takes no carried list`)
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
    this.composites(after, part => `${part}'`, n => v(`${n}_len'`))
    for (const [n, k] of this.spec.kinded ?? []) { for (const part of k.vars(n)) delete after[part]; after[n] = k.value(n, primed) }
    return after
  }
  // The values handed to the builders' callbacks.
  private env(parts: {inputs?: boolean, state?: boolean, flags?: boolean, queries?: boolean} = {}): Record<string, unknown> {
    this.distinct()
    const out: Record<string, unknown> = {}
    for (const [n, k] of this.spec.params) out[n] = k.value(n)
    for (const [n, d] of this.spec.fns ?? []) out[n] = fnTerm(n, d)
    if (parts.inputs !== false) {
      for (const [n, k] of this.spec.inputs) out[n] = k.value(n)
      for (const n of this.spec.carried ?? []) out[n] = new MapRef(n, 0)
      for (const n of this.spec.seqs ?? []) { delete out[`${n}_len`]; out[n] = new SeqRef(new MapRef(n, 0), v(`${n}_len`)) }
      for (const n of this.spec.seqTables ?? []) { for (const part of [`${n}_base`, `${n}_len`, `${n}_rows`]) delete out[part]; out[n] = new SeqTable(n, v(`${n}_rows`)) }
      const ps = Object.fromEntries(this.spec.params.map(([n]) => [n, out[n]]))
      for (const [n, k, fs, ls] of this.spec.lists2 ?? []) { const l = new CarriedList(n, k, v(`${n}_len`), fs, part => new MapRef(part, 0), ls, ps, this.spec.params); for (const part of l.maps) delete out[part]; out[n] = l }
    }
    if (parts.state !== false) {
      for (const [n] of this.spec.state) out[n] = v(n)
      for (const [n, init] of this.spec.maps) out[n] = new MapRef(n, init)
      for (const n of this.spec.lists ?? []) out[n] = new ListRef(n, v(`${n}_len`))
      this.composites(out, part => part, n => v(`${n}_len`))
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
  // Maps and lists of a kind in place of their parts' maps (and a list's length), each part's map named by `at`.
  private composites(out: Record<string, unknown>, at: (part: string) => string, len: (name: string) => Term): void {
    const init = new Map(this.spec.maps)
    for (const [n, k] of this.spec.cells ?? []) { for (const part of k.vars(n)) delete out[part]; out[n] = new CellsRef(n, k, part => new MapRef(at(part), init.get(part)!)) }
    for (const [n, k] of this.spec.items ?? []) { for (const part of k.vars(n)) delete out[part]; out[n] = new ItemsRef(n, k, len(n), part => new ListRef(at(part), len(n))) }
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const tables: Record<string, NodeTable<any, any, any>> = {}
    for (const [n, k, cs, fs] of this.spec.nodes ?? []) {
      const t = new NodeTable(n, k, cs, fs, v(at(`${n}_size`)), part => new MapRef(at(part), init.get(part)!), {...tables})
      tables[n] = t
      for (const part of [...k.vars(n), ...cs.map(c => `${n}^${c}`), ...Object.keys(fs).map(f => `${n}$${f}`)]) delete out[part]
      out[n] = t
    }
  }
  // Every name the rule declares is declared once (a flag named again replaces the earlier one, so flags are checked as
  // they are defined): an input and a state variable sharing a name would hand the callbacks only one of them.
  private names(): [string, string][] {
    const s = this.spec
    return [...s.params.map(([n]) => [n, 'a param']), ...(s.fns ?? []).map(([n]) => [n, 'a function']), ...s.inputs.map(([n]) => [n, 'an input']), ...(s.carried ?? []).map(n => [n, 'a carried map']),
      ...s.state.map(([n]) => [n, 'a state variable']), ...s.maps.map(([n]) => [n, 'a map']), ...s.sums.map(([n]) => [n, 'a sum']), ...s.queries.map(([n]) => [n, 'a query']),
      ...[...(s.cells ?? []), ...(s.items ?? [])].filter(([n, k]) => !k.vars(n).includes(n)).map(([n]) => [n, 'a map of a kind']),
      ...(s.nodes ?? []).map(([n]) => [n, 'a table of nodes']),
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
    expandParts(updates)
    const state: Record<string, E> = {}, maps: Record<string, MapUpdate> = {}
    for (const [n, u] of Object.entries(updates) as [string, TermLike | MapWrite | undefined][]) {
      if (u === undefined) continue
      if (typeof u === 'object' && 'map' in u) {
        if (u.map !== n) throw new Error(`${s.name}: the step writes map ${u.map} under the name ${n}`)
        maps[n] = 'each' in u ? {each: u.each, value: hoist.term(u.value, [u.each])} : {key: hoist.term(u.key), value: hoist.term(u.value)}
      } else state[n] = hoist.term(termOf(u))
    }
    // An existential in a precondition or the assumption: a value the params or the request bring (a param or an input
    // the runtimes find, encodeParams and encodeInput), fresh for each existential and, for a request, each step.
    const pre0 = pulledOut(s.pre.map(f => f(pEnv as never)), `${s.name}: a precondition`, 'some$p'), as0 = pulledOut(s.assume.map(f => f(env as never)), `${s.name}: the assumption`, 'some$a')
    const known = new Set([...params, ...inputs])
    for (const b of as0.bodies) { const out = namesIn(b.body).filter(n => !known.has(n) && !as0.vars.includes(n)); if (out.length) throw new Error(`${s.name}: an exists(...) in the assumption reads ${out[0]}: it reads only the params and the request (its value comes with the request)`) }
    skolemsOf.set(this, {params: pre0.bodies, inputs: as0.bodies})
    params.push(...pre0.vars); inputs.push(...as0.vars)
    const pre = [...this.kindAssumptions('params'), ...pre0.cs]
    const assume = [...this.kindAssumptions('inputs'), ...(s.lists2 ?? []).flatMap(([n]) => (env[n] as CarriedList<unknown>).equations().map(c => hoist.cond(c.c))), ...as0.cs.map(c => hoist.cond(c))]
    placed()
    // Functions, and their facts: each function's own (named after it), then the rule's.
    // The functions a function reads come first, each named <function>.<use>.
    const flat = flatFns(s.fns ?? [])
    const fns: Record<string, Fn> = Object.fromEntries(flat.map(([n, d]) => [n, {js: fnSource(n, d), ...(d.arity > 1 ? {arity: d.arity, call: jsOf(d)} : {}), ...(d.lean ? {lean: d.lean} : {}), ...(d.recur ? {recur: d.recur} : {})}]))
    const facts: Law[] = [
      ...flat.flatMap(([n, d, uses]) => Object.entries(d.facts?.(fnTerm(n, d), uses) ?? {}).map(([name, f]) => this.lawOf(`${n}: ${name}`, f))),
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
    return withArithmetic(m, [], s.arith ?? [])
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
        const input = this.randomInput(rand, bound, params)
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
    const updates = inScope(sc, () => expandParts(s.step?.(this.env() as never) ?? {})) as Record<string, unknown>
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
  compare<St extends Record<string, Raw>>(reference: {init(params: Value<P>): St, step(params: Value<P>, st: St, request: RawInputs<I>): St},
    opts: Draws<RawInputs<I>> & {params?: (rand: Rand) => Value<P>, depth?: number} = {}): Agreement {
    const s = this.spec, rand = opts.rand ?? seeded(5), bound = opts.bound ?? 100, gen = this.compiled(), run = interpret(this.machine)
    let checked = 0
    const sample = (kinds: [string, Kind<unknown>][]) => Object.fromEntries(kinds.map(([n, k]) => [n, k.sample(rand, bound)]))
    for (let trial = 0; trial < (opts.trials ?? 200); trial++) {
      const params = (opts.params?.(rand) ?? sample(s.params)) as Value<P>, ps = this.encodeParams(params as never)
      let ours = gen.init(ps), theirs = reference.init(params)
      const edges = trial === 0 ? opts.edges ?? [] : []
      for (let d = 0; d < (opts.depth ?? 10) + edges.length; d++) {
        const request = edges[d] ?? opts.draw?.(rand) ?? sample(s.inputs) as RawInputs<I>, encoded = this.encodeInput(request as never, params as never)
        // A request the rule's assumption refuses is no step of the rule: the runtimes throw, so it isn't compared.
        if (!allowed(this.machine, run, ps, ours, encoded)) continue
        ours = gen.step(ps, ours, encoded); theirs = reference.step(params, theirs, request)
        const got = this.decode(ours)
        for (const [field, want] of Object.entries(theirs)) {
          checked++
          if (!sameRaw(got[field], want)) return {checked, failure: `${s.name}, params ${JSON.stringify(params)}, after ${JSON.stringify(request)}: ${field} is ${shown(got[field])} here, ${shown(want)} in the code it describes`}
        }
      }
    }
    return {checked}
  }

  // --- running it -----------------------------------------------------------------------------------------------------
  // Runtime values (numbers, booleans, choice names, null for a missing value) to the variables the machine reads.
  encodeParams(values: {[k in keyof P]: Raw}): Record<string, number> { return this.withSkolems('params', encode(this.spec.params, values as Record<string, Raw>)) }
  // The values the params or a request bring for the existentials of a precondition or the assumption: each a witness
  // found (exact for one natural or integer read linearly), or 0 where none is (the precondition or the assumption then
  // fails, so the params or the request are refused).
  private withSkolems<T extends Record<string, number | ReadonlyMap<number, number>>>(which: 'params' | 'inputs', out: T, params?: Record<string, number>): T {
    if (!skolemsOf.has(this)) void this.machine
    const sk = skolemsOf.get(this)?.[which] ?? []
    if (!sk.length) return out
    const m = this.machine, env: Record<string, number> = {...params, ...numbersOf(out as Request)}
    for (const b of sk) {
      const w = someHolds(b.body, b.vars, env, {scalars: {}, maps: {}}, m)?.witness ?? {}
      for (const n of b.vars) { (out as Record<string, number>)[n] = w[n] ?? 0; env[n] = w[n] ?? 0 }
    }
    return out
  }
  // A carried map is a Set of keys (each cell 1), an array of them, or a Map of key to natural; a sequence an array of
  // naturals, a table of them an array of such arrays.
  // A carried list is an array of its items' runtime values (its length and folds computed from them); `params`, what
  // folds that read the params are computed with.
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  encodeInput(values: {[k in keyof I]: I[k] extends MapRef ? ReadonlySet<number> | readonly number[] | ReadonlyMap<number, number> : I[k] extends SeqRef ? readonly number[] : I[k] extends SeqTable ? readonly (readonly number[])[] : I[k] extends CarriedList<any, any> ? readonly Raw[] : Raw}, params?: {[k in keyof P]: Raw}): Request {
    const at = params && this.paramValues(this.encodeParams(params))
    const lists = Object.fromEntries((this.spec.lists2 ?? []).map(([n, k, fs]) => [n, new CarriedList(n, k, v(`${n}_len`), fs, part => new MapRef(part, 0), {}, at).encode((values as Record<string, Raw>)[n])]))
    // A sequence: its values at their positions (no 0 cell), its length; a table: the rows one after another in one map,
    // each row's offset and length.
    const seqMaps: Record<string, Map<number, number>> = {}, seqLens: Record<string, number> = {}
    const cells = (xs: readonly number[], from = 0) => xs.flatMap((x, i) => (x ? [[from + i, x] as [number, number]] : []))
    for (const n of this.spec.seqs ?? []) { const xs = (values as Record<string, readonly number[]>)[n] ?? []; seqMaps[n] = new Map(cells(xs)); seqLens[`${n}_len`] = xs.length }
    for (const n of this.spec.seqTables ?? []) {
      const rows = (values as Record<string, readonly (readonly number[])[]>)[n] ?? [], base: number[] = []
      rows.reduce((at, r) => (base.push(at), at + r.length), 0)
      seqMaps[n] = new Map(rows.flatMap((r, i) => cells(r, base[i])))
      seqMaps[`${n}_base`] = new Map(base.flatMap((b, i) => (b ? [[i, b] as [number, number]] : [])))
      seqMaps[`${n}_len`] = new Map(rows.flatMap((r, i) => (r.length ? [[i, r.length] as [number, number]] : [])))
      seqLens[`${n}_rows`] = rows.length
    }
    const out: Request = encode(this.spec.inputs, {...values as Record<string, Raw>, ...seqLens, ...Object.fromEntries(Object.entries(lists).map(([n, l]) => [`${n}_len`, l.len]))})
    for (const l of Object.values(lists)) Object.assign(out, l.maps)
    Object.assign(out, seqMaps)
    for (const n of this.spec.carried ?? []) {
      if (n in out) continue
      const given = (values as Record<string, unknown>)[n]
      out[n] = given instanceof Map ? new Map(given as Map<number, number>) : new Map([...(given as Iterable<number>)].map(key => [key, 1] as const))
    }
    return this.withSkolems('inputs', out, params && this.encodeParams(params))
  }
  // Each carried list's folds at its end (what `L.fold.<f>` reads), computed from its items as encodeInput computes
  // them, without running the rule: `foldsOf({Lines: [...]})` → {Lines: {total: 30}}. Only the lists given.
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  foldsOf(values: {[k in keyof I]?: I[k] extends CarriedList<any, any> ? readonly Raw[] : never}, params?: {[k in keyof P]: Raw}): Record<string, Record<string, number>> {
    const at = params && this.paramValues(this.encodeParams(params))
    return Object.fromEntries((this.spec.lists2 ?? []).filter(([n]) => n in values).map(([n, k, fs]) => {
      const {maps, len} = new CarriedList(n, k, v(`${n}_len`), fs, part => new MapRef(part, 0), {}, at).encode((values as Record<string, Raw>)[n])
      return [n, Object.fromEntries(Object.keys(fs).map(f => [f, maps[`${n}$${f}`]!.get(len) ?? 0]))]
    }))
  }
  // The state's variables declared with a kind (a yes/no, a choice, an integer...), with their kinds.
  kindsOfState(): [string, Kind<unknown>][] { return this.spec.kinded ?? [] }
  // Random params and inputs that meet their kinds (not the user's `pre` or `assume`, which a caller checks).
  randomParams(rand: Rand, bound: number): Record<string, number> { return this.withSkolems('params', Object.assign({}, ...this.spec.params.map(([n, k]) => k.random(n, rand, bound)))) }
  // The params' values by their kinds, as constants (what a fold that reads them is computed with).
  private paramValues(ps: Record<string, number>): Record<string, unknown> {
    return Object.fromEntries(this.spec.params.map(([n, k]) => [n, k.build(n, part => new Term({op: 'const', value: ps[part]!}, ps[part]!))]))
  }
  // `ps`: the params (encoded), for folds that read them.
  randomInput(rand: Rand, bound: number, ps?: Record<string, number>): Request {
    const out: Request = Object.assign({}, ...this.spec.inputs.map(([n, k]) => k.random(n, rand, bound)))
    for (const n of this.spec.carried ?? []) out[n] = new Map(Array.from({length: bound + 1}, (_, key) => [key, rand(2)] as const).filter(([, cell]) => cell === 1))
    // A carried list: items drawn by their kind, its length and folds as the encoding computes them.
    for (const [n, k, fs] of this.spec.lists2 ?? []) {
      const l = new CarriedList(n, k, v(`${n}_len`), fs, part => new MapRef(part, 0), {}, ps && this.paramValues(ps)).encode(Array.from({length: rand(bound + 1)}, () => k.sample(rand, bound)))
      Object.assign(out, l.maps, {[`${n}_len`]: l.len})
    }
    return this.withSkolems('inputs', out, ps)
  }
  // The state's scalars as runtime values: each kinded variable as its kind decodes it (an integer as one signed
  // number, a decimal as its number, a choice by name, a string as itself, none as null).
  decode(st: State): Record<string, Raw> {
    const out: Record<string, Raw> = {...st.scalars}
    for (const [n, k] of this.spec.kinded ?? []) { for (const part of k.vars(n)) delete out[part]; out[n] = k.decode(n, st.scalars) }
    // A map of a kind: the keys any of its parts holds a cell at, each with its value; a list of a kind: its items.
    const cell = (n: string, k: Kind<unknown>, key: number) => k.decode(n, Object.fromEntries(k.vars(n).map(part => [part, st.maps[part]?.get(key) ?? st.defaults?.[part] ?? new Map(this.spec.maps).get(part)!])))
    for (const [n, k] of this.spec.cells ?? []) {
      const keys = [...new Set(k.vars(n).flatMap(part => [...(st.maps[part]?.keys() ?? [])]))].sort((a, b) => a - b)
      out[n] = Object.fromEntries(keys.map(key => [key, cell(n, k, key)]))
    }
    for (const [n, k] of this.spec.items ?? []) out[n] = Array.from({length: st.scalars[`${n}_len`]!}, (_, i) => cell(n, k, i)) as never
    // A table of nodes: node 1 first, each its value and its children.
    for (const [n, k, cs] of this.spec.nodes ?? []) {
      const at = (part: string, key: number) => st.maps[part]?.get(key) ?? 0
      out[n] = Array.from({length: st.scalars[`${n}_size`]!}, (_, i) => ({value: cell(n, k, i + 1), ...Object.fromEntries(cs.map(c => [c, at(`${n}^${c}`, i + 1)]))})) as never
    }
    return out
  }
  // The prune order's variable, if the history is pruned (a runtime must send it nondecreasing).
  get orderedBy(): string | undefined { return this.spec.prune ? new Map(this.spec.inputs).get(this.spec.prune.order)!.vars(this.spec.prune.order)[0] : undefined }
  interpreter() { return interpret(this.machine) }
  compiled(): {init: (params: object) => State & {head?: number}, fork: (st: State) => State, step: (params: object, st: State, input: object) => State & {head?: number}} {
    return loadJs(this.machine)
  }
}
// A step's writes to maps and lists of a kind, as the writes to their parts' maps.
const expandParts = <T extends Record<string, unknown>>(updates: T): T => {
  for (const [n, u] of Object.entries(updates)) if (isPartsWrite(u)) { delete updates[n]; Object.assign(updates, u.parts) }
  return updates
}
const encode = (kinds: [string, Kind<unknown>][], values: Record<string, Raw>): Record<string, number> => Object.assign({}, ...kinds.map(([n, k]) => k.encode(n, values[n])))

export const rule = (name: string): Rule => new Rule({name, params: [], inputs: [], state: [], maps: [], flags: [], pre: [], assume: [], sums: [], queries: [], arith: new Set()})

// The values a rule's callbacks receive, for helpers written outside the chain (a decision's condition, a shared law):
// `(env: DecisionEnv<typeof r>) => ...`.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyOf<R, K extends 'decide' | 'step' | 'law'> = R extends Rule<infer P, infer I, infer S, infer M, infer F, any, infer Su, infer Q> ? K extends 'decide' ? P & I : K extends 'law' ? P & S & M & Su : P & I & S & M & F & Su & Q : never
export type DecisionEnv<R> = AnyOf<R, 'decide'>
export type StepEnv<R> = AnyOf<R, 'step'>
export type LawEnv<R> = AnyOf<R, 'law'>

// --- decisions and loops ------------------------------------------------------------------------------------------

// `steps`: the decision as a step law of its rule, where it reads a condition about every key (`decide`).
export type Decision = {name: string, rule: Rule<Obj>, given: C[], then: C, goal: Goal, steps?: {rule: Rule<Obj>, law: StepLaw}}
const quantifiedE = (e: E): boolean => e.op === 'if' ? quantifiedIn(e.c) || quantifiedE(e.then) || quantifiedE(e.else) : 'a' in e && typeof e.a === 'object' ? quantifiedE(e.a) || ('b' in e && typeof e.b === 'object' && quantifiedE(e.b)) : false
const quantifiedIn = (c: C): boolean => c.op === 'all' || (c.op === 'not' ? quantifiedIn(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.some(quantifiedIn) : c.op === 'flag' ? false : quantifiedE(c.a) || quantifiedE(c.b))

// A function: arguments in, a result out, each field of the result a term or a condition over the arguments, the
// params and the functions it reads. Its laws are decisions about the same terms it computes, so what is proven is what
// runs (`run`, the compiled one-step rule whose state after the step is the result).
//   const reserve = fun('reserve').inputs({left: nat, used: nat}).returns(({left, used}) => ({granted: left.gt(0), left: left.minus(1), used: used.plus(1)}))
//   reserve.law('an empty budget grants nothing', ({left}) => left.eq(0), out => out.granted.not())
// (A field of no known kind, `any`, is a term.)
type ResultOf<V> = 0 extends 1 & V ? Term : [V] extends [Cond] ? Cond : [V] extends [Decimal] ? Decimal : [V] extends [Int] ? Int : [V] extends [Choice<infer K>] ? Choice<K> : [V] extends [Str] ? Str : [V] extends [Variant<infer C, infer T>] ? Variant<C, T> : [V] extends [Maybe<infer W>] ? Maybe<ResultOf<W>> : [V] extends [Term | number] ? Term : [V] extends [Record<string, unknown>] ? {[f in keyof V]: ResultOf<V[f]>} : Term
type Result<T> = {[k in keyof T]: ResultOf<T[k]>}
type ValueOf<V> = 0 extends 1 & V ? number : [V] extends [Cond] ? boolean : [V] extends [Choice<infer K>] ? K : [V] extends [Str] ? string : [V] extends [Variant<infer C, infer T>] ? CaseRaw<C, T> : [V] extends [Maybe<infer W>] ? ValueOf<W> | null : [V] extends [Term | number | Int | Decimal] ? number : [V] extends [Record<string, unknown>] ? {[f in keyof V]: ValueOf<V[f]>} : number
type CaseRaw<C extends Cases, T extends string = 'tag'> = {[k in keyof C]: {[t in T]: k} & {[f in keyof C[k]]: C[k][f] extends Kind<infer V> ? ValueOf<V> : never}}[keyof C]
type Value<T> = {[k in keyof T]: ValueOf<T[k]>}
// A request's runtime values: a carried map as a set of keys (or an array of them, or a map of key to natural), a carried
// list as an array of its items' values, anything else as its kind's value (what encodeInput takes).
type RawInputs<T> = {[k in keyof T]: T[k] extends MapRef ? ReadonlySet<number> | readonly number[] | ReadonlyMap<number, number> : T[k] extends SeqRef ? readonly number[] : T[k] extends SeqTable ? readonly (readonly number[])[] : T[k] extends CarriedList<infer V, infer _F> ? readonly ValueOf<V>[] : ValueOf<T[k]>}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Field = Term | Cond | Int | Decimal | Choice<string> | Str | Variant<any, any> | Maybe<any> | {[f: string]: Field | number}
// The kind a result field is kept in.
const kindOf = (t: Field | number): Kind<unknown> => (t instanceof Cond ? bool : t instanceof Int ? int : t instanceof Decimal ? decimal(t.places) : t instanceof Choice ? oneOf(...t.values) : t instanceof Str ? str({like: t.patterns})
  : t instanceof Variant ? t.kind : t instanceof Maybe ? maybe(kindOf(t.inner as Field)) : isRecord(t) ? record(Object.fromEntries(Object.entries(t).map(([f, x]) => [f, kindOf(x as Field)]))) : nat)
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
    return lawOfFun(this as never, this.r.decide(name, env => given(env, this.result(env) as never), env => then(this.result(env) as never, env)))
  }
  // A law about two calls under the same params: `then(outA, outB, a, b)` given `given(a, b)` (noninterference, say).
  relate(name: string, given: (a: P & I, b: P & I) => Cond | Cond[], then: (outA: O, outB: O, a: P & I, b: P & I) => Cond): Decision {
    return lawOfFun(this as never, this.r.relate(name, given, (a, b) => then(this.result(a) as never, this.result(b) as never, a, b)))
  }

  // Against the code it describes: `reference` called with the same arguments (drawn by their kinds, or by `draw`, the
  // `edges` first) must return the same value for every field it returns (a field it leaves out is not compared). The
  // check for an encoding: that the terms here are what the real function computes, on its real inputs.
  //   cap.compare(({left, local}) => ({out: realCap(left, local)}), {edges: [{left: 2 ** 32 + 5, local: 10}]})
  compare(reference: (values: Value<I>, params: Value<P>) => Partial<Value<O>>, opts: Draws<Value<I>> & {params?: Value<P>} = {}): Agreement {
    const rand = opts.rand ?? seeded(5), bound = opts.bound ?? 1000, params = (opts.params ?? {}) as Value<P>, kinds = this.r['spec'].inputs
    let checked = 0
    const draws = [...(opts.edges ?? []), ...Array.from({length: opts.trials ?? 2000}, () => opts.draw?.(rand) ?? Object.fromEntries(kinds.map(([n, k]) => [n, k.sample(rand, bound)])) as Value<I>)]
    for (const values of draws) {
      const ours = this.run(values, params) as Record<string, unknown>, theirs = reference(values, params) as Record<string, unknown>
      for (const [field, want] of Object.entries(theirs)) {
        checked++
        if (!sameRaw(ours[field], want)) return {checked, failure: `${this.name} at ${JSON.stringify(values)}: ${field} is ${shown(ours[field])} here, ${shown(want)} in the code it describes`}
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
    const st = rule.decode(gen.step(ps, gen.init(ps), rule.encodeInput(values as never, params as never)))
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
  get hasRank(): boolean { return !!this.spec.rank }
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

// `run`: a real run from the start that breaks the law (params, and each request in order, a carried map as its cells),
// when a few random runs found one before the prover ran (a step law broken from a state no run is known to reach comes
// back with its `witness` alone).
// `found`: what the search found and proved beside the laws (`proveRule`'s, `proveSteps`'s), as laws to pass with them and
// as lemmas to state in `recur` or `carriesList` (source to paste).
// `witnesses`: for each law with "there exists", the witness it was proven through, as it reads.
export type Verdict = {proven: boolean, checked: boolean, stuck?: string, goal?: string, witness?: Record<string, number>, why?: string, trees?: Record<string, Tree>, run?: {params: Record<string, number>, trace: Record<string, unknown>[]}, found?: Found, witnesses?: Record<string, string>}
// `facts`: lemmas about the rule's functions (those known by their facts) proven from those facts by a cyclic proof
// (core/cycles.ts), the laws proven with them; `rank`: a loop's rank, found from its runs (`proveLoop` with none).
export type Found = {laws?: {law: Law, text: string, source?: string}[], lemmas?: Record<string, {lemmas?: string[], between?: string[]}>, facts?: string[], rank?: string}
// `search`: where the laws aren't proven and no run breaks them, what they need may be what nobody stated, so the
// prover looks for it within `ms` (10 s): lemmas about the rule's recurrences and its lists' folds (core/discover.ts),
// then lemmas about the functions known by their facts, each proven by a cyclic proof (core/cycles.ts; `cycles: false`
// leaves them out), then invariants (core/infer.ts), each proven by the kernel with the laws, the verdict theirs.
// `{search: false}`: the prover alone.
export type ProveOptions = {search?: boolean | {ms?: number, cycles?: boolean}}
// A verdict that isn't a checked proof, as the error a lemma, a guard or a gate is refused with (the verdict on `.verdict`).
export class Unproven extends Error {
  constructor(what: string, readonly verdict: Verdict) {
    const found = [verdict.goal && `goal ${verdict.goal}`, verdict.stuck, verdict.witness && `a counterexample: ${JSON.stringify(verdict.witness)}`, verdict.why].filter(Boolean).join('; ')
    super(`${what}: ${verdict.proven ? 'proven, but the kernel did not check the proof' : `not proven${found ? ` (${found})` : ''}`}`)
  }
}
const goalsVerdict = (goals: Goal[], checkIt = true): Verdict => {
  const trees: Record<string, Tree> = {}
  for (const g of goals) {
    const out = grow(g)
    if (!('tree' in out)) return {proven: false, checked: false, goal: g.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {}), ...(out.why ? {why: out.why} : {})}
    trees[g.name] = out.tree
  }
  return {proven: true, checked: !checkIt || goals.every(g => check(g, trees[g.name]!)), trees}
}
// The kinds' laws first, those the caller didn't pass already (by name).
const withKinds = (r: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, laws: Law[]): Law[] => [...r.kindLaws().filter(k => !laws.some(l => l.name === k.name)), ...laws]
// A real run from the start that breaks a law or a step law, from a few random runs (each request drawn by its kinds,
// those the rule's assumption refuses skipped): a false law is refused at once, with the run, where the symbolic search
// would have to decide every case of its goal to reach one. Nothing here is trusted; a run it finds is a run the
// interpreter took. A rule that reads functions is skipped: the kernel knows them only by their facts (a recurrence's
// induction machine reads the function it proves things about), so a run computing them proves nothing about the goal.
const refuteBudget = {trials: 60, depth: 6, bound: 3, ms: 150}
// The search's own runs, before it looks for what the laws need: deeper and wider, from another seed.
const deeperBudget = {trials: 600, depth: 24, bound: 8, ms: 1500, seed: 29}
function refuteByRuns(r: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, laws: Law[], stepLaws: StepLaw[] = [], budget: typeof refuteBudget & {seed?: number} = refuteBudget): {goal: string, witness: Record<string, number>, run?: {params: Record<string, number>, trace: Record<string, unknown>[]}} | undefined {
  const m = r.machine
  // Division by a constant is a function too, but its facts fix its value, so a run computing it is a run of the rule.
  if (Object.keys(m.fns ?? {}).some(f => !isArithmetic(f)) || m.facts?.some(f => !isArithmetic(f.name.slice(0, f.name.indexOf(':'))))) return undefined
  const run = interpret(m), rand = seeded(budget.seed ?? 13), until = performance.now() + budget.ms, bound = budget.bound
  const shown = (input: Request) => Object.fromEntries(Object.entries(input).map(([n, x]) => [n, typeof x === 'number' ? x : Object.fromEntries(x as ReadonlyMap<number, number>)]))
  try {
    for (let trial = 0; trial < budget.trials && performance.now() < until; trial++) {
      const params = r.randomParams(rand, bound)
      if (m.pre && !evalC(m.pre, params, {scalars: {}, maps: {}}, m)) continue
      const watching = [...laws, ...stepLaws].map(w => ({w, on: watch(m, run, w, params, bound)}))
      let st = run.init(params)
      const trace: Request[] = []
      // The witness: the params, the state the breaking step starts from (or the start) and its request's own values.
      const broken = (w: Law | StepLaw, at: string, before: State, input?: Request) =>
        ({goal: `${w.name} ${at}`, witness: {...params, ...before.scalars, ...(input ? numbersOf(input) : {})}, run: {params, trace: trace.map(shown)}})
      for (const {w, on} of watching) if (!('then' in w) && !on.start(st)) return broken(w, '@start', st)
      for (let d = 0, tries = 0; d < budget.depth && tries < 40; tries++) {
        const input = r.randomInput(rand, bound, params)
        if (!allowed(m, run, params, st, input)) continue
        d++
        const next = run.step(params, st, input)
        trace.push(input)
        for (const {w, on} of watching) if (!on.step(st, input, next)) return broken(w, !('then' in w) ? '@step' : (w.steps ?? 1) > 1 ? `@${w.steps} steps` : '@step law', st, input)
        st = next
      }
    }
    // A step law holds from every state the laws allow, reached or not: from random such states (each scalar and cell
    // small, kept when every law and kind law holds there), a step that breaks it is a counterexample too, without a run.
    // On a wide rule (32 variables or more) the laws are tried so as well, since they are proven by one step from every
    // such state (the kernel's search, when it fails, ends at one, and there that search is the slow part), and a
    // variable of a kind is drawn as its kind draws (33 yes/nos drawn from 0..7 almost never make a lawful state).
    const steps1 = stepLaws.filter(sl => (sl.steps ?? 1) === 1), given = withKinds(r, laws)
    const wide = Object.keys(m.state).length + m.inputs.length >= 32, lawsHere = wide ? given : [], kinded = wide ? r.kindsOfState() : []
    for (let trial = 0; !m.history && (steps1.length || lawsHere.length) && trial < budget.trials * 4 && performance.now() < until; trial++) {
      const params = r.randomParams(rand, bound)
      if (m.pre && !evalC(m.pre, params, {scalars: {}, maps: {}}, m)) continue
      const scalars: Record<string, number> = Object.fromEntries(Object.keys(m.state).map(n => [n, rand(8)]))
      for (const [n, k] of kinded) Object.assign(scalars, k.random(n, rand, bound))
      const st: State = {scalars, maps: Object.fromEntries(Object.keys(m.maps ?? {}).map(n => [n, new Map(Array.from({length: rand(3)}, () => [rand(bound + 1), rand(bound + 1)] as const))]))}
      if (!given.every(l => watch(m, run, l, params, bound).start(st))) continue
      const input = r.randomInput(rand, bound, params)
      if (!allowed(m, run, params, st, input)) continue
      const next = run.step(params, st, input), witness = () => ({...params, ...st.scalars, ...numbersOf(input)})
      for (const sl of steps1) if (!watch(m, run, sl, params, bound).step(st, input, next)) return {goal: `${sl.name} @step law`, witness: witness()}
      for (const l of lawsHere) if (!watch(m, run, l, params, bound).step(st, input, next)) return {goal: `${l.name} @step`, witness: witness()}
    }
  } catch { return undefined }
  return undefined
}
const refutedVerdict = (out: NonNullable<ReturnType<typeof refuteByRuns>>): Verdict => ({proven: false, checked: false, goal: out.goal, stuck: 'sat', witness: out.witness, ...(out.run ? {run: out.run} : {})})
// The divisors some laws read (modBy, divBy), noted on the rule so its machine declares them: a law may come from
// another instance of the same rule (a factory called twice).
const noting = <R extends Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>>(r: R, ...xs: object[]): R => { const ks = divisorsIn(xs as never); if (ks.size) r.dividesBy(...ks); return r }
export function proveRule(r: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, laws: Law[], opts: ProveOptions = {}): Verdict {
  noting(r, laws)
  const refuted = refuteByRuns(r, laws)
  if (refuted) return refutedVerdict(refuted)
  const out = proveLaws(r.machine, withKinds(r, laws))
  const v: Verdict = {proven: out.proven, checked: out.checked, ...(out.failed ? {goal: out.failed.goal, stuck: out.failed.stuck, ...(out.failed.witness ? {witness: out.failed.witness} : {}), ...(out.failed.why ? {why: out.failed.why} : {})} : {}), ...(out.witnesses && out.proven ? {witnesses: out.witnesses} : {})}
  return searched(r, laws, [], v, opts)
}
export function proveSteps(r: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, laws: Law[], stepLaws: StepLaw[], opts: ProveOptions = {}): Verdict {
  noting(r, laws, stepLaws)
  const refuted = refuteByRuns(r, laws, stepLaws)
  if (refuted) return refutedVerdict(refuted)
  const out = proveStepLaws(r.machine, withKinds(r, laws), stepLaws)
  const v: Verdict = {proven: out.proven, checked: out.checked, ...(out.failed ? {goal: out.failed.goal, stuck: out.failed.stuck, ...(out.failed.witness ? {witness: out.failed.witness} : {}), ...(out.failed.why ? {why: out.failed.why} : {})} : {})}
  return searched(r, laws, stepLaws, v, opts)
}
// The search, where the prover alone didn't prove the laws and nothing refuted them: the lemmas first where the rule has
// recurrences or carried lists (the rule made again with them), then invariants over what it then is. The verdict is the
// prover's on the laws with what was found; when nothing is found, the prover's own (with why).
function searched(r: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, laws: Law[], stepLaws: StepLaw[], v: Verdict, opts: ProveOptions): Verdict {
  if ((v.proven && v.checked) || opts.search === false || v.run || v.stuck === 'sat' && !/@step|@\d+ steps/.test(v.goal ?? '')) return v
  const deeper = refuteByRuns(r, laws, stepLaws, deeperBudget)
  if (deeper?.run) return refutedVerdict(deeper)
  const until = performance.now() + (typeof opts.search === 'object' && opts.search.ms !== undefined ? opts.search.ms : 10_000)
  let rule = r, lemmas: Found['lemmas']
  const {fns, lists} = r.parts
  if (lists.length || fns.some(([, d]) => recurOf(d))) {
    const d = withDeadline(until, () => discover(r, laws, stepLaws, v))
    if (d.verdict.proven && d.verdict.checked) return {...d.verdict, found: {lemmas: d.found}}
    if (Object.keys(d.found).length) (rule = d.rule, lemmas = d.found)
  }
  // Functions known by their facts alone (not a recurrence): lemmas about them, fitted to their values and proven from
  // the facts as cyclic claims, the laws proven with them as facts.
  if ((typeof opts.search !== 'object' || opts.search.cycles !== false) && fns.some(([, d]) => !recurOf(d)) && rule.machine.facts?.length && until - performance.now() > 500) {
    const c = withDeadline(until, () => cycleLemmas(rule.machine, withKinds(rule, laws), stepLaws, {ms: (until - performance.now()) / 2}))
    if (c.proven && c.checked) return {proven: true, checked: true, found: {...(lemmas ? {lemmas} : {}), facts: c.found.map(f => f.text)}}
  }
  const ms = until - performance.now()
  if (ms < 500) return v
  const inf = inferLaws(rule, laws, stepLaws, {ms, ...(rule === r ? {first: v} : {})})
  if (!(inf.proven && inf.checked)) return {...v, why: [v.why, `the search found nothing that proves it in ${Math.round(inf.stats.ms)} ms`].filter(Boolean).join('; ')}
  const {found, stats: _stats, ...verdict} = inf
  void _stats
  return {...verdict, found: {laws: found, ...(lemmas ? {lemmas} : {})}}
}
export type {StepLaw}
export type {Liveness}
export function proveLeadsTo(r: Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>, laws: Law[], l: Liveness, opts: {ms?: number} = {}): Verdict {
  noting(r, laws, l)
  if (laws.some(law => law.some?.length)) throw new Error(`${r.machine.name}: a law with "there exists" goes to proveRule or proveSteps; a liveness takes plain laws (the ones its proof printed, Verdict.witnesses)`)
  if (Array.isArray(l.rank) && !l.rank.length) {
    const f = findLeadsTo(r.machine, withKinds(r, laws), l, {params: (rand, bound) => r.randomParams(rand, bound), input: (rand, bound, ps) => r.randomInput(rand, bound, ps)}, opts)
    return {proven: f.proven, checked: f.checked, ...(f.goal ? {goal: f.goal, stuck: f.stuck} : {}), ...(f.witness ? {witness: f.witness} : {}), ...(f.why ? {why: f.why} : {}),
      ...(f.found ? {found: {rank: f.found.rank, ...(f.laws?.length ? {laws: f.laws.map((law, i) => ({law, text: f.found!.laws[i] ?? law.name}))} : {})}} : {})}
  }
  const out = proveLiveness(r.machine, withKinds(r, laws), l)
  return {proven: out.proven, checked: out.checked, ...(out.failed ? {goal: out.failed.goal, stuck: out.failed.stuck, ...(out.failed.witness ? {witness: out.failed.witness} : {}), ...(out.failed.why ? {why: out.failed.why} : {})} : {})}
}
export const proveDecision = (d: Decision): Verdict => (d.steps ? proveSteps(d.steps.rule as never, [], [d.steps.law], {search: false}) : goalsVerdict([d.goal]))
const seeded = (seed: number): Rand => { let x = seed; return k => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) } }
// A decision's callbacks against its condition, on random params and requests: `given` and `then` each run with every
// value known, against what the interpreter evaluates of the decision built from them.
export function crossCheckDecision(d: Decision, opts: {trials?: number, bound?: number, rand?: Rand} = {}): {checked: number, failure?: string} {
  const src = sources.get(d)?.decision
  if (!src) return {checked: 0}
  const r = d.rule, m = r.machine, bound = opts.bound ?? 4, rand = opts.rand ?? seeded(11), own = d.given.slice(d.given.length - src.own)
  let checked = 0
  for (let i = 0; i < (opts.trials ?? 500); i++) {
    const ps = r.randomParams(rand, bound), input = r.randomInput(rand, bound, ps), values = {...ps, ...numbersOf(input)}
    // a map a request carries reads 0 past its cells (a list's encoding keeps no 0 cell)
    const carried = Object.entries(input).filter((e): e is [string, ReadonlyMap<number, number>] => typeof e[1] !== 'number')
    const st: State = {scalars: {}, maps: Object.fromEntries(carried.map(([n, cells]) => [n, new Map(cells)])), defaults: Object.fromEntries(carried.map(([n]) => [n, 0]))}
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
// With no rank stated, the rank is searched for from the loop's runs (core/cycles.ts's findRank), with the invariants it
// needs (inferLaws), within `ms` (10 s); the verdict is the kernel's on the rank and the laws found, in `found`.
// The certificate, by default, is the cyclic proof of its halting goals (kernel/prove.ts's certLoop, translated from the
// usual trees, which are then its input and not checked again); where none is made, the usual trees, checked.
export const proveLoop = (l: LoopRule<Obj, Obj, Obj>, laws: Law[], opts: {ms?: number} = {}): Verdict => {
  if (l.hasRank) {
    const t0 = performance.now(), goals = loopObligations(l.loop, laws, l.rankTerms), v = goalsVerdict(goals, !certOn())
    if (!v.proven) return v
    const c = certLoop(l.loop, laws, l.rankTerms, v.trees!, performance.now() - t0)
    return c && !c.checked && certOn() ? {...v, checked: goals.every(g => check(g, v.trees![g.name]!))} : v
  }
  const t0 = performance.now(), out = findRank(l.loop, laws, opts)
  if (out.proven && out.checked && out.rank && out.trees) certLoop(l.loop, [...laws, ...(out.laws ?? [])], out.rank, out.trees, performance.now() - t0)
  return {proven: out.proven, checked: out.checked, ...(out.trees ? {trees: out.trees} : {}), ...(out.goal ? {goal: out.goal, stuck: out.stuck} : {}), ...(out.witness ? {witness: out.witness} : {}), ...(out.why ? {why: out.why} : {}),
    ...(out.found ? {found: {rank: out.found.rank, ...(out.laws?.length ? {laws: out.laws.map((law, i) => ({law, text: out.found!.laws[i] ?? law.name}))} : {})}} : {})}
}

// --- folds over trees ---------------------------------------------------------------------------------------------------

// A tree as a runtime value: a leaf with its inputs, or a node with its own inputs and two subtrees.
export type TreeValue<I> = {leaf: I} | {node: I, left: TreeValue<I>, right: TreeValue<I>}
// A fold over binary trees (the kernel's Fold, proven by Kern.fold_sound in Lean): each leaf's values from its inputs and
// the params, each node's from its own inputs, the params and its two children's values. A law about the values holds
// of every tree when it holds at every leaf and at every node whose children meet it: induction over the tree, which
// the kernel checks as two goals and Lean again.
//   const rollup = fold('spend roll-up').params({cap: nat}).inputs({c: nat})
//     .leaf(({c, cap}) => ({spend: min(c, cap), count: 1}))
//     .node(({c, cap}, l, r) => ({spend: l.spend.plus(r.spend).plus(min(c, cap)), count: l.count.plus(r.count).plus(1)}))
//   proveFold(rollup, [rollup.law('within the cap', ({spend, count, cap}) => spend.atMost(count.mul(cap)))])
type FoldSpec = {name: string, params: [string, Kind<unknown>][], inputs: [string, Kind<unknown>][], pre: ((p: never) => Cond)[], assume: ((env: never) => Cond)[],
  leaf?: (env: never) => Record<string, TermLike>, node?: (env: never, left: never, right: never) => Record<string, TermLike>}
export class FoldRule<P extends Obj = {}, I extends Obj = {}, S extends Obj = {}> {
  constructor(private readonly spec: FoldSpec) {}
  private with(more: Partial<FoldSpec>): never { return new FoldRule({...this.spec, ...more}) as never }
  get name() { return this.spec.name }
  params<K extends Kinds>(kinds: K): FoldRule<P & ValuesOf<K>, I, S> { return this.with({params: [...this.spec.params, ...Object.entries(kinds)]}) }
  inputs<K extends Kinds>(kinds: K): FoldRule<P, I & ValuesOf<K>, S> { return this.with({inputs: [...this.spec.inputs, ...Object.entries(kinds)]}) }
  pre(f: (p: P) => Cond): FoldRule<P, I, S> { return this.with({pre: [...this.spec.pre, f as (p: never) => Cond]}) }
  // What every leaf's and node's inputs satisfy (with their kinds' own assumptions).
  assume(f: (env: P & I) => Cond): FoldRule<P, I, S> { return this.with({assume: [...this.spec.assume, f as (env: never) => Cond]}) }
  leaf<T extends Record<string, TermLike>>(f: (env: P & I) => T): FoldRule<P, I, {[k in keyof T]: Term}> { return this.with({leaf: f as never}) }
  node(f: (env: P & I, left: S, right: S) => {[k in keyof S]: TermLike}): FoldRule<P, I, S> { return this.with({node: f as never}) }
  // Nodes with any number of children (RoseFold): the children's values folded into `kids`, from `from` by `step` (which
  // reads the params), each lemma a law of every prefix of every node's children that meet the fold's laws.
  children<A extends Record<string, number | ((p: P) => TermLike)>>(from: A, step: (acc: {[k in keyof A]: Term}, kid: S, p: P) => {[k in keyof A]: TermLike},
    lemmas: Record<string, (acc: {[k in keyof A]: Term}, p: P) => Cond> = {}): RoseFold<P, I, S, {[k in keyof A]: Term}> {
    return new RoseFold(this.spec, {from: from as never, step: step as never, lemmas: lemmas as never})
  }
  private env(inputs = true): Record<string, unknown> {
    const out: Record<string, unknown> = {}
    for (const [n, k] of this.spec.params) out[n] = k.value(n)
    if (inputs) for (const [n, k] of this.spec.inputs) out[n] = k.value(n)
    return out
  }
  private names(): string[] {
    if (!this.spec.leaf) throw new Error(`${this.spec.name}: a fold needs a leaf`)
    return Object.keys(this.spec.leaf(this.env() as never))
  }
  private side(prefix: string): Record<string, Term> { return Object.fromEntries(this.names().map(n => [n, v(`${prefix}${n}`)])) }
  // A law about the values (and the params): it reads no input.
  law(name: string, f: (env: P & S) => Cond): Law { return {name, holds: f({...this.env(false), ...this.side('')} as never).c} }
  get fold(): Fold {
    const s = this.spec
    if (!s.leaf || !s.node) throw new Error(`${s.name}: a fold needs a leaf and a node`)
    const env = this.env(), pEnv = this.env(false)
    const pre = [...s.params.flatMap(([n, k]) => k.assume(n)).map(c => c.c), ...s.pre.map(f => f(pEnv as never).c)]
    const assume = [...s.inputs.flatMap(([n, k]) => k.assume(n)).map(c => c.c), ...s.assume.map(f => f(env as never).c)]
    const terms = (r: Record<string, TermLike>) => Object.fromEntries(Object.entries(r).map(([n, t]) => [n, termOf(t)]))
    const leaf = terms(s.leaf(env as never)), node = terms(s.node(env as never, this.side('l_') as never, this.side('r_') as never))
    return {name: s.name, params: s.params.flatMap(([n, k]) => k.vars(n)), inputs: s.inputs.flatMap(([n, k]) => k.vars(n)), leaf, node,
      ...(pre.length ? {pre: pre.length === 1 ? pre[0]! : {op: 'and', xs: pre}} : {}), ...(assume.length ? {assume: assume.length === 1 ? assume[0]! : {op: 'and', xs: assume}} : {})}
  }
  // The values of a tree, by the terms that were proven (each leaf's and node's inputs as their kinds encode them; one
  // that doesn't meet `assume` is refused, as the laws are claimed only of trees that meet it).
  run(tree: TreeValue<{[k in keyof I]: Raw}>, params: {[k in keyof P]?: Raw} = {}): {[k in keyof S]: number} {
    const f = this.fold, ps = encode(this.spec.params, params as Record<string, Raw>), none: Machine = {name: f.name, params: [], inputs: [], state: {}, step: {}}
    const st: State = {scalars: {}, maps: {}}
    if (f.pre && !evalC(f.pre, ps, st, none)) throw new RangeError(`${f.name}: the params don't meet its precondition`)
    const go = (t: TreeValue<Record<string, Raw>>): Record<string, number> => {
      const own = 'leaf' in t ? t.leaf : t.node, env: Record<string, number> = {...ps, ...encode(this.spec.inputs, own)}
      if (f.assume && !evalC(f.assume, env, st, none)) throw new RangeError(`${f.name}: ${JSON.stringify(own)} doesn't meet its assumption`)
      if ('leaf' in t) return Object.fromEntries(Object.entries(f.leaf).map(([n, e]) => [n, evalE(e, env, st, none)]))
      const l = go(t.left), r = go(t.right)
      const both = {...env, ...Object.fromEntries(Object.entries(l).map(([n, x]) => [`l_${n}`, x])), ...Object.fromEntries(Object.entries(r).map(([n, x]) => [`r_${n}`, x]))}
      return Object.fromEntries(Object.entries(f.node).map(([n, e]) => [n, evalE(e, both, st, none)]))
    }
    return go(tree as TreeValue<Record<string, Raw>>) as never
  }
  // The builders against what they built, on random trees: each value by the callbacks' own arithmetic against the
  // terms the kernel proved (as run evaluates them), and each law's callback against its condition.
  crossCheck(laws: Law[] = [], opts: {trials?: number, depth?: number, bound?: number, rand?: Rand} = {}): Agreement {
    const s = this.spec, rand = opts.rand ?? seeded(13), bound = opts.bound ?? 6, f = this.fold
    let checked = 0
    const sample = (kinds: [string, Kind<unknown>][]) => Object.fromEntries(kinds.map(([n, k]) => [n, k.sample(rand, bound)]))
    const tree = (d: number): TreeValue<Record<string, Raw>> => (d === 0 || rand(3) === 0 ? {leaf: sample(s.inputs)} : {node: sample(s.inputs), left: tree(d - 1), right: tree(d - 1)})
    const known = (vals: Record<string, number>) => Object.fromEntries(Object.entries(vals).map(([n, x]) => [n, new Term({op: 'const', value: x}, x)]))
    for (let t = 0; t < (opts.trials ?? 200); t++) {
      const params = sample(s.params), ps = encode(s.params, params)
      const pv = known(ps), pEnv = Object.fromEntries(s.params.map(([n, k]) => [n, k.build(n, part => pv[part]!)]))
      const builder = (tr: TreeValue<Record<string, Raw>>): Record<string, number> | undefined => {
        const own = 'leaf' in tr ? tr.leaf : tr.node, iv = known(encode(s.inputs, own)), env = {...pEnv, ...Object.fromEntries(s.inputs.map(([n, k]) => [n, k.build(n, part => iv[part]!)]))}
        const out = 'leaf' in tr ? s.leaf!(env as never) : (() => { const l = builder(tr.left), r = builder(tr.right); return l && r ? s.node!(env as never, known(l) as never, known(r) as never) : undefined })()
        if (!out) return undefined
        const vals = Object.entries(out).map(([n, x]) => [n, valOf(x)] as const)
        return vals.every(([, x]) => x !== undefined) ? Object.fromEntries(vals) as Record<string, number> : undefined
      }
      const tr = tree(opts.depth ?? 3)
      let ours: Record<string, number>
      try { ours = this.run(tr as never, params as never) } catch { continue }
      const theirs = builder(tr)
      if (!theirs) continue
      for (const [n, x] of Object.entries(theirs)) { checked++; if (ours[n] !== x) return {checked, failure: `${f.name}: ${n} is ${x} by its callbacks, ${ours[n]} by the terms proven, for ${JSON.stringify(tr)}`} }
      for (const law of laws) {
        const ok = evalC(law.holds, {...ps, ...ours}, {scalars: {}, maps: {}}, {name: f.name, params: [], inputs: [], state: {}, step: {}})
        checked++
        if (!ok) return {checked, failure: `${f.name}: law ${law.name} fails for ${JSON.stringify(tr)} with params ${JSON.stringify(params)}`}
      }
    }
    return {checked}
  }
}
export const fold = (name: string): FoldRule => new FoldRule({name, params: [], inputs: [], pre: [], assume: []})
// A fold's laws proven over every tree (a rose fold's own laws, its children's lemmas, with them).
export const proveFold = (f: {fold: Fold, lemmas?: Law[]}, laws: Law[]): Verdict => {
  // (by default the certificate a cyclic proof, core/cyclic.ts's certCyclic, the usual trees its input; where none is
  // made, the usual trees checked)
  const all = [...(f.lemmas ?? []), ...laws], t0 = performance.now(), v = goalsVerdict(foldObligations(f.fold, all), !certOn()), usualMs = performance.now() - t0
  if (cyclicOn()) crossCyclic('fold', f.fold.name, v.proven && v.checked, () => { const {facts, specs} = foldNodes(f.fold, all); return proveCyclic(facts, specs) }, usualMs,
    v.trees && (st => translatedProof(() => JSON.stringify(['fold', f.fold, all]), () => foldNodes(f.fold, all, v.trees, st), st)))
  if (certOn() && v.proven) {
    const c = certCyclic('fold', f.fold.name, v.trees && (st => translatedProof(() => JSON.stringify(['fold', f.fold, all]), () => foldNodes(f.fold, all, v.trees, st), st)), () => { const {facts, specs} = foldNodes(f.fold, all); return proveCyclic(facts, specs) }, usualMs)
    if (!c.checked) { uncovered('fold', f.fold.name, c.why); v.checked = foldObligations(f.fold, all).every(g => v.trees?.[g.name] !== undefined && check(g, v.trees[g.name]!)) }
  }
  return v
}

const asTerm = (t: TermLike): Term => (t instanceof Term ? t : lit(t))
// A tree whose nodes have any number of children, as a runtime value.
export type RoseValue<I> = {leaf: I} | {node: I, children: RoseValue<I>[]}
type RoseSpec = {from: Record<string, number | ((p: never) => TermLike)>, step: (acc: never, kid: never, p: never) => Record<string, TermLike>, lemmas: Record<string, (acc: never, p: never) => Cond>}
// A fold over trees whose nodes have any number of children, as the kernel's binary fold (so the kernel and Lean's
// fold_sound check it as they check any fold): a node's children become a chain of glue nodes, each folding one child
// into the values of the rest (`kids`, from `from` at the chain's end), and the node reads the chain's values. Every
// tree node carries `kind$` (0 a node or leaf of the tree, 1 a glue node or the chain's end) and its role as an input; a
// law of the fold is claimed where kind$ is 0, each lemma where it is 1. A binary tree no rose tree maps to (a child
// where a chain belongs, or a chain where a child does) is read as one that does: a node reads a chain only, a glue
// node a child only, so the laws are proven of every binary tree, and of each rose tree's image in particular.
//   fold('org chart').params({cap: nat}).inputs({pay: nat})
//     .leaf(({pay}) => ({cost: pay, heads: 1}))
//     .children({cost: 0, heads: 0}, (acc, kid) => ({cost: acc.cost.plus(kid.cost), heads: acc.heads.plus(kid.heads)}))
//     .node(({pay}, kids) => ({cost: kids.cost.plus(pay), heads: kids.heads.plus(1)}))
export class RoseFold<P extends Obj = {}, I extends Obj = {}, S extends Obj = {}, A extends Obj = {}> {
  constructor(private readonly spec: FoldSpec, private readonly kids: RoseSpec, private readonly nodeOf?: (env: never, kids: never) => Record<string, TermLike>) {}
  get name() { return this.spec.name }
  node(f: (env: P & I, kids: A) => {[k in keyof S]: TermLike}): RoseFold<P, I, S, A> { return new RoseFold(this.spec, this.kids, f as never) }
  private env(inputs = true): Record<string, unknown> {
    const out: Record<string, unknown> = {}
    for (const [n, k] of this.spec.params) out[n] = k.value(n)
    if (inputs) for (const [n, k] of this.spec.inputs) out[n] = k.value(n)
    return out
  }
  private names(): string[] {
    if (!this.spec.leaf) throw new Error(`${this.spec.name}: a fold needs a leaf`)
    return Object.keys(this.spec.leaf(this.env() as never))
  }
  private side(prefix: string): Record<string, Term> { return Object.fromEntries(this.names().map(n => [n, v(`${prefix}${n}`)])) }
  private accs(prefix: string): Record<string, Term> { return Object.fromEntries(Object.keys(this.kids.from).map(a => [a, v(`${prefix}kids$${a}`)])) }
  private start(p: Record<string, unknown>): Record<string, Term> { return Object.fromEntries(Object.entries(this.kids.from).map(([a, x]) => [a, typeof x === 'number' ? lit(x) : asTerm(x(p as never))])) }
  // A law about the values and the params, claimed of every node and leaf of the tree.
  law(name: string, f: (env: P & S) => Cond): Law { return {name, holds: v('kind$').atLeast(1).or(f({...this.env(false), ...this.side('')} as never)).c} }
  // The children's lemmas (claimed of every glue node), and that kind$ is 0 or 1: proveFold adds them.
  get lemmas(): Law[] {
    const p = this.env(false)
    return [{name: `${this.spec.name}: kind$ is 0 or 1`, holds: v('kind$').atMost(1).c},
      ...Object.entries(this.kids.lemmas).map(([n, l]) => ({name: n, holds: v('kind$').eq(0).or(l(this.accs('') as never, p as never)).c}))]
  }
  get fold(): Fold {
    const s = this.spec, node = this.nodeOf
    if (!s.leaf || !node) throw new Error(`${s.name}: a fold needs a leaf and a node`)
    const env = this.env(), pEnv = this.env(false), names = this.names(), accNames = Object.keys(this.kids.from)
    const role = v('role$'), real = role.eq(0)
    const pre = [...s.params.flatMap(([n, k]) => k.assume(n)).map(c => c.c), ...s.pre.map(f => f(pEnv as never).c)]
    const own = all(...s.inputs.flatMap(([n, k]) => k.assume(n)), ...s.assume.map(f => f(env as never)))
    const assume = role.atMost(1).and(role.eq(1).or(own)).c
    const start = this.start(pEnv)
    // A leaf of the tree, or the end of a chain (no children yet).
    const leafOut = s.leaf(env as never)
    const leaf: Record<string, E> = {...Object.fromEntries(names.map(n => [n, when(real, leafOut[n]!, 0).e])),
      ...Object.fromEntries(accNames.map(a => [`kids$${a}`, when(real, 0, start[a]!).e])), 'kind$': when(real, 0, 1).e}
    // A node reads the chain on its left (its children's values); a glue node folds its left child into the rest.
    const lAcc = this.accs('l_'), rAcc = this.accs('r_'), lk = v('l_kind$'), rk = v('r_kind$')
    const kidsIn = Object.fromEntries(accNames.map(a => [a, when(lk.eq(1), lAcc[a]!, start[a]!)]))
    const rest = Object.fromEntries(accNames.map(a => [a, when(rk.eq(1), rAcc[a]!, start[a]!)]))
    const nodeOut = node(env as never, kidsIn as never), stepped = this.kids.step(rest as never, this.side('l_') as never, pEnv as never)
    const nodeE: Record<string, E> = {...Object.fromEntries(names.map(n => [n, when(real, nodeOut[n]!, 0).e])),
      ...Object.fromEntries(accNames.map(a => [`kids$${a}`, when(real, 0, when(lk.eq(0), stepped[a]!, rest[a]!)).e])), 'kind$': when(real, 0, 1).e}
    return {name: s.name, params: s.params.flatMap(([n, k]) => k.vars(n)), inputs: [...s.inputs.flatMap(([n, k]) => k.vars(n)), 'role$'], leaf, node: nodeE,
      ...(pre.length ? {pre: pre.length === 1 ? pre[0]! : {op: 'and', xs: pre}} : {}), assume}
  }
  // The values of a rose tree, by the terms proven (the tree as the binary tree the fold reads it as).
  run(tree: RoseValue<{[k in keyof I]: Raw}>, params: {[k in keyof P]?: Raw} = {}): {[k in keyof S]: number} {
    const f = this.fold, ps = encode(this.spec.params, params as Record<string, Raw>), none: Machine = {name: f.name, params: [], inputs: [], state: {}, step: {}}
    const st: State = {scalars: {}, maps: {}}
    if (f.pre && !evalC(f.pre, ps, st, none)) throw new RangeError(`${f.name}: the params don't meet its precondition`)
    const zero = Object.fromEntries(f.inputs.map(n => [n, 0]))
    const at = (exprs: Record<string, E>, env: Record<string, number>) => Object.fromEntries(Object.entries(exprs).map(([n, e]) => [n, evalE(e, env, st, none)]))
    const kidsOf = (vals: Record<string, number>, prefix: string) => Object.fromEntries(Object.entries(vals).map(([n, x]) => [`${prefix}${n}`, x]))
    const chain = (cs: RoseValue<Record<string, Raw>>[]): Record<string, number> => {
      const env = {...ps, ...zero, 'role$': 1}
      if (!cs.length) return at(f.leaf, env)
      return at(f.node, {...env, ...kidsOf(go(cs[0]!), 'l_'), ...kidsOf(chain(cs.slice(1)), 'r_')})
    }
    const go = (t: RoseValue<Record<string, Raw>>): Record<string, number> => {
      const own = 'leaf' in t ? t.leaf : t.node, env: Record<string, number> = {...ps, ...encode(this.spec.inputs, own), 'role$': 0}
      if (f.assume && !evalC(f.assume, env, st, none)) throw new RangeError(`${f.name}: ${JSON.stringify(own)} doesn't meet its assumption`)
      if ('leaf' in t) return at(f.leaf, env)
      return at(f.node, {...env, ...kidsOf(chain(t.children), 'l_'), ...kidsOf(chain([]), 'r_')})
    }
    const out = go(tree as RoseValue<Record<string, Raw>>)
    return Object.fromEntries(this.names().map(n => [n, out[n]!])) as never
  }
  // The builders against what they built, on random rose trees: each value by the callbacks' own arithmetic (the
  // children folded by step, then the node) against the terms proven, and each law and lemma at the root.
  crossCheck(laws: Law[] = [], opts: {trials?: number, depth?: number, bound?: number, rand?: Rand} = {}): Agreement {
    const s = this.spec, rand = opts.rand ?? seeded(17), bound = opts.bound ?? 6, f = this.fold
    let checked = 0
    const sample = (kinds: [string, Kind<unknown>][]) => Object.fromEntries(kinds.map(([n, k]) => [n, k.sample(rand, bound)]))
    const tree = (d: number): RoseValue<Record<string, Raw>> => (d === 0 || rand(3) === 0 ? {leaf: sample(s.inputs)} : {node: sample(s.inputs), children: Array.from({length: rand(4)}, () => tree(d - 1))})
    const known = (vals: Record<string, number>) => Object.fromEntries(Object.entries(vals).map(([n, x]) => [n, new Term({op: 'const', value: x}, x)]))
    const nums = (out: Record<string, TermLike>) => { const vals = Object.entries(out).map(([n, x]) => [n, valOf(x)] as const); return vals.every(([, x]) => x !== undefined) ? Object.fromEntries(vals) as Record<string, number> : undefined }
    for (let t = 0; t < (opts.trials ?? 200); t++) {
      const params = sample(s.params), ps = encode(s.params, params)
      const pv = known(ps), pEnv = Object.fromEntries(s.params.map(([n, k]) => [n, k.build(n, part => pv[part]!)]))
      const builder = (tr: RoseValue<Record<string, Raw>>): Record<string, number> | undefined => {
        const own = 'leaf' in tr ? tr.leaf : tr.node, iv = known(encode(s.inputs, own)), env = {...pEnv, ...Object.fromEntries(s.inputs.map(([n, k]) => [n, k.build(n, part => iv[part]!)]))}
        if ('leaf' in tr) return nums(s.leaf!(env as never))
        let acc: Record<string, number> | undefined = nums(this.start(pEnv))
        for (const c of [...tr.children].reverse()) { const kid = builder(c); acc = acc && kid && nums(this.kids.step(known(acc) as never, known(kid) as never, pEnv as never)) }
        return acc && nums(this.nodeOf!(env as never, known(acc) as never))
      }
      const tr = tree(opts.depth ?? 3)
      let ours: Record<string, number>
      try { ours = this.run(tr as never, params as never) } catch { continue }
      const theirs = builder(tr)
      if (!theirs) continue
      for (const [n, x] of Object.entries(theirs)) { checked++; if (ours[n] !== x) return {checked, failure: `${f.name}: ${n} is ${x} by its callbacks, ${ours[n]} by the terms proven, for ${JSON.stringify(tr)}`} }
      for (const law of laws) {
        checked++
        if (!evalC(law.holds, {...ps, ...ours, 'kind$': 0}, {scalars: {}, maps: {}}, {name: f.name, params: [], inputs: [], state: {}, step: {}})) return {checked, failure: `${f.name}: law ${law.name} fails for ${JSON.stringify(tr)} with params ${JSON.stringify(params)}`}
      }
    }
    return {checked}
  }
}

// Statecharts (core/chart.ts): states nested and in parallel regions, compiled to a rule.
export {Chart, chart, type StateNode, type Transition} from './chart.ts'
