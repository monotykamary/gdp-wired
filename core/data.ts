// Recursive datatypes as values, proven by cyclic proofs. Untrusted: this file states facts and nodes, kernel/prove.ts
// grows a tree for every goal, and kernel/cyclic.ts checks the whole, as for every cyclic proof (nothing here is new to
// the kernel). Lean's twin of a proof (lean-kernel/Data.lean and the export's own definitions) is about the datatype as
// declared: a Lean `inductive`, the functions by pattern matching, the law over them.
//
// The encoding: every natural is a value of every datatype (a bijection between the naturals and the datatype's values,
// which Lean's twin defines and proves), so a value is a natural and two values are equal exactly when they are the same
// natural. A datatype D is read through maps: `D.tag[x]` (which constructor), `D.<ctor>.<field>[x]` (its fields, 0 under
// another constructor), `D.size[x]` (1 plus the sizes of its fields of D's group: the rank). A field is a natural, a value
// of D, of another datatype of D's group (declared together: a rose tree and its forest), or of one declared before (a
// list of lists); every datatype has its own codes. A constructor of no field is
// the constant of its tag; one with fields is a map read at its fields (`D.<ctor>[key]`); a function is a map read at
// its arguments; several arguments are read at their pairing, left-nested (a + b)² + b, as the library reads a function
// of several arguments (core/dsl.ts's argsKey). The facts, each at every value of its keys:
//   - the shape: D.tag[x] is a constructor's tag, and under tag j, D.size[x] = 1 + the sizes of x's fields of type D,
//     and the fields of every other constructor 0
//   - eta: under tag j, x is constructor j at its own fields (every natural is a value)
//   - each constructor: D.tag[C[key]] = j and each field of C[key] is its argument
//   - each function: f[key] = its body, a match read as ifs on the tag, a field bound by a case read from its map
//   - congruence of each map read at a pairing: equal arguments, equal cells (the kernel compares a pairing's
//     monomials, not its arguments)
// A law is a node at rank (level, D.size[x]) for an argument x; its uses read it at x's fields (structural induction),
// or at the arguments of a function's own recursive calls (recursion induction, other arguments changing with them; on a
// natural n, at n − 1, its rank n), each where the tag is the case's. On a datatype of a group, the law has a companion
// for each other datatype x's fields reach (the law lifted through each function's own call at such a field), each node
// using the others at the fields of their datatypes (mutual induction). Lemmas the law needs are found by the values
// (theory exploration: equations between terms the random values agree on, then the shapes of a predicate kept), proven
// the same way at lower levels, and used at the terms of the law they match.
import type {C, E} from './machine.ts'
import {type Fact} from '../kernel/cyclic.ts'
import {substC, substE} from '../kernel/kernel.ts'
import {type CyclicVerdict, type NodeSpec, proveCyclic} from './cyclic.ts'
import {clock, counted, pairedKeys, withDeadline} from '../kernel/prove.ts'
import {work} from './solver.ts'
import {ranksOfRuns} from './cycles.ts'
import {proveThrough, transferPlan} from './transfer.ts'

// --- sorts and the AST ------------------------------------------------------------------------------------------------

export const self = {self: true} as const
export const natural = 'nat' as const
export const boolean = 'bool' as const
// A signed integer (Lean's Int): opt-in, beside the naturals, whose truncated subtraction keeps its meaning. Encoded as
// its zigzag code (z ↦ 2z for z ≥ 0, −2z − 1 below), a bijection with the naturals like a datatype's, so a value is one
// natural and two values are equal exactly when their codes are; its arithmetic reads a code as two naturals, p − n
// (from the code's quotient and remainder by 2), and writes the result's code back (`encI`, `codeOfPair`).
export const integer = 'int' as const
// A field is a natural, an integer or a value of a datatype: the datatype itself, another of its group (declared with
// it by `mutual`), or one declared before it (a list of lists, say).
export type FieldSort = 'nat' | 'int' | {data: string}
export type Sort = 'nat' | 'bool' | 'int' | Data
export const isDataField = (s: FieldSort): s is {data: string} => typeof s === 'object'
export type Ctor = {name: string, fields: {name: string, sort: FieldSort}[]}

// Terms: naturals, conditions as values (0 or 1), datatype values; `match` binds a case's fields by name.
export type X =
  | {op: 'var', name: string}
  | {op: 'nat', value: number}
  | {op: 'add' | 'sub' | 'min' | 'max', a: X, b: X}
  | {op: 'mul', k: number, a: X}
  | {op: 'prod', a: X, b: X} // a product of two naturals
  | {op: 'mod' | 'div', k: number, a: X} // a natural's remainder and quotient by a constant k >= 1
  // integers: a literal, sums, differences, negation, a constant multiple (any sign), a natural as an integer, and
  // Euclid's quotient and remainder by a constant k >= 1 (0 <= x mod k < k, as SMT-LIB and Lean's Int / and % read them)
  | {op: 'int', value: number}
  | {op: 'iadd' | 'isub', a: X, b: X}
  | {op: 'ineg', a: X}
  | {op: 'imul', k: number, a: X}
  | {op: 'ofnat', a: X}
  | {op: 'imod' | 'idiv', k: number, a: X}
  | {op: 'if', c: Y, then: X, else: X}
  | {op: 'call', fn: string, args: X[]}
  | {op: 'ctor', data: string, ctor: number, args: X[]}
  | {op: 'match', data: string, of: X, cases: {binds: string[], body: X}[]}
  | {op: 'natmatch', of: X, zero: X, pred: string, succ: X}
  | {op: 'apply', param: string, arg: X}
  | {op: 'bool', c: Y}
  // A value's size (1 plus the sizes of its fields of its datatype's group): what a measure reads
  | {op: 'size', data: string, of: X}
export type Y =
  | {op: '<' | '<=' | '=', a: X, b: X}
  | {op: 'i<' | 'i<=', a: X, b: X} // integers compared by value ('=' compares codes, which is the same)
  | {op: 'and' | 'or', xs: Y[]}
  | {op: 'not', x: Y}
  | {op: 'is', data: string, of: X, ctor: number}
  | {op: 'holds', x: X}

// --- the surface ------------------------------------------------------------------------------------------------------

let fresh = 0
export const bindName = (field: string) => `${field}#${++fresh}`

export class Nat {
  constructor(readonly x: X) {}
  plus(b: NatLike): Nat { return new Nat({op: 'add', a: this.x, b: natX(b)}) }
  minus(b: NatLike): Nat { return new Nat({op: 'sub', a: this.x, b: natX(b)}) }
  times(k: number): Nat { return new Nat({op: 'mul', k, a: this.x}) }
  // A product of two naturals (the kernel multiplies it out; nonlinear: what proves it is products of facts and squares).
  mul(b: NatLike): Nat { return new Nat({op: 'prod', a: this.x, b: natX(b)}) }
  modBy(k: number): Nat { return new Nat({op: 'mod', k: divisorOf(k), a: this.x}) }
  divBy(k: number): Nat { return new Nat({op: 'div', k: divisorOf(k), a: this.x}) }
  toInt(): Integer { return new Integer({op: 'ofnat', a: this.x}) }
  lt(b: NatLike): Bool { return new Bool({op: '<', a: this.x, b: natX(b)}) }
  atMost(b: NatLike): Bool { return new Bool({op: '<=', a: this.x, b: natX(b)}) }
  gt(b: NatLike): Bool { return new Bool({op: '<', a: natX(b), b: this.x}) }
  atLeast(b: NatLike): Bool { return new Bool({op: '<=', a: natX(b), b: this.x}) }
  eq(b: NatLike): Bool { return new Bool({op: '=', a: this.x, b: natX(b)}) }
  ne(b: NatLike): Bool { return this.eq(b).not() }
  // A natural as 0 or the successor of another (`pred`): recursion on a natural passes `pred` where this is a parameter.
  // oxlint-disable-next-line typescript/no-explicit-any
  match(cases: {zero: () => Nat | Bool | Val | Integer | number, succ: (f: {pred: Nat}) => Nat | Bool | Val | Integer | number}): any {
    const pred = bindName('pred'), zero = cases.zero(), succ = cases.succ({pred: new Nat({op: 'var', name: pred})})
    const int = zero instanceof Integer || succ instanceof Integer
    const body = (o: unknown): X => (typeof o === 'number' ? (int ? intX(o) : natX(o)) : o instanceof Bool ? {op: 'bool', c: o.y} : (o as Nat | Val).x)
    const x: X = {op: 'natmatch', of: this.x, zero: body(zero), pred, succ: body(succ)}
    return (zero instanceof Bool ? new Bool({op: 'holds', x}) : zero instanceof Val ? new Val(zero.data, x) : int ? new Integer(x) : new Nat(x)) as never
  }
}
export type NatLike = Nat | number
const natX = (t: NatLike): X => (typeof t === 'number' ? {op: 'nat', value: t} : t.x)
const divisorOf = (k: number): number => { if (!Number.isSafeInteger(k) || k < 1) throw new RangeError(`a divisor is a whole number at least 1, not ${k}`); return k }
// An integer's term; a number is a literal (any sign).
export class Integer {
  constructor(readonly x: X) {}
  plus(b: IntegerLike): Integer { return new Integer({op: 'iadd', a: this.x, b: intX(b)}) }
  minus(b: IntegerLike): Integer { return new Integer({op: 'isub', a: this.x, b: intX(b)}) }
  negate(): Integer { return new Integer({op: 'ineg', a: this.x}) }
  times(k: number): Integer { if (!Number.isSafeInteger(k)) throw new RangeError(`${k} is not an integer`); return new Integer({op: 'imul', k, a: this.x}) }
  modBy(k: number): Integer { return new Integer({op: 'imod', k: divisorOf(k), a: this.x}) }
  divBy(k: number): Integer { return new Integer({op: 'idiv', k: divisorOf(k), a: this.x}) }
  lt(b: IntegerLike): Bool { return new Bool({op: 'i<', a: this.x, b: intX(b)}) }
  atMost(b: IntegerLike): Bool { return new Bool({op: 'i<=', a: this.x, b: intX(b)}) }
  gt(b: IntegerLike): Bool { return new Bool({op: 'i<', a: intX(b), b: this.x}) }
  atLeast(b: IntegerLike): Bool { return new Bool({op: 'i<=', a: intX(b), b: this.x}) }
  eq(b: IntegerLike): Bool { return new Bool({op: '=', a: this.x, b: intX(b)}) }
  ne(b: IntegerLike): Bool { return this.eq(b).not() }
}
export type IntegerLike = Integer | number
// An integer function's result: a natural literal in a branch (a match's case, an if's arm) is the integer's.
const intResult = (x: X): X => (x.op === 'nat' ? {op: 'int', value: x.value} : x.op === 'if' ? {...x, then: intResult(x.then), else: intResult(x.else)}
  : x.op === 'match' ? {...x, cases: x.cases.map(c => ({...c, body: intResult(c.body)}))} : x.op === 'natmatch' ? {...x, zero: intResult(x.zero), succ: intResult(x.succ)} : x)
const intX = (t: IntegerLike): X => { if (typeof t !== 'number') return t.x; if (!Number.isSafeInteger(t)) throw new RangeError(`${t} is not an integer`); return {op: 'int', value: t} }
export class Bool {
  constructor(readonly y: Y) {}
  and(...bs: Bool[]): Bool { return new Bool({op: 'and', xs: [this.y, ...bs.map(b => b.y)]}) }
  or(...bs: Bool[]): Bool { return new Bool({op: 'or', xs: [this.y, ...bs.map(b => b.y)]}) }
  not(): Bool { return new Bool({op: 'not', x: this.y}) }
  implies(b: Bool): Bool { return this.not().or(b) }
  iff(b: Bool): Bool { return this.implies(b).and(b.implies(this)) }
}
export const yes = new Bool({op: '<=', a: {op: 'nat', value: 0}, b: {op: 'nat', value: 0}})
export const no = new Bool({op: '<', a: {op: 'nat', value: 0}, b: {op: 'nat', value: 0}})
export class Val {
  constructor(readonly data: Data, readonly x: X) {}
  // Every case covered; each case's fields by name (a natural, or a value of the datatype).
  // oxlint-disable-next-line typescript/no-explicit-any
  match(cases: Record<string, (fields: Record<string, any>) => Nat | Bool | Val | Integer | number>): any {
    const d = this.data
    const built = d.ctors.map(c => {
      const f = cases[c.name]
      if (!f) throw new Error(`${d.name}: match has no case ${c.name}`)
      const binds = c.fields.map(fl => bindName(fl.name))
      const fields = Object.fromEntries(c.fields.map((fl, i) => [fl.name, wrap(fieldSort(fl), {op: 'var', name: binds[i]!})]))
      return {binds, out: f(fields)}
    })
    const first = built[0]!.out
    // A case that is an integer makes every case's number an integer's literal.
    const int = built.some(b => b.out instanceof Integer)
    const body = (o: unknown): X => (typeof o === 'number' ? (int ? intX(o) : natX(o)) : o instanceof Bool ? {op: 'bool', c: o.y} : (o as Nat | Val).x)
    const x: X = {op: 'match', data: d.name, of: this.x, cases: built.map(b => ({binds: b.binds, body: body(b.out)}))}
    return (first instanceof Bool ? new Bool({op: 'holds', x}) : first instanceof Val ? new Val(first.data, x) : int ? new Integer(x) : new Nat(x)) as never
  }
  is(ctor: string): Bool { return new Bool({op: 'is', data: this.data.name, of: this.x, ctor: this.data.index(ctor)}) }
  // Its size: 1 plus the sizes of its fields of its datatype's group (a list's length plus 1, a tree's nodes and leaves).
  size(): Nat { return new Nat({op: 'size', data: this.data.name, of: this.x}) }
  eq(b: Val): Bool { return new Bool({op: '=', a: this.x, b: b.x}) }
  ne(b: Val): Bool { return this.eq(b).not() }
}
// A value of a sort from its term.
export const wrap = (s: Sort, x: X): Nat | Bool | Val | Integer => (s === 'nat' ? new Nat(x) : s === 'bool' ? new Bool({op: 'holds', x}) : s === 'int' ? new Integer(x) : new Val(s, x))
const xOf = (s: Sort, v: unknown): X => (s === 'nat' ? natX(v as NatLike) : s === 'bool' ? {op: 'bool', c: (v as Bool).y} : s === 'int' ? intX(v as IntegerLike) : (v as Val).x)
export function when<T extends Nat | Val | Bool | Integer | number>(c: Bool, a: T, b: T): T extends number ? Nat : T {
  if (a instanceof Bool) return new Bool({op: 'or', xs: [{op: 'and', xs: [c.y, a.y]}, {op: 'and', xs: [{op: 'not', x: c.y}, (b as Bool).y]}]}) as never
  const int = a instanceof Integer || b instanceof Integer, lit = (t: number) => (int ? intX(t) : natX(t))
  const ax = typeof a === 'number' ? lit(a) : (a as Nat | Val).x, bx = typeof b === 'number' ? lit(b) : (b as Nat | Val).x
  const x: X = {op: 'if', c: c.y, then: ax, else: bx}
  return (a instanceof Val ? new Val(a.data, x) : int ? new Integer(x) : new Nat(x)) as never
}

// A datatype: its constructors, each with fields that are naturals or values of a datatype (`self`, another of its group,
// or one declared before it). Its constructors are ordered as Lean's bijection numbers them: those of no field, then
// those with no field of its group, then the rest; a group with a datatype that has no value is refused.
const declared = new Map<string, Data>()
let declaredSeq = 0
export const dataNamed = (name: string): Data => { const d = declared.get(name); if (!d) throw new Error(`no datatype ${name}`); return d }
// A field's sort; whether it is of the datatype's group (the fields its size counts, and an induction descends into).
export const fieldSort = (f: {sort: FieldSort}): Sort => (f.sort === 'nat' || f.sort === 'int' ? f.sort : dataNamed(f.sort.data))
export const inGroup = (d: Data, f: {sort: FieldSort}): boolean => isDataField(f.sort) && d.group.includes(f.sort.data)
export class Data {
  readonly ctors: Ctor[]
  readonly seq = ++declaredSeq
  constructor(readonly name: string, decl: Record<string, Record<string, FieldSort>>, readonly group: string[] = [name]) {
    if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(name)) throw new Error(`${name}: a datatype's name is letters and digits`)
    const all: Ctor[] = Object.entries(decl).map(([c, fs]) => ({name: c, fields: Object.entries(fs).map(([f, s]) => ({name: f, sort: s}))}))
    for (const c of all) for (const f of c.fields) if (isDataField(f.sort) && !group.includes(f.sort.data) && !declared.has(f.sort.data)) throw new Error(`${name}.${c.name}.${f.name}: no datatype ${f.sort.data}`)
    const rank = (c: Ctor) => (!c.fields.length ? 0 : c.fields.every(f => !(isDataField(f.sort) && group.includes(f.sort.data))) ? 1 : 2)
    this.ctors = [...all].sort((a, b) => rank(a) - rank(b))
    declared.set(name, this)
  }
  index(ctor: string): number { const i = this.ctors.findIndex(c => c.name === ctor); if (i < 0) throw new Error(`${this.name} has no constructor ${ctor}`); return i }
  get nullary(): number { return this.ctors.filter(c => !c.fields.length).length }
  make(ctor: string, ...args: (Val | NatLike | Integer)[]): Val {
    const j = this.index(ctor), c = this.ctors[j]!
    if (args.length !== c.fields.length) throw new Error(`${this.name}.${ctor} takes ${c.fields.length} fields`)
    return new Val(this, {op: 'ctor', data: this.name, ctor: j, args: c.fields.map((f, i) => xOf(fieldSort(f), args[i]))})
  }
  // How many constructors deep its smallest value is (a constructor of no field of the group: 0), and each constructor's.
  ctorHeight(c: Ctor): number { return c.fields.reduce((h, f) => (inGroup(this, f) ? Math.max(h, 1 + dataNamed((f.sort as {data: string}).data).height) : h), 0) }
  get height(): number { return groupHeights(this.group).get(this.name)! }
}
// The heights of a group's datatypes (least fixpoint; Infinity where a datatype has no value).
function groupHeights(group: string[]): Map<string, number> {
  const h = new Map(group.map(n => [n, Infinity]))
  for (let changed = true; changed;) {
    changed = false
    for (const n of group) for (const c of dataNamed(n).ctors) {
      const v = c.fields.reduce((m, f) => (isDataField(f.sort) && group.includes(f.sort.data) ? Math.max(m, 1 + h.get(f.sort.data)!) : m), 0)
      if (v < h.get(n)!) { h.set(n, v); changed = true }
    }
  }
  return h
}
// A group's checks: each datatype has a value, and Lean's decoding terminates (a datatype every constructor of which has
// a field of the group and none of no field decodes n at fields up to n itself: those must not call each other in a ring).
function checkGroup(ds: Data[]) {
  const hs = groupHeights(ds.map(d => d.name))
  for (const d of ds) if (hs.get(d.name) === Infinity) throw new Error(`${d.name}: every constructor has a field of ${ds.length > 1 ? 'its group' : d.name} that has no value, so it has no value`)
  void weakOrder(ds)
}
// A datatype is weak when its code n may be decoded at fields up to n (no constructor of no field, the first of the rest
// with a field of the group); the order Lean's measure numbers them in (each weak one after the group's datatypes its
// fields name), or a refusal.
export function weakOrder(ds: Data[]): Map<string, number> {
  const weak = (d: Data) => d.nullary === 0 && d.ctors[0]!.fields.some(f => inGroup(d, f))
  const out = new Map<string, number>(), busy = new Set<string>()
  const visit = (d: Data): number => {
    const had = out.get(d.name)
    if (had !== undefined) return had
    if (!weak(d)) { out.set(d.name, 0); return 0 }
    if (busy.has(d.name)) throw new Error(`${d.name}: its group's datatypes with no constructor of no field name each other in a ring, which the bijection with the naturals doesn't take`)
    busy.add(d.name)
    const o = 1 + Math.max(0, ...d.ctors.flatMap(c => c.fields.flatMap(f => (inGroup(d, f) && (f.sort as {data: string}).data !== d.name ? [visit(dataNamed((f.sort as {data: string}).data))] : []))))
    busy.delete(d.name)
    if (d.ctors.some(c => c.fields.some(f => isDataField(f.sort) && f.sort.data === d.name)) && weak(d)) throw new Error(`${d.name}: no constructor of no field and its first constructor has a field of ${d.name}, which the bijection with the naturals doesn't take`)
    out.set(d.name, o)
    return o
  }
  ds.forEach(visit)
  return out
}
type Decl = Record<string, Record<string, unknown>>
const normField = (own: string, group: string[]) => (s: unknown): FieldSort => {
  if (s === self) return {data: own}
  if (s === 'nat' || (s && typeof s === 'object' && 'nat' in s)) return 'nat'
  if (s === 'int') return 'int'
  if (s instanceof Data) return {data: s.name}
  if (typeof s === 'string' && group.includes(s)) return {data: s}
  throw new Error(`${own}: a field is natural, integer, self, a datatype declared before, or a name of its group`)
}
const withCtors = (d: Data) => { for (const c of d.ctors) Object.defineProperty(d, c.name, c.fields.length ? {value: (...args: (Val | NatLike | Integer)[]) => d.make(c.name, ...args)} : {get: () => d.make(c.name)}) }
// `data('List', {nil: {}, cons: {head: natural, tail: self}})`: `List.nil`, `List.cons(h, t)`, and `xs.match({...})`. A
// field may be a datatype declared before (`data('Bag', {none: {}, more: {items: List, rest: self}})`).
export function data<const D extends Decl>(name: string, decl: D): Data & {[c in keyof D]: keyof D[c] extends never ? Val : (...args: (Val | NatLike | Integer)[]) => Val} {
  const d = new Data(name, Object.fromEntries(Object.entries(decl).map(([c, fs]) => [c, Object.fromEntries(Object.entries(fs as object).map(([f, s]) => [f, normField(name, [name])(s)]))])))
  checkGroup([d]); withCtors(d)
  return d as never
}
// Datatypes declared together, each field naming one of the group by its name (a mutual pair: a rose tree and its
// forest, `mutual({Rose: {node: {value: natural, kids: 'Forest'}}, Forest: {nil: {}, cons: {head: 'Rose', tail: 'Forest'}}})`).
// oxlint-disable-next-line typescript/no-explicit-any
export function mutual<const G extends Record<string, Decl>>(decls: G): {[n in keyof G]: Data & Record<string, any>} {
  const group = Object.keys(decls)
  const ds = group.map(n => new Data(n, Object.fromEntries(Object.entries(decls[n]!).map(([c, fs]) => [c, Object.fromEntries(Object.entries(fs as object).map(([f, s]) => [f, normField(n, group)(s)]))])), group))
  checkGroup(ds); ds.forEach(withCtors)
  return Object.fromEntries(ds.map(d => [d.name, d])) as never
}

// A function: its parameters' sorts, the sort it returns, its body over the parameters (it may call itself, and
// functions defined before or after it: functions that call each other are mutually recursive). Its recursion is checked
// when first read: structural (every call within a ring of functions calling each other passes, at the callee's
// parameter fixed for it, a field, or a field's field, of the caller's, bound by a match; or a natural's predecessor),
// else well-founded (one function, not a ring: a measure every call lowers, proven, below). `decreases`: that parameter;
// `ring`: the functions of its ring, itself among them; `measure` and `termination`: a well-founded one's measure and the
// kernel's proofs that every call lowers it. `measure` given (`{measure: ['xs', 'ys']}`, lexicographic; a component of
// several names their sum, `{measure: [['xs', 'ys']]}`): that measure, not searched, and no structural recursion tried.
export type Fn = {name: string, params: {name: string, sort: Sort}[], ret: Sort, body: () => X, readonly decreases?: number, readonly ring: string[], paramFns: string[],
  readonly measure?: Measure, readonly termination?: Termination, stated?: Measure}
export type Callable = ((...args: (Val | NatLike | Bool | Integer)[]) => any) & {fn: Fn}
type Rec = {decreases?: number, ring: string[], measure?: Measure, termination?: Termination}
const fns = new Map<string, Fn>()
export function define(name: string, params: Record<string, Sort>, ret: Sort, body: (args: Record<string, any>) => Nat | Bool | Val | Integer | number, opts: {measure?: (string | string[])[]} = {}): Callable {
  if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(name)) throw new Error(`${name}: a function's name is letters and digits`)
  const ps = Object.entries(params).map(([n, s]) => ({name: n, sort: s}))
  const stated = opts.measure && measureOf(name, ps, opts.measure)
  let built: X | undefined, rec: Rec | undefined, failed: Error | undefined
  // The recursion, checked once (a refusal kept and given again).
  const got = (): Rec => {
    if (failed) throw failed
    try { return (rec ??= recursion(fn)) } catch (e) { failed = e as Error; throw e }
  }
  const fn = {name, params: ps, ret, paramFns: [] as string[], stated, body: () => {
    if (!built) {
      const args = Object.fromEntries(ps.map(p => [p.name, wrap(p.sort, {op: 'var', name: `${name}.${p.name}`})]))
      built = ret === 'int' ? intResult(xOf(ret, body(args))) : xOf(ret, body(args))
      fn.paramFns = [...new Set(paramsIn(built))]
      walk(built, o => { if (o.op === 'call' && !fns.has(o.fn as string)) throw new Error(`${name} calls ${String(o.fn)}, which isn't defined`) })
    }
    return built
  }, get decreases() { return got().decreases }, get ring() { return got().ring }, get measure() { return got().measure }, get termination() { return got().termination },
  set rec(r: Rec) { rec = r }} as Fn & {rec: Rec}
  fns.set(name, fn)
  const call = (...args: (Val | NatLike | Bool | Integer)[]) => {
    if (args.length !== ps.length) throw new Error(`${name} takes ${ps.length} arguments`)
    return wrap(ret, {op: 'call', fn: name, args: ps.map((p, i) => xOf(p.sort, args[i]))})
  }
  return Object.assign(call, {fn})
}
// An uninterpreted function of a natural (a law about every f): `const f = fnParam('f')`, `f(x)`.
export const fnParam = (name: string): ((x: NatLike) => Nat) & {param: string} =>
  Object.assign((x: NatLike) => new Nat({op: 'apply', param: name, arg: natX(x)}), {param: name})
const paramsIn = (t: unknown): string[] => { const out: string[] = []; walk(t, o => { if (o.op === 'apply') out.push(o.param as string) }); return out }
function walk(t: unknown, f: (o: Record<string, unknown>) => void): void {
  if (Array.isArray(t)) { t.forEach(x => walk(x, f)); return }
  if (!t || typeof t !== 'object') return
  const o = t as Record<string, unknown>
  f(o)
  for (const v of Object.values(o)) walk(v, f)
}

// The calls a body makes, each with what its bound names are fields of (a parameter, through matches).
function callsIn(body: X): {fn: string, args: X[], fieldsOf: Map<string, string>}[] {
  const calls: {fn: string, args: X[], fieldsOf: Map<string, string>}[] = []
  const go = (x: unknown, fieldsOf: Map<string, string>): void => {
    if (!x || typeof x !== 'object') return
    if (Array.isArray(x)) { x.forEach(y => go(y, fieldsOf)); return }
    const o = x as X
    if (o.op === 'match') {
      go(o.of, fieldsOf)
      const of = o.of.op === 'var' ? (fieldsOf.get(o.of.name) ?? o.of.name) : undefined
      o.cases.forEach(c => { const m = new Map(fieldsOf); if (of) c.binds.forEach(b => m.set(b, of)); go(c.body, m) })
      return
    }
    if (o.op === 'natmatch') {
      go(o.of, fieldsOf); go(o.zero, fieldsOf)
      const of = o.of.op === 'var' ? (fieldsOf.get(o.of.name) ?? o.of.name) : undefined, m = new Map(fieldsOf)
      if (of) m.set(o.pred, of)
      go(o.succ, m)
      return
    }
    if (o.op === 'call') calls.push({fn: o.fn, args: o.args, fieldsOf})
    for (const v of Object.values(o)) go(v, fieldsOf)
  }
  go(body, new Map())
  return calls
}
// A function's ring (the functions it calls that call it back, itself among them) and the parameter of each every call
// within the ring passes a field of, or a refusal. Each of the ring is given its own.
function recursion(fn: Fn): Rec {
  const callees = (f: Fn) => [...new Set(callsIn(f.body()).map(c => c.fn))]
  const reach = (from: string): Set<string> => { const seen = new Set<string>(), todo = [from]; while (todo.length) { const g = todo.pop()!; for (const h of callees(fnOf(g))) if (!seen.has(h)) { seen.add(h); todo.push(h) } } return seen }
  const mine = reach(fn.name)
  const ring = [...mine].filter(g => g === fn.name || reach(g).has(fn.name))
  if (!mine.has(fn.name)) { (fn as Fn & {rec: unknown}).rec = {ring: [fn.name]}; return {ring: [fn.name]} }
  const members = [fn.name, ...ring.filter(g => g !== fn.name)].map(fnOf)
  const options = members.map(f => f.params.flatMap((p, i) => (p.sort instanceof Data || p.sort === 'nat' ? [i] : [])))
  const calls = members.map(f => callsIn(f.body()).filter(c => ring.includes(c.fn)))
  // The first choice (by parameter order) every call within the ring meets.
  const choose = (i: number, chosen: number[]): number[] | undefined => {
    if (i === members.length) {
      const ok = members.every((f, a) => calls[a]!.every(c => { const b = members.findIndex(g => g.name === c.fn), arg = c.args[chosen[b]!]!; return arg.op === 'var' && c.fieldsOf.get(arg.name) === `${f.name}.${f.params[chosen[a]!]!.name}` }))
      return ok ? chosen : undefined
    }
    for (const o of options[i]!) { const r = choose(i + 1, [...chosen, o]); if (r) return r }
    return undefined
  }
  const got = fn.stated ? undefined : choose(0, [])
  if (!got) {
    const why = `${fn.name}: not structural recursion (no parameter whose field every recursive call passes${members.length > 1 ? `, in its ring ${members.map(f => f.name).join(', ')}` : ''}${fn.stated ? '; a measure is given' : ''})`
    if (members.length > 1) throw new Error(`${why}, and a ring of functions is taken by structural recursion only`)
    const t = termination(fn, why)
    return {ring: [fn.name], measure: t.measure, termination: t}
  }
  const names = members.map(f => f.name)
  members.forEach((f, a) => { (f as Fn & {rec: unknown}).rec = {decreases: got[a], ring: names} })
  return {decreases: got[0], ring: names}
}

// --- well-founded recursion -------------------------------------------------------------------------------------------
//
// A function whose recursion isn't structural is taken when a measure is proven to fall at every call it makes to itself.
// A measure is a lexicographic tuple of components, each Σ coef·size(parameter) + c (a natural's size itself, a datatype
// value's its size: 1 plus its fields' of the group), read truncated at 0. For each call the body makes to itself, its
// obligation is a law over the function's parameters: under the path to the call (the cases its matches take, the
// conditions of its ifs), the measure at the call's arguments is below the measure at the parameters. Each obligation is
// proven by proveData (a cyclic proof the kernel checks) in a program without the function: its facts are those of the
// datatypes and of the functions already taken, never the equation of the function being taken (nor one of a call
// nested in an argument or a condition: that is refused). Only then is the function's equation a fact.
//
// Why that is sound (lean-kernel/Data.lean's `wf_fix_unique`): the body, read as a functional F of the function, reads
// the function only at the calls on the path the arguments take, each at a lower measure; so F g x = F h x wherever g and
// h agree below x's measure, and a functional with that property has exactly one fixpoint. The equation then has a
// solution (the facts have a model: what the cyclic proofs conclude isn't vacuous) and only one (it is the function as
// written, which Lean's export defines by `termination_by` the same measure). Without the proof, `f(x) = f(x) + 1` would
// be a fact with no model, from which the kernel would prove anything.
//
// The measure: one the user gives, else the first of these the function's runs don't contradict (each call recorded
// from the parameters' sizes to the arguments') and whose obligations are proven: a parameter's size, a lexicographic
// pair or triple of them, a sum of two or of all, then the lexicographic rank core/cycles.ts's LP fits to the runs.
export type Measure = {comps: {coef: number[], c: number}[]}
export type Termination = {measure: Measure, text: string, obligations: {law: DataLaw, proof?: CyclicVerdict, scheme?: string, lemmas: string[]}[], ms: number}
export const terminationMs = {ms: 10_000}
const measurable = (s: Sort) => s === 'nat' || s instanceof Data
function measureOf(name: string, ps: {name: string, sort: Sort}[], m: (string | string[])[]): Measure {
  if (!m.length) throw new Error(`${name}: an empty measure`)
  return {comps: m.map(c => {
    const names = typeof c === 'string' ? [c] : c
    return {coef: ps.map(p => names.filter(n => n === p.name).length), c: names.every(n => ps.some(p => p.name === n && measurable(p.sort))) ? 0 : (() => { throw new Error(`${name}: a measure names its parameters of a datatype or naturals (${names.join(', ')})`) })()}
  })}
}
export const showMeasure = (f: Pick<Fn, 'params'>, m: Measure): string => {
  const comp = (c: Measure['comps'][number]) => {
    const parts = c.coef.flatMap((k, i) => (k ? [`${k < 0 ? '−' : ''}${Math.abs(k) === 1 ? '' : `${Math.abs(k)}·`}${f.params[i]!.sort === 'nat' ? f.params[i]!.name : `size(${f.params[i]!.name})`}`] : []))
    const t = [...parts, ...(c.c ? [String(c.c)] : [])].join(' + ').replace(/\+ −/g, '− ')
    return t || '0'
  }
  return m.comps.length === 1 ? comp(m.comps[0]!) : `(${m.comps.map(comp).join(', ')})`
}
// A component at arguments, as a term (its negative part subtracted, truncated as the encoding reads it).
const sizeX = (s: Sort, a: X): X => (s === 'nat' ? a : {op: 'size', data: (s as Data).name, of: a})
export function measureX(f: Pick<Fn, 'params'>, c: Measure['comps'][number], args: X[]): X {
  const pos: X[] = [], neg: X[] = []
  c.coef.forEach((k, i) => { if (!k) return; const t = sizeX(f.params[i]!.sort, args[i]!); (k > 0 ? pos : neg).push(Math.abs(k) === 1 ? t : {op: 'mul', k: Math.abs(k), a: t}) })
  if (c.c > 0) pos.push({op: 'nat', value: c.c})
  if (c.c < 0) neg.push({op: 'nat', value: -c.c})
  const sum = (ts: X[]): X => (ts.length ? ts.reduce((a, b) => ({op: 'add', a, b})) : {op: 'nat', value: 0})
  return neg.length ? {op: 'sub', a: sum(pos), b: sum(neg)} : sum(pos)
}
const lexY = (as: X[], bs: X[]): Y => (as.length === 1 ? {op: '<', a: as[0]!, b: bs[0]!} : {op: 'or', xs: [{op: '<', a: as[0]!, b: bs[0]!}, {op: 'and', xs: [{op: '=', a: as[0]!, b: bs[0]!}, lexY(as.slice(1), bs.slice(1))]}]})
// The calls a body makes to fn, each with its path: a match on a variable (a parameter, or a field a match bound) is the
// variable at the case's constructor, its fields new variables (`shape`), as a natural matched is 0 or its predecessor
// plus 1; an if's condition, or a match on another term (its other cases true), wraps the law (`wrap`). A case that
// contradicts one taken before on its path is never reached, and its calls have none.
type Site = {args: X[], wrap: (y: Y) => Y, shape: Map<string, X>, vars: {name: string, sort: Sort}[]}
function callSites(fn: Fn): Site[] {
  const out: Site[] = [], yesX: X = {op: 'bool', c: yes.y}
  type Path = {wrap: Site['wrap'], shape: Map<string, X>, vars: Site['vars']}
  const at = (sh: Map<string, X>, name: string): X | undefined => { let t = sh.get(name); while (t && t.op === 'var' && sh.has(t.name)) t = sh.get(t.name); return t }
  const goY = (y: Y, w: Path): void => {
    switch (y.op) {
      case '<': case '<=': case '=': case 'i<': case 'i<=': goX(y.a, w); goX(y.b, w); return
      case 'and': case 'or': y.xs.forEach(z => goY(z, w)); return
      case 'not': goY(y.x, w); return
      case 'is': goX(y.of, w); return
      case 'holds': goX(y.x, w); return
    }
  }
  const goX = (x: X, w: Path): void => {
    switch (x.op) {
      case 'var': case 'nat': return
      case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'iadd': case 'isub': goX(x.a, w); goX(x.b, w); return
      case 'mul': case 'mod': case 'div': case 'imul': case 'imod': case 'idiv': case 'ineg': case 'ofnat': goX(x.a, w); return
      case 'int': return
      case 'apply': goX(x.arg, w); return
      case 'size': goX(x.of, w); return
      case 'bool': goY(x.c, w); return
      case 'ctor': x.args.forEach(a => goX(a, w)); return
      case 'call': x.args.forEach(a => goX(a, w)); if (x.fn === fn.name) out.push({args: x.args, ...w}); return
      case 'if': goY(x.c, w); goX(x.then, {...w, wrap: y => w.wrap({op: 'or', xs: [{op: 'not', x: x.c}, y]})}); goX(x.else, {...w, wrap: y => w.wrap({op: 'or', xs: [x.c, y]})}); return
      case 'match': {
        goX(x.of, w)
        const d = dataNamed(x.data), v = x.of.op === 'var' ? x.of.name : undefined, had = v ? at(w.shape, v) : undefined
        x.cases.forEach((c, j) => {
          if (v && had?.op === 'ctor') {
            // matched before on this path: the same case, its fields the ones bound then; another, never reached
            if (had.ctor === j) goX(c.body, {...w, shape: new Map([...w.shape, ...c.binds.map((b, i) => [b, had.args[i]!] as [string, X])])})
            return
          }
          if (v && !had) {
            const fields = c.binds.map((b, i) => ({name: b, sort: fieldSort(d.ctors[j]!.fields[i]!)}))
            goX(c.body, {wrap: w.wrap, shape: new Map([...w.shape, [v, {op: 'ctor', data: x.data, ctor: j, args: c.binds.map(b => ({op: 'var', name: b}) as X)}]]), vars: [...w.vars, ...fields]})
            return
          }
          goX(c.body, {...w, wrap: y => w.wrap({op: 'holds', x: {op: 'match', data: x.data, of: x.of, cases: x.cases.map((c2, i) => ({binds: c2.binds, body: i === j ? {op: 'bool', c: y} : yesX}))}})})
        })
        return
      }
      case 'natmatch': {
        goX(x.of, w)
        const v = x.of.op === 'var' ? x.of.name : undefined
        if (v && !at(w.shape, v)) {
          goX(x.zero, {...w, shape: new Map([...w.shape, [v, {op: 'nat', value: 0}]])})
          goX(x.succ, {wrap: w.wrap, shape: new Map([...w.shape, [v, {op: 'add', a: {op: 'var', name: x.pred}, b: {op: 'nat', value: 1}}]]), vars: [...w.vars, {name: x.pred, sort: 'nat'}]})
          return
        }
        goX(x.zero, {...w, wrap: y => w.wrap({op: 'holds', x: {op: 'natmatch', of: x.of, zero: {op: 'bool', c: y}, pred: x.pred, succ: yesX}})})
        goX(x.succ, {...w, wrap: y => w.wrap({op: 'holds', x: {op: 'natmatch', of: x.of, zero: yesX, pred: x.pred, succ: {op: 'bool', c: y}}})})
        return
      }
    }
  }
  goX(fn.body(), {wrap: y => y, shape: new Map(), vars: fn.params.map(q => ({name: `${fn.name}.${q.name}`, sort: q.sort}))})
  return out
}
// The obligation of a call: under its path, the measure at its arguments below the measure at the parameters, a law over
// the path's variables (the parameters not matched, the fields of the cases taken).
function obligation(fn: Fn, m: Measure, s: Site, i: number): DataLaw {
  const own = fn.params.map(q => ({op: 'var', name: `${fn.name}.${q.name}`}) as X)
  const shaped = (t: unknown): unknown => (Array.isArray(t) ? t.map(shaped) : t && typeof t === 'object' ? ((t as X).op === 'var' && s.shape.has((t as {name: string}).name) ? shaped(s.shape.get((t as {name: string}).name)) : Object.fromEntries(Object.entries(t).map(([key, v]) => [key, shaped(v)]))) : t)
  const holds = shaped(s.wrap(lexY(m.comps.map(c => measureX(fn, c, s.args)), m.comps.map(c => measureX(fn, c, own))))) as Y
  return {name: `${fn.name}'s call ${i + 1} lowers ${showMeasure(fn, m)}`, vars: s.vars.filter(v => !s.shape.has(v.name)), holds, params: [...new Set(paramsIn(holds))]}
}
// The calls the function's runs make, each from its parameters' sizes to its arguments' (random arguments, up to 2,000
// calls a run: a run past that is cut, its calls kept).
let tracing: {fn: string, stack: Value[][], fuel: number, edge: (from: Value[], to: Value[]) => void} | undefined
function runEdges(fn: Fn): {s: number[], t: number[]}[] {
  const rand = rng(17), edges = new Map<string, {s: number[], t: number[]}>()
  const feat = (vs: Value[]) => fn.params.map((p, i) => (p.sort === 'nat' ? vs[i] as number : p.sort instanceof Data ? sizeOf(p.sort, vs[i]!) : 0))
  const tables = new Map<string, (n: number) => number>()
  const params = new Proxy({}, {get: (_, key: string) => tables.get(key) ?? (tables.set(key, randomFn(rand)), tables.get(key))}) as Record<string, (n: number) => number>
  for (let i = 0; i < 120 && edges.size < 400; i++) {
    const vals = fn.params.map(p => randomValue(p.sort, rand, 1 + (i % 7)))
    tracing = {fn: fn.name, stack: [], fuel: 2000, edge: (a, b) => { const e = {s: feat(a), t: feat(b)}; edges.set(JSON.stringify(e), e) }}
    try { evalX({op: 'call', fn: fn.name, args: vals.map((_, j) => ({op: 'var', name: `$a${j}`}))}, new Map(vals.map((v, j) => [`$a${j}`, v])), params) } catch { /* cut: its calls kept */ } finally { tracing = undefined }
  }
  return [...edges.values()]
}
const valueOf = (c: Measure['comps'][number], xs: number[]) => Math.max(0, c.coef.reduce((a, k, i) => a + k * xs[i]!, c.c))
const lowers = (m: Measure, e: {s: number[], t: number[]}): boolean => {
  for (const c of m.comps) { const a = valueOf(c, e.t), b = valueOf(c, e.s); if (a < b) return true; if (a > b) return false }
  return false
}
function candidates(fn: Fn, edges: {s: number[], t: number[]}[]): Measure[] {
  if (fn.stated) return [fn.stated]
  const ix = fn.params.flatMap((p, i) => (measurable(p.sort) ? [i] : [])), n = fn.params.length
  const one = (i: number) => ({coef: fn.params.map((_, j) => (j === i ? 1 : 0)), c: 0}), sum = (is: number[]) => ({coef: fn.params.map((_, j) => (is.includes(j) ? 1 : 0)), c: 0})
  const out: Measure[] = ix.map(i => ({comps: [one(i)]}))
  for (const i of ix) for (const j of ix) if (i !== j) out.push({comps: [one(i), one(j)]})
  for (const [a, i] of ix.entries()) for (const j of ix.slice(a + 1)) out.push({comps: [sum([i, j])]})
  if (ix.length <= 4) for (const i of ix) for (const j of ix) for (const k of ix) if (i !== j && j !== k && i !== k) out.push({comps: [one(i), one(j), one(k)]})
  if (ix.length > 2) out.push({comps: [sum(ix)]})
  // The LP's rank over the runs (coefficients and constants), where the runs give edges.
  if (edges.length) {
    const vars = ix.map(i => `p${i}`), env = (xs: number[]) => Object.fromEntries(ix.map(i => [`p${i}`, xs[i]!]))
    const r = ranksOfRuns(vars, edges.flatMap(e => [env(e.s), env(e.t)]), edges.map(e => ({s: env(e.s), t: env(e.t)})))
    if (!r.left && r.comps.length) out.push({comps: r.comps.map(c => ({coef: Array.from({length: n}, (_, j) => c.coef[`p${j}`] ?? 0), c: c.c}))})
  }
  return out
}
// An obligation as one node of a cyclic proof (no use, no models): its conclusion, each definition it reads unfolded
// once, the constructors' facts at the values built, the shape at each size it reads and at its variables of a
// datatype, the congruences 16 random models' explanations use. The kernel checks it as any cyclic proof; undefined where it isn't proven.
function directly(law: DataLaw, ms: number): CyclicVerdict | undefined {
  const p = programOf([law]), fs = factsOf(p), concl = encY(p, law.holds, new Map())
  varSorts = new Map(law.vars.flatMap(v => (v.sort instanceof Data ? [[v.name, v.sort] as [string, Data]] : [])))
  const until = clock() + ms
  const insts = instancesOf(p, fs, {roots: [concl], others: [], depth: 1, shapesAt: [...varSorts.keys()].map(ev), etaAt: [], models: modelsFor(p, law, 16, 3), until})
  if (clock() > until) return undefined
  const was = pairedKeys.skip
  pairedKeys.skip = true
  try {
    const v = withDeadline(until, () => proveCyclic(fs.facts, [{name: law.name, hyps: [], concl, rank: [k(0)], insts, uses: []}]))
    return v.proven && v.checked ? v : undefined
  } finally { pairedKeys.skip = was }
}
function termination(fn: Fn, why: string): Termination {
  return counted(dataRate, () => {
    if (dataTrace) console.error(`[data] termination of ${fn.name}`)
    const t0 = performance.now(), sites = callSites(fn)
    if (!fn.params.some(p => measurable(p.sort))) throw new Error(`${why}, and it has no parameter a measure reads (a natural or a datatype value)`)
    if (dataTrace) console.error(`[data]   ${sites.length} calls`)
    const edges = runEdges(fn), until = clock() + terminationMs.ms, tried: string[] = [], seen = new Set<string>()
    if (dataTrace) console.error(`[data]   its runs: ${edges.length} calls at ${Math.round(performance.now() - t0)} ms`)
    for (const m of candidates(fn, edges)) {
      if (dataTrace) console.error(`[data]   ${showMeasure(fn, m)} at ${Math.round(performance.now() - t0)} ms`)
      if (clock() > until) { tried.push('out of time'); break }
      const text = showMeasure(fn, m), bad = edges.find(e => !lowers(m, e))
      if (seen.has(text)) continue
      seen.add(text)
      if (bad) { if (fn.stated || !tried.length) tried.push(`${text}: a call of its runs doesn't lower it (from ${JSON.stringify(bad.s)} to ${JSON.stringify(bad.t)}, the parameters' sizes)`); continue }
      const obligations: Termination['obligations'] = []
      let failed: string | undefined
      for (const [i, site] of sites.entries()) {
        const law = obligation(fn, m, site, i)
        // A call nested in its own argument or condition: the obligation would read the function being taken.
        if (programOf([law]).fns.some(g => g.name === fn.name)) throw new Error(`${why}, and a call to itself is nested in the argument or the condition of another (nested recursion isn't taken)`)
        // First one node, the definitions unfolded once (most calls lower the measure by their cases alone); else
        // proveData: by induction where the obligation has a scheme (a call on a filter of the tail: the filter's own
        // recursion), else, or then, the definitions unfolded alone.
        const left = () => Math.max(1, until - clock()), cex = refute(law, 200)
        if (cex) { failed = `${text}: its call ${i + 1} doesn't lower it at ${JSON.stringify(cex)}`; break }
        const direct = directly(law, Math.min(2000, left()))
        if (direct) { obligations.push({law, proof: direct, lemmas: []}); continue }
        const inductive = schemes(programOf([law]), law).length > 0
        // (no conjectured lemmas: their making isn't counted in the budget, and a call's decrease mostly needs none)
        let v = proveData(law, inductive ? {ms: Math.min(12_000, left()), lemmas: false} : {induction: false, ms: Math.min(4000, left())})
        if (inductive && !(v.proven && v.checked) && !v.counterexample && clock() < until) v = proveData(law, {induction: false, ms: Math.min(4000, left())})
        if (!(v.proven && v.checked)) { failed = `${text}: its call ${i + 1} ${v.counterexample ? `doesn't lower it at ${JSON.stringify(v.counterexample)}` : 'not proven to lower it'}`; break }
        obligations.push({law, proof: v.proof, scheme: v.scheme, lemmas: v.lemmas})
      }
      if (!failed) return {measure: m, text, obligations, ms: Math.round(performance.now() - t0)}
      tried.push(failed)
    }
    throw new Error(`${why}, and no measure is proven to fall at every call${tried.length ? ` (${tried.slice(0, 3).join('; ')})` : ''}`)
  })
}

// A law: its variables' sorts and what holds of them.
export type DataLaw = {name: string, vars: {name: string, sort: Sort}[], holds: Y, params: string[]}
export function law(name: string, vars: Record<string, Sort>, holds: (vs: Record<string, any>) => Bool): DataLaw {
  const vs = Object.entries(vars).map(([n, s]) => ({name: n, sort: s}))
  const y = holds(Object.fromEntries(vs.map(v => [v.name, wrap(v.sort, {op: 'var', name: v.name})]))).y
  return {name, vars: vs, holds: y, params: [...new Set(paramsIn(y))]}
}

// --- values: what the functions compute (the runtime, and the random values the search tests against) ------------------

export type Value = number | {c: number, f: Value[]}
type Env = Map<string, Value>
const fnOf = (name: string) => { const f = fns.get(name); if (!f) throw new Error(`no function ${name}`); return f }
// A function by its name, if one is defined (core/transfer.ts names its copies apart from every other).
export const fnNamed = (name: string): Fn | undefined => fns.get(name)
const asNat = (v: Value) => v as number
// Evaluation within bounds: a natural past 2^53 (no longer exact) always throws EvalLimit, and within the search
// (`evalBounds.on`: proveData, refute) so do calls nested past `depth` or past `calls` of one call's evaluation, which
// recursive powers and factorials reach on small values. The sample that needs one is skipped (refute), the model's
// read is unknown (the search).
export class EvalLimit extends RangeError {}
export const evalBounds = {on: false, depth: 1000, calls: 20_000}
let evalCalls = 0
const exact = (n: number): number => { if (n > Number.MAX_SAFE_INTEGER) throw new EvalLimit('past 2^53'); return n }
export function evalX(x: X, env: Env, params: Record<string, (n: number) => number>, d = 0): Value {
  switch (x.op) {
    case 'var': { const v = env.get(x.name); if (v === undefined) throw new Error(`unbound ${x.name}`); return v }
    case 'nat': return x.value
    case 'add': return exact(asNat(evalX(x.a, env, params, d)) + asNat(evalX(x.b, env, params, d)))
    case 'sub': return Math.max(0, asNat(evalX(x.a, env, params, d)) - asNat(evalX(x.b, env, params, d)))
    case 'min': return Math.min(asNat(evalX(x.a, env, params, d)), asNat(evalX(x.b, env, params, d)))
    case 'max': return Math.max(asNat(evalX(x.a, env, params, d)), asNat(evalX(x.b, env, params, d)))
    case 'mul': return exact(x.k * asNat(evalX(x.a, env, params, d)))
    case 'prod': return exact(asNat(evalX(x.a, env, params, d)) * asNat(evalX(x.b, env, params, d)))
    case 'mod': return asNat(evalX(x.a, env, params, d)) % x.k
    case 'div': return Math.floor(asNat(evalX(x.a, env, params, d)) / x.k)
    case 'int': return x.value
    case 'iadd': return exact(asNat(evalX(x.a, env, params, d)) + asNat(evalX(x.b, env, params, d)))
    case 'isub': return exact(asNat(evalX(x.a, env, params, d)) - asNat(evalX(x.b, env, params, d)))
    case 'ineg': return -asNat(evalX(x.a, env, params, d))
    case 'imul': return exact(x.k * asNat(evalX(x.a, env, params, d)))
    case 'ofnat': return asNat(evalX(x.a, env, params, d))
    case 'imod': return euclidMod(asNat(evalX(x.a, env, params, d)), x.k)
    case 'idiv': { const v = asNat(evalX(x.a, env, params, d)); return (v - euclidMod(v, x.k)) / x.k }
    case 'if': return evalY(x.c, env, params, d) ? evalX(x.then, env, params, d) : evalX(x.else, env, params, d)
    case 'bool': return evalY(x.c, env, params, d) ? 1 : 0
    case 'apply': return params[x.param]!(asNat(evalX(x.arg, env, params, d)))
    case 'size': return sizeOf(dataNamed(x.data), evalX(x.of, env, params, d))
    case 'ctor': return {c: x.ctor, f: x.args.map(a => evalX(a, env, params, d))}
    case 'natmatch': {
      const n = asNat(evalX(x.of, env, params, d))
      if (n === 0) return evalX(x.zero, env, params, d)
      const e2 = new Map(env); e2.set(x.pred, n - 1)
      return evalX(x.succ, e2, params, d)
    }
    case 'match': {
      const v = evalX(x.of, env, params, d) as {c: number, f: Value[]}, cs = x.cases[v.c]!
      const e2 = new Map(env)
      cs.binds.forEach((b, i) => e2.set(b, v.f[i]!))
      return evalX(cs.body, e2, params, d)
    }
    case 'call': {
      const f = fnOf(x.fn), body = f.body(), vals = x.args.map(a => evalX(a, env, params, d))
      const e2: Env = new Map(f.params.map((p, i) => [`${f.name}.${p.name}`, vals[i]!]))
      if (evalBounds.on) {
        if (d === 0) evalCalls = 0
        if (d >= evalBounds.depth || ++evalCalls > evalBounds.calls) throw new EvalLimit(`${f.name}: past the evaluation's bounds`)
      }
      if (tracing?.fn !== f.name) return evalX(body, e2, params, d + 1)
      // A run of a function whose termination is being proven: each call recorded, the run cut past its fuel.
      const t = tracing
      if (--t.fuel < 0) throw new RangeError('out of fuel')
      const top = t.stack.at(-1)
      if (top) t.edge(top, vals)
      t.stack.push(vals)
      try { return evalX(body, e2, params, d + 1) } finally { t.stack.pop() }
    }
  }
}
export function evalY(y: Y, env: Env, params: Record<string, (n: number) => number>, d = 0): boolean {
  switch (y.op) {
    case '<': return asNat(evalX(y.a, env, params, d)) < asNat(evalX(y.b, env, params, d))
    case '<=': return asNat(evalX(y.a, env, params, d)) <= asNat(evalX(y.b, env, params, d))
    case 'i<': return asNat(evalX(y.a, env, params, d)) < asNat(evalX(y.b, env, params, d))
    case 'i<=': return asNat(evalX(y.a, env, params, d)) <= asNat(evalX(y.b, env, params, d))
    case '=': return same(evalX(y.a, env, params, d), evalX(y.b, env, params, d))
    case 'and': return y.xs.every(z => evalY(z, env, params, d))
    case 'or': return y.xs.some(z => evalY(z, env, params, d))
    case 'not': return !evalY(y.x, env, params, d)
    case 'is': return (evalX(y.of, env, params, d) as {c: number}).c === y.ctor
    case 'holds': return evalX(y.x, env, params, d) === 1
  }
}
const euclidMod = (v: number, k: number) => ((v % k) + k) % k
const same = (a: Value, b: Value): boolean => (typeof a === 'number' || typeof b === 'number' ? a === b : a.c === b.c && a.f.every((x, i) => same(x, b.f[i]!)))
export const showValue = (d: Sort, v: Value): string => {
  if (typeof v === 'number') return String(v)
  if (d === 'nat' || d === 'bool' || d === 'int') return JSON.stringify(v)
  const c = d.ctors[v.c]!
  return c.fields.length ? `${c.name}(${c.fields.map((f, i) => showValue(fieldSort(f), v.f[i]!)).join(', ')})` : c.name
}

// Random values: small naturals (so that comparisons and equalities between them happen), values of up to `size`
// constructors of fields of the datatype.
type Rand = () => number
export const rng = (seed: number): Rand => () => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed / 2147483648 }
export function randomValue(s: Sort, rand: Rand, size: number, natMax = 5): Value {
  if (s === 'nat') return Math.floor(rand() * (natMax + 1))
  if (s === 'bool') return rand() < 0.5 ? 0 : 1
  if (s === 'int') return Math.floor(rand() * (2 * natMax + 1)) - natMax
  // The leaves: constructors of no field of the group, or (a datatype with none, a rose tree) those of least height.
  const base = s.ctors.filter(c => c.fields.every(f => !inGroup(s, f)))
  const leaves = base.length ? base : s.ctors.filter(c => s.ctorHeight(c) === s.height)
  const pick = size <= 0 || rand() < 0.25 ? leaves : s.ctors
  const c = pick[Math.floor(rand() * pick.length)]!, j = s.ctors.indexOf(c)
  const rec = c.fields.filter(f => inGroup(s, f)).length
  return {c: j, f: c.fields.map(f => randomValue(fieldSort(f), rand, inGroup(s, f) ? Math.floor((size - 1) / Math.max(1, rec)) : Math.min(3, size), natMax))}
}
// A random function of a natural: a table of small values.
export const randomFn = (rand: Rand, natMax = 5): ((n: number) => number) => { const t = new Map<number, number>(); return n => { if (!t.has(n)) t.set(n, Math.floor(rand() * (natMax + 1))); return t.get(n)! } }

export type Sample = {env: Env, params: Record<string, (n: number) => number>}
export function samples(vars: {name: string, sort: Sort}[], paramNames: string[], n: number, seed = 1): Sample[] {
  const rand = rng(seed), out: Sample[] = []
  for (let i = 0; i < n; i++) out.push({env: new Map(vars.map(v => [v.name, randomValue(v.sort, rand, 1 + (i % 7))])), params: Object.fromEntries(paramNames.map(p => [p, randomFn(rand)]))})
  return out
}

// --- the encoding -----------------------------------------------------------------------------------------------------

const ev = (name: string): E => ({op: 'var', name})
const k = (value: number): E => ({op: 'const', value})
const get = (map: string, key: E): E => ({op: 'get', map, key})
const eqC = (a: E, b: E): C => ({op: '=', a, b})
const leC = (a: E, b: E): C => ({op: '<=', a, b})
const andC = (...xs: C[]): C => (xs.length === 1 ? xs[0]! : {op: 'and', xs})
const implies = (a: C, b: C): C => ({op: 'or', xs: [{op: 'not', x: a}, b]})
const yesC: C = leC(k(0), k(0))
const pairE = (a: E, b: E): E => { const s: E = {op: 'add', a, b}; return {op: 'add', a: {op: 'prod', a: s, b: s}, b} }
export const keyOf = (args: E[]): E => args.slice(1).reduce(pairE, args[0]!)
// The arguments of a key built by keyOf (n of them), read back from its shape.
export function argsOf(key: E, n: number): E[] | undefined {
  if (n === 1) return [key]
  if (key.op !== 'add' || key.a.op !== 'prod' || key.a.a.op !== 'add') return undefined
  const left = argsOf(key.a.a.a, n - 1)
  return left && [...left, key.b]
}
export const tagMap = (d: string) => `${d}.tag`, sizeMap = (d: string) => `${d}.size`
export const fieldMap = (d: Data, j: number, i: number) => `${d.name}.${d.ctors[j]!.name}.${d.ctors[j]!.fields[i]!.name}`
export const ctorMap = (d: Data, j: number) => `${d.name}.${d.ctors[j]!.name}`

// `divisors`: the constants the program divides by (mod, div), and 2 where it reads an integer (its code's parity);
// `ints`: whether it reads an integer.
export type Program = {datas: Data[], fns: Fn[], params: string[], divisors: number[], ints: boolean}
// Everything a law reads: the datatypes, the functions (with those they call), the function parameters.
export function programOf(laws: DataLaw[], extra: Fn[] = []): Program {
  const fs = new Map<string, Fn>(), ds = new Map<string, Data>(), ps = new Set<string>()
  // A datatype with those its fields name (its group, those declared before it).
  const addSort = (s: Sort) => { if (s instanceof Data && !ds.has(s.name)) { ds.set(s.name, s); for (const c of s.ctors) for (const f of c.fields) addSort(fieldSort(f)) } }
  const visit = (t: unknown) => walk(t, o => {
    if (o.op === 'call' && !fs.has(o.fn as string)) { const f = fnOf(o.fn as string); fs.set(f.name, f); f.params.forEach(p => addSort(p.sort)); addSort(f.ret); visit(f.body()) }
    if (o.op === 'apply') ps.add(o.param as string)
    if (o.op === 'size') addSort(dataNamed(o.data as string))
    // (a datatype read only through a constructor, a match or a test of one: a law with a definition unfolded)
    if ((o.op === 'ctor' || o.op === 'match' || o.op === 'is') && typeof o.data === 'string') addSort(dataNamed(o.data))
  })
  for (const l of laws) { l.vars.forEach(v => addSort(v.sort)); visit(l.holds) }
  for (const f of extra) visit({op: 'call', fn: f.name, args: []})
  // In order of declaration (each after those its fields name; a group together).
  const datas = [...ds.values()].sort((a, b) => a.seq - b.seq)
  // Functions in definition order (each after those it calls).
  const order: Fn[] = [], seen = new Set<string>()
  const place = (f: Fn) => { if (seen.has(f.name)) return; seen.add(f.name); walk(f.body(), o => { if (o.op === 'call' && o.fn !== f.name) place(fnOf(o.fn as string)) }); order.push(f) }
  for (const f of fs.values()) place(f)
  // (the recursion of each checked)
  for (const f of order) void f.decreases
  const divs = new Set<number>()
  let ints = false
  const scan = (t: unknown) => walk(t, o => { if (o.op === 'mod' || o.op === 'div' || o.op === 'imod' || o.op === 'idiv') divs.add(o.k as number); if (typeof o.op === 'string' && (intOps.has(o.op) || o.op === 'i<' || o.op === 'i<=')) ints = true })
  for (const l of laws) { scan(l.holds); if (l.vars.some(v => v.sort === 'int')) ints = true }
  for (const f of order) { scan(f.body()); if (f.ret === 'int' || f.params.some(q => q.sort === 'int')) ints = true }
  for (const d of datas) if (d.ctors.some(c => c.fields.some(f => f.sort === 'int'))) ints = true
  if (ints) divs.add(2)
  return {datas, fns: order, params: [...ps], divisors: [...divs].sort((a, b) => a - b), ints}
}

const dataOf = (p: Program, name: string) => p.datas.find(d => d.name === name)!
// Division and remainder by a constant: the maps div$k and mod$k (core/machine.ts names them so), known by Euclid's fact
// at each key read (`arith k`).
export const divMap = (k: number) => `div$${k}`, modMap = (k: number) => `mod$${k}`
const arithMap = /^(?:div|mod)\$(\d+)$/
// Integers by their zigzag code: a code c is the integer p − n, p and n its value's two parts as maps of the code
// (int$pos, int$neg), known by one fact (`zcode`): c + c mod 2 = 2p + 2n, p = 0 where c is odd, n = 0 where it is even;
// a pair (p, n) has the code 2(p ∸ n) + (2(n ∸ p) ∸ 1). Neither direction needs an if, so the kernel splits only where a
// proof needs the sign or the parity.
export const zig = (z: number): number => (z >= 0 ? 2 * z : -2 * z - 1)
export const unzig = (c: number): number => (c % 2 === 0 ? c / 2 : -(c + 1) / 2)
type Pair = [E, E]
const sumE = (a: E, b: E): E => (a.op === 'const' && a.value === 0 ? b : b.op === 'const' && b.value === 0 ? a : {op: 'add', a, b})
export const posMap = 'int$pos', negMap = 'int$neg'
const pairOfCode = (c: E): Pair => {
  if (c.op === 'const') { const z = unzig(c.value); return [k(Math.max(z, 0)), k(Math.max(-z, 0))] }
  return [get(posMap, c), get(negMap, c)]
}
const codeOfPair = ([pos, neg]: Pair): E => {
  if (neg.op === 'const' && neg.value === 0) return {op: 'mul', k: 2, a: pos}
  return {op: 'add', a: {op: 'mul', k: 2, a: {op: 'sub', a: pos, b: neg}}, b: {op: 'sub', a: {op: 'mul', k: 2, a: {op: 'sub', a: neg, b: pos}}, b: k(1)}}
}
const intOps = new Set(['int', 'iadd', 'isub', 'ineg', 'imul', 'ofnat', 'imod', 'idiv'])
// An integer term as the two naturals p − n of its value.
function encI(p: Program, x: X, env: Map<string, E>): Pair {
  if (x.op === 'int') return [k(Math.max(x.value, 0)), k(Math.max(-x.value, 0))]
  if (x.op === 'iadd' || x.op === 'isub') {
    const [a, b] = [encI(p, x.a, env), encI(p, x.b, env)]
    return x.op === 'iadd' ? [sumE(a[0], b[0]), sumE(a[1], b[1])] : [sumE(a[0], b[1]), sumE(a[1], b[0])]
  }
  if (x.op === 'ineg') { const [pos, neg] = encI(p, x.a, env); return [neg, pos] }
  if (x.op === 'imul') { const [pos, neg] = encI(p, x.a, env), m = Math.abs(x.k), sc = (e: E): E => (m === 1 ? e : {op: 'mul', k: m, a: e}); return x.k >= 0 ? [sc(pos), sc(neg)] : [sc(neg), sc(pos)] }
  if (x.op === 'ofnat') return [encX(p, x.a, env), k(0)]
  // pos + (k − 1)·neg is the value plus k·neg: the same remainder, and the quotient plus neg.
  if (x.op === 'imod' || x.op === 'idiv') {
    const [pos, neg] = encI(p, x.a, env), t = x.k === 1 ? pos : sumE(pos, {op: 'mul', k: x.k - 1, a: neg})
    return x.op === 'imod' ? [get(modMap(x.k), t), k(0)] : [get(divMap(x.k), t), neg]
  }
  return pairOfCode(encX(p, x, env))
}
export function encX(p: Program, x: X, env: Map<string, E>): E {
  switch (x.op) {
    case 'prod': return {op: 'prod', a: encX(p, x.a, env), b: encX(p, x.b, env)}
    case 'mod': return get(modMap(x.k), encX(p, x.a, env))
    case 'div': return get(divMap(x.k), encX(p, x.a, env))
    case 'int': return k(zig(x.value))
    case 'iadd': case 'isub': case 'ineg': case 'imul': case 'ofnat': case 'imod': case 'idiv': return codeOfPair(encI(p, x, env))
    case 'var': return env.get(x.name) ?? ev(x.name)
    case 'nat': return k(x.value)
    case 'add': case 'sub': case 'min': case 'max': return {op: x.op, a: encX(p, x.a, env), b: encX(p, x.b, env)}
    case 'mul': return {op: 'mul', k: x.k, a: encX(p, x.a, env)}
    case 'if': return {op: 'if', c: encY(p, x.c, env), then: encX(p, x.then, env), else: encX(p, x.else, env)}
    case 'bool': return {op: 'if', c: encY(p, x.c, env), then: k(1), else: k(0)}
    case 'apply': return get(x.param, encX(p, x.arg, env))
    case 'size': return get(sizeMap(x.data), encX(p, x.of, env))
    case 'call': return get(x.fn, keyOf(x.args.map(a => encX(p, a, env))))
    case 'ctor': { const d = dataOf(p, x.data); return x.args.length ? get(ctorMap(d, x.ctor), keyOf(x.args.map(a => encX(p, a, env)))) : k(x.ctor) }
    case 'natmatch': {
      const of = encX(p, x.of, env), e2 = new Map(env)
      e2.set(x.pred, {op: 'sub', a: of, b: k(1)})
      return {op: 'if', c: eqC(of, k(0)), then: encX(p, x.zero, env), else: encX(p, x.succ, e2)}
    }
    case 'match': {
      const d = dataOf(p, x.data), of = encX(p, x.of, env)
      const bodies = x.cases.map((c, j) => { const e2 = new Map(env); c.binds.forEach((b, i) => e2.set(b, get(fieldMap(d, j, i), of))); return encX(p, c.body, e2) })
      return bodies.slice(0, -1).reduceRight<E>((acc, b, j) => ({op: 'if', c: eqC(get(tagMap(d.name), of), k(j)), then: b, else: acc}), bodies.at(-1)!)
    }
  }
}
export function encY(p: Program, y: Y, env: Map<string, E>): C {
  switch (y.op) {
    case 'i<': case 'i<=': { const [a, b] = [encI(p, y.a, env), encI(p, y.b, env)]; return {op: y.op === 'i<' ? '<' : '<=', a: sumE(a[0], b[1]), b: sumE(b[0], a[1])} }
    // Two integers where one is arithmetic: equal values (the same as equal codes, without writing the sum's code).
    case '=': if (intOps.has(y.a.op) || intOps.has(y.b.op)) { const [a, b] = [encI(p, y.a, env), encI(p, y.b, env)]; return {op: '=', a: sumE(a[0], b[1]), b: sumE(b[0], a[1])} }
      return {op: '=', a: encX(p, y.a, env), b: encX(p, y.b, env)}
    case '<': case '<=': return {op: y.op, a: encX(p, y.a, env), b: encX(p, y.b, env)}
    case 'and': case 'or': return {op: y.op, xs: y.xs.map(z => encY(p, z, env))}
    case 'not': return {op: 'not', x: encY(p, y.x, env)}
    case 'is': return eqC(get(tagMap(y.data), encX(p, y.of, env)), k(y.ctor))
    case 'holds': return eqC(encX(p, y.x, env), k(1))
  }
}

// The facts of a program, each named by what it is (`shape D`, `eta D`, `ctor D.c`, `fn f`, `cong m`).
export type Facts = {facts: Fact[], at: Map<string, number>, arity: Map<string, number>}
export function factsOf(p: Program): Facts {
  const facts: Fact[] = [], at = new Map<string, number>(), arity = new Map<string, number>()
  const put = (name: string, f: Fact) => { at.set(name, facts.length); facts.push({...f, name}) }
  const x = ev('x$')
  for (const d of p.datas) {
    const tag = get(tagMap(d.name), x), size = (t: E) => get(sizeMap(d.name), t)
    // Under tag j: the size, and every field of another constructor 0 (what Lean's model reads there).
    const under = (c: Ctor, j: number): C => {
      const sz = c.fields.flatMap((f, i) => (inGroup(d, f) ? [get(sizeMap((f.sort as {data: string}).data), get(fieldMap(d, j, i), x))] : [])).reduce<E>((a, b) => ({op: 'add', a, b}), k(1))
      const others = d.ctors.flatMap((c2, j2) => (j2 === j ? [] : c2.fields.map((_, i2) => eqC(get(fieldMap(d, j2, i2), x), k(0)))))
      return andC(eqC(size(x), sz), ...others)
    }
    put(`shape ${d.name}`, {name: '', keys: ['x$'], holds: andC(leC(tag, k(d.ctors.length - 1)), ...d.ctors.map((c, j) => implies(eqC(tag, k(j)), under(c, j))))})
    put(`eta ${d.name}`, {name: '', keys: ['x$'], holds: andC(...d.ctors.map((c, j) => implies(eqC(tag, k(j)), eqC(x, c.fields.length ? get(ctorMap(d, j), keyOf(c.fields.map((_, i) => get(fieldMap(d, j, i), x)))) : k(j)))))})
    if (d.nullary) put(`nullary ${d.name}`, {name: '', keys: [], holds: andC(...d.ctors.slice(0, d.nullary).map((_, j) => eqC(get(tagMap(d.name), k(j)), k(j))))})
    for (const [j, c] of d.ctors.entries()) {
      if (!c.fields.length) continue
      const as = c.fields.map((_, i) => `a$${i}`), key = keyOf(as.map(ev)), cell = get(ctorMap(d, j), key)
      arity.set(ctorMap(d, j), as.length)
      put(`ctor ${ctorMap(d, j)}`, {name: '', keys: as, holds: andC(eqC(get(tagMap(d.name), cell), k(j)), ...c.fields.map((_, i) => eqC(get(fieldMap(d, j, i), cell), ev(as[i]!))))})
    }
  }
  for (const f of p.fns) {
    const keys = f.params.map(q => `${f.name}.${q.name}`)
    arity.set(f.name, keys.length)
    const body = encX(p, f.body(), new Map())
    put(`fn ${f.name}`, {name: '', keys, holds: andC(eqC(get(f.name, keyOf(keys.map(ev))), body), ...(f.ret === 'bool' ? [leC(get(f.name, keyOf(keys.map(ev))), k(1))] : []))})
  }
  // Euclid's division by each divisor: x = k·(x div k) + x mod k, x mod k < k.
  for (const k2 of p.divisors) {
    put(`arith ${k2}`, {name: '', keys: ['x$'], holds: andC(eqC(x, {op: 'add', a: {op: 'mul', k: k2, a: get(divMap(k2), x)}, b: get(modMap(k2), x)}), {op: '<', a: get(modMap(k2), x), b: k(k2)})})
    arity.set(divMap(k2), 1); arity.set(modMap(k2), 1)
  }
  if (p.ints) {
    const pos = get(posMap, x), neg = get(negMap, x), par = get(modMap(2), x)
    put('zcode', {name: '', keys: ['x$'], holds: andC(eqC({op: 'add', a: x, b: par}, {op: 'add', a: {op: 'mul', k: 2, a: pos}, b: {op: 'mul', k: 2, a: neg}}), {op: 'or', xs: [eqC(par, k(0)), eqC(pos, k(0))]}, {op: 'or', xs: [eqC(par, k(1)), eqC(neg, k(0))]})})
    arity.set(posMap, 1); arity.set(negMap, 1)
  }
  // Every map the encoding reads: the datatypes' tag, size and fields too (each of one argument).
  for (const d of p.datas) {
    arity.set(tagMap(d.name), 1); arity.set(sizeMap(d.name), 1)
    d.ctors.forEach((c, j) => c.fields.forEach((_, i) => arity.set(fieldMap(d, j, i), 1)))
  }
  for (const q of p.params) arity.set(q, 1)
  for (const [m, n] of arity) {
    const as = Array.from({length: n}, (_, i) => `a$${i}`), bs = Array.from({length: n}, (_, i) => `b$${i}`)
    put(`cong ${m}`, {name: '', keys: [...as, ...bs], holds: implies(andC(...as.map((a, i) => eqC(ev(a), ev(bs[i]!)))), eqC(get(m, keyOf(as.map(ev))), get(m, keyOf(bs.map(ev)))))})
  }
  return {facts, at, arity}
}

// --- the codes Lean's twin defines (lean-kernel/Data.lean, lean-kernel/data.ts) ------------------------------------------

// The naturals onto the pairs in order of their sum (Data.lean's cun) and back (cpair); a datatype's values as naturals:
// those of no field their tag, the rest z + m·q + r (z of no field, m with fields, r the constructor's place among
// those, q its fields packed by cpair). Every natural is a value; numbers past 2^53 are refused.
const tri = (s: number) => (s * (s + 1)) / 2
const cun = (n: number): [number, number] => { let s = Math.floor((Math.sqrt(8 * n + 1) - 1) / 2); while (tri(s) > n) s--; while (tri(s + 1) <= n) s++; const b = n - tri(s); return [s - b, b] }
const cpair = (a: number, b: number) => tri(a + b) + b
const tup = (q: number, k: number, i: number): number => (k <= 1 ? q : i === 0 ? cun(q)[0] : tup(cun(q)[1], k - 1, i - 1))
const tupk = (xs: number[]): number => (xs.length === 1 ? xs[0]! : cpair(xs[0]!, tupk(xs.slice(1))))
const safe = (x: number) => { if (!Number.isSafeInteger(x)) throw new RangeError('past 2^53'); return x }
export function decode(d: Data, n: number): Value {
  const z = d.nullary, m = d.ctors.length - z
  if (n < z) return {c: n, f: []}
  const q = Math.floor((n - z) / m), j = z + ((n - z) % m), c = d.ctors[j]!
  return {c: j, f: c.fields.map((f, i) => { const x = tup(q, c.fields.length, i); return f.sort === 'nat' ? x : f.sort === 'int' ? unzig(x) : decode(dataNamed(f.sort.data), x) })}
}
export function encode(d: Data, v: Value): number {
  const o = v as {c: number, f: Value[]}, z = d.nullary, m = d.ctors.length - z
  if (o.c < z) return o.c
  const c = d.ctors[o.c]!
  return safe(z + m * tupk(c.fields.map((f, i) => (f.sort === 'nat' ? o.f[i] as number : f.sort === 'int' ? zig(o.f[i] as number) : encode(dataNamed(f.sort.data), o.f[i]!)))) + (o.c - z))
}
// Each map of the encoding as a function of its arguments, on the codes (for core/cycles.ts's runs).
export function codeValues(p: Program): Record<string, (...xs: number[]) => number> {
  const out: Record<string, (...xs: number[]) => number> = {}
  for (const d of p.datas) {
    out[tagMap(d.name)] = n => (decode(d, n) as {c: number}).c
    out[sizeMap(d.name)] = n => sizeOf(d, decode(d, n))
    d.ctors.forEach((c, j) => {
      c.fields.forEach((f, i) => { out[fieldMap(d, j, i)] = n => { const v = decode(d, n) as {c: number, f: Value[]}; return v.c === j ? (f.sort === 'nat' ? v.f[i] as number : f.sort === 'int' ? zig(v.f[i] as number) : encode(dataNamed(f.sort.data), v.f[i]!)) : 0 } })
      if (c.fields.length) out[ctorMap(d, j)] = (...xs) => encode(d, {c: j, f: c.fields.map((f, i) => (f.sort === 'nat' ? xs[i]! : f.sort === 'int' ? unzig(xs[i]!) : decode(dataNamed(f.sort.data), xs[i]!)))})
    })
  }
  for (const f of p.fns) out[f.name] = (...xs) => {
    const v = evalX(f.body(), new Map(f.params.map((q, i) => [`${f.name}.${q.name}`, q.sort instanceof Data ? decode(q.sort, xs[i]!) : q.sort === 'int' ? unzig(xs[i]!) : xs[i]!])), {})
    return f.ret instanceof Data ? encode(f.ret, v) : f.ret === 'int' ? zig(v as number) : v as number
  }
  for (const k2 of p.divisors) { out[divMap(k2)] = n => Math.floor(n / k2); out[modMap(k2)] = n => n % k2 }
  if (p.ints) { out[posMap] = n => Math.max(unzig(n), 0); out[negMap] = n => Math.max(-unzig(n), 0) }
  return out
}
// That a value's fields of its datatype have smaller codes (true of the codes above: each field at most q).
export const orderFacts = (p: Program): Fact[] => p.datas.map(d => ({name: `order ${d.name}`, keys: ['x$'], holds: andC(yesC, ...d.ctors.flatMap((c, j) =>
  c.fields.flatMap((f, i): C[] => (isDataField(f.sort) && f.sort.data === d.name ? [implies(eqC(get(tagMap(d.name), ev('x$')), k(j)), {op: '<', a: get(fieldMap(d, j, i), ev('x$')), b: ev('x$')})] : []))))}))

// --- concrete models: a value of the encoding at random values (which terms are equal, for congruences and matches) ----

// Values interned per datatype: a constructor of no field is its tag; the rest numbered from there. A key is a
// pairing's natural, read back through its square root.
export class Model {
  private ids = new Map<string, Map<string, number>>()
  private vals = new Map<string, Value[]>()
  constructor(readonly p: Program, readonly params: Record<string, (n: number) => number>) {}
  id(d: Data, v: Value): number {
    if (typeof v === 'number') return v
    if (!d.ctors[v.c]!.fields.length) return v.c
    const text = JSON.stringify(v)
    let m = this.ids.get(d.name), list = this.vals.get(d.name)
    if (!m || !list) { this.ids.set(d.name, (m = new Map())); this.vals.set(d.name, (list = [])) }
    let i = m.get(text)
    if (i === undefined) { i = d.nullary + list.length; m.set(text, i); list.push(v) }
    return i
  }
  value(d: Data, id: number): Value {
    if (id < d.nullary) return {c: id, f: []}
    const v = this.vals.get(d.name)?.[id - d.nullary]
    if (!v) throw new Error(`${d.name}: no value numbered ${id} here`)
    return v
  }
  // A value of a sort as the encoding's natural, and back.
  code(s: Sort, v: Value): number { return s instanceof Data ? this.id(s, v) : s === 'int' ? zig(v as number) : (v as number) }
  decode(s: Sort, n: number): Value { return s instanceof Data ? this.value(s, n) : s === 'int' ? unzig(n) : n }
  private memo = new Map<string, number>()
  read(map: string, key: number): number {
    const at = `${map}|${key}`, had = this.memo.get(at)
    if (had !== undefined) return had
    const out = this.readNew(map, key)
    this.memo.set(at, out)
    return out
  }
  private terms = new WeakMap<object, WeakMap<object, number>>()
  private readNew(map: string, key: number): number {
    const p = this.p
    for (const d of p.datas) {
      if (map === tagMap(d.name)) return (this.value(d, key) as {c: number}).c
      if (map === sizeMap(d.name)) return sizeOf(d, this.value(d, key))
      for (const [j, c] of d.ctors.entries()) {
        for (const [i, f] of c.fields.entries()) if (map === fieldMap(d, j, i)) { const v = this.value(d, key) as {c: number, f: Value[]}; return v.c === j ? this.code(fieldSort(f), v.f[i]!) : 0 }
        if (c.fields.length && map === ctorMap(d, j)) { const as = unkey(key, c.fields.length); return this.id(d, {c: j, f: c.fields.map((f, i) => this.decode(fieldSort(f), as[i]!))}) }
      }
    }
    const f = p.fns.find(g => g.name === map)
    if (f) {
      const as = unkey(key, f.params.length)
      const env: Env = new Map(f.params.map((q, i) => [`${f.name}.${q.name}`, this.decode(q.sort, as[i]!)]))
      const out = evalX(f.body(), env, this.params)
      return f.ret === 'nat' || f.ret === 'bool' ? out as number : f.ret === 'int' ? zig(out as number) : this.id(f.ret, out)
    }
    const ar = arithMap.exec(map)
    if (ar) { const k2 = Number(ar[1]); return map.startsWith('mod') ? key % k2 : Math.floor(key / k2) }
    if (map === posMap) return Math.max(unzig(key), 0)
    if (map === negMap) return Math.max(-unzig(key), 0)
    const prm = this.params[map]
    if (prm) return prm(key)
    throw new Error(`no map ${map}`)
  }
  evalE(e: E, env: Record<string, number>): number {
    let m = this.terms.get(env)
    if (!m) this.terms.set(env, (m = new WeakMap()))
    const had = m.get(e)
    if (had !== undefined) return had
    const out = this.evalNew(e, env)
    m.set(e, out)
    return out
  }
  private evalNew(e: E, env: Record<string, number>): number {
    switch (e.op) {
      case 'var': { const v = env[e.name]; if (v === undefined) throw new Error(`unbound ${e.name}`); return v }
      case 'const': return e.value
      case 'add': return this.evalE(e.a, env) + this.evalE(e.b, env)
      case 'sub': return Math.max(0, this.evalE(e.a, env) - this.evalE(e.b, env))
      case 'min': return Math.min(this.evalE(e.a, env), this.evalE(e.b, env))
      case 'max': return Math.max(this.evalE(e.a, env), this.evalE(e.b, env))
      case 'mul': return e.k * this.evalE(e.a, env)
      case 'prod': return this.evalE(e.a, env) * this.evalE(e.b, env)
      case 'if': return this.evalC(e.c, env) ? this.evalE(e.then, env) : this.evalE(e.else, env)
      case 'get': return this.read(e.map, this.evalE(e.key, env))
    }
  }
  evalC(c: C, env: Record<string, number>): boolean {
    switch (c.op) {
      case '<': return this.evalE(c.a, env) < this.evalE(c.b, env)
      case '<=': return this.evalE(c.a, env) <= this.evalE(c.b, env)
      case '=': return this.evalE(c.a, env) === this.evalE(c.b, env)
      case 'and': return c.xs.every(x => this.evalC(x, env))
      case 'or': return c.xs.some(x => this.evalC(x, env))
      case 'not': return !this.evalC(c.x, env)
      case 'flag': case 'all': throw new Error(`${c.op} isn't in the encoding`)
    }
  }
}
export const sizeOf = (d: Data, v: Value): number => { const o = v as {c: number, f: Value[]}; return 1 + d.ctors[o.c]!.fields.reduce((s, f, i) => s + (inGroup(d, f) ? sizeOf(fieldSort(f) as Data, o.f[i]!) : 0), 0) }
const isqrt = (n: number) => { let s = Math.floor(Math.sqrt(n)); while (s * s > n) s--; while ((s + 1) * (s + 1) <= n) s++; return s }
export function unkey(key: number, n: number): number[] {
  if (n === 1) return [key]
  const s = isqrt(key), b = key - s * s, a = s - b
  return [...unkey(a, n - 1), b]
}

// --- the search -------------------------------------------------------------------------------------------------------

export type Lemma = {law: DataLaw, spec?: NodeSpec}
// `program`: the datatypes and functions the proof's facts are of; `node`: the law's own node in the proof (lemmas' nodes
// and cases besides).
// `through`: a law proven as said with the built-ins and its definitions unfolded (core/transfer.ts), what it went through.
export type DataVerdict = {proven: boolean, checked: boolean, law: string, counterexample?: Record<string, string>, proof?: CyclicVerdict, lemmas: string[], scheme?: string, ms: number, goal?: string, stuck?: string, tried: number, program?: Program, node?: number, through?: string[]}
// `patience` multiplies each attempt's budget; `ms` the whole search's (120,000 by default). Both are counted in work, not
// wall time (`dataRate` below), so a verdict is the same on any machine.
// `transfer: false` keeps the law as stated (core/transfer.ts: its non-recursive definitions unfolded, the built-ins its
// own recursive functions agree with).
export type Options = {samples?: number, depth?: number, lemmas?: boolean | DataLaw[], ms?: number, induction?: boolean, seed?: number, patience?: number, transfer?: boolean}

// Random values of the law's variables: a law false at one is refuted with it.
// A sample whose evaluation passes the bounds (EvalLimit, or the stack) is skipped.
export function refute(l: DataLaw, n = 400, seed = 7): Record<string, string> | undefined {
  return bounded(() => {
    for (const s of samples(l.vars, programOf([l]).params, n, seed)) {
      let ok: boolean
      try { ok = evalY(l.holds, s.env, s.params) } catch (e) { if (e instanceof RangeError) continue; throw new Error(`${l.name}: ${(e as Error).message}`) }
      if (!ok) return Object.fromEntries(l.vars.map(v => [v.name, showValue(v.sort, s.env.get(v.name)!)]))
    }
    return undefined
  })
}
const bounded = <T>(f: () => T): T => { const was = evalBounds.on; evalBounds.on = true; try { return f() } finally { evalBounds.on = was } }

// The node of a law: its variables (each a plain variable of the encoding), its conclusion, rank (level, size of the
// variable inducted on), the uses of the scheme, and the facts at every term its goal reads, to `depth` unfoldings.
// A use may read another node of the scheme (`member`: a companion, below).
type SchemeUse = {subst: Record<string, E>, guard: C, member?: number}
// `on`: the variable whose size is the rank (a natural's is itself, recursion on a natural).
// A function's own recursion when it is well-founded (its call graph, functional induction): `rank`, its measure at the
// law's arguments (each component a term over the law's variables), `shapes` the values of a datatype it reads.
type Scheme = {name: string, on?: {v: string, d: Data | 'nat'}, uses: SchemeUse[], companions?: Companion[], rank?: E[], shapes?: E[]}
// Mutual induction on a variable of a datatype of a group (a rose tree and its forest): the law, and for each other
// datatype of the group its fields reach, a companion, the law said of a value of that datatype; each node uses the one
// of each field's datatype at that field (member 0 the law, i the i-th companion).
type Companion = {law: DataLaw, on: {v: string, d: Data}, uses: SchemeUse[]}
// The function a function f calls at its decreasing argument's field of datatype `to` (a rose tree's sum, at its forest:
// the forest's sum): the call, the same for every such field, its other arguments f's own parameters or closed terms.
function partner(f: Fn, to: Data): {fn: Fn, args: (number | X)[]} | undefined {
  const di = f.decreases
  if (di === undefined) return undefined
  const own = `${f.name}.${f.params[di]!.name}`, found = new Map<string, {fn: Fn, args: (number | X)[]}>()
  let bad = false
  const go = (x: unknown, fields: Set<string>): void => {
    if (!x || typeof x !== 'object') return
    if (Array.isArray(x)) { x.forEach(y => go(y, fields)); return }
    const t = x as X
    if (t.op === 'match' && t.of.op === 'var' && t.of.name === own) {
      const d = dataNamed(t.data)
      t.cases.forEach((c, j) => go(c.body, new Set([...fields, ...c.binds.filter((_, i) => { const fl = d.ctors[j]!.fields[i]!; return isDataField(fl.sort) && fl.sort.data === to.name })])))
      return
    }
    if (t.op === 'call') {
      const g = fnOf(t.fn), gd = g.decreases, at = gd === undefined ? undefined : t.args[gd]
      if (at?.op === 'var' && fields.has(at.name)) {
        const args = t.args.map((a, i): number | X | undefined => (i === gd ? -1 : a.op === 'var' && a.name.startsWith(`${f.name}.`) ? f.params.findIndex(q => `${f.name}.${q.name}` === a.name) : !JSON.stringify(a).includes('"op":"var"') ? a : undefined))
        if (args.some(a => a === undefined)) bad = true
        else found.set(JSON.stringify([g.name, args]), {fn: g, args: args as (number | X)[]})
      }
    }
    for (const v of Object.values(t)) go(v, fields)
  }
  go(f.body(), new Set())
  return !bad && found.size === 1 ? [...found.values()][0] : undefined
}
// The law said of a value of datatype `to` in place of v: v a variable of `to`, and each call whose decreasing argument
// is then of `to` (no longer of its own datatype) its function's partner at `to`; none where a sort no longer fits (an
// argument, a comparison).
function companionOf(l: DataLaw, v: string, to: Data, name: string): DataLaw | undefined {
  // (a sort unknown, an if's or a match's, fits any)
  const sorts = new Map<string, Sort>(l.vars.map(x => [x.name, x.sort])), same = (a?: Sort, b?: Sort) => a === undefined || b === undefined || (a instanceof Data ? a.name : a) === (b instanceof Data ? b.name : b)
  const sortOf = (x: X, renamed: boolean): Sort | undefined => (x.op === 'var' ? (renamed && x.name === name ? to : sorts.get(x.name)) : x.op === 'call' ? fnOf(x.fn).ret : x.op === 'ctor' ? dataNamed(x.data) : x.op === 'match' || x.op === 'if' ? undefined : 'nat')
  let ok = true
  const lift = (t: unknown): unknown => {
    if (!ok) return t
    if (Array.isArray(t)) return t.map(lift)
    if (!t || typeof t !== 'object') return t
    const o = t as X
    if (o.op === 'var' && o.name === v) return {op: 'var', name}
    if (o.op === 'call') {
      const f = fnOf(o.fn), di = f.decreases, as = o.args.map(a => lift(a) as X)
      if (di !== undefined && !same(sortOf(as[di]!, true), sortOf(o.args[di]!, false))) {
        const pt = partner(f, to)
        if (!pt || !same(sortOf(as[di]!, true), to)) { ok = false; return o }
        const args = pt.args.map(a => (a === -1 ? as[di]! : typeof a === 'number' ? as[a]! : a))
        if (args.some((a, i) => i !== pt.fn.decreases && !same(sortOf(a, true), pt.fn.params[i]!.sort))) { ok = false; return o }
        return {op: 'call', fn: pt.fn.name, args}
      }
      if (as.some((a, i) => !same(sortOf(a, true), f.params[i]!.sort))) { ok = false; return o }
      return {...o, args: as}
    }
    if (o.op === 'ctor') { const d = dataNamed(o.data), as = o.args.map(a => lift(a) as X); if (as.some((a, i) => !same(sortOf(a, true), fieldSort(d.ctors[o.ctor]!.fields[i]!)))) ok = false; return {...o, args: as} }
    const out = Object.fromEntries(Object.entries(o).map(([key, x]) => [key, lift(x)])) as Record<string, unknown>
    if (out.op === '=' && !same(sortOf(out.a as X, true), sortOf(out.b as X, true))) ok = false
    const om = o as X
    if (om.op === 'match' && !same(sortOf(out.of as X, true), dataNamed(om.data))) ok = false
    return out
  }
  const holds = lift(l.holds) as Y
  if (!ok || !JSON.stringify(holds).includes(JSON.stringify({op: 'var', name}))) return undefined
  return {name: `${l.name}, at ${to.name}`, vars: l.vars.map(x => (x.name === v ? {name, sort: to} : x)), holds, params: l.params}
}
// The mutual scheme on v: the companions of the datatypes v's fields reach (through the group), or none.
function mutualScheme(l: DataLaw, v: string, d: Data): Scheme | undefined {
  const at = new Map<string, {law: DataLaw, v: string}>([[d.name, {law: l, v}]]), todo = [d]
  while (todo.length) {
    const x = todo.shift()!, from = at.get(x.name)!
    for (const c of x.ctors) for (const f of c.fields) {
      if (!inGroup(x, f) || at.has((f.sort as {data: string}).data)) continue
      const to = dataNamed((f.sort as {data: string}).data), name = `${v}${to.name}`, law = companionOf(from.law, from.v, to, name)
      if (!law) return undefined
      at.set(to.name, {law, v: name}); todo.push(to)
    }
  }
  if (at.size < 2) return undefined
  const order = [...at.keys()]
  const usesOf = (x: Data, xv: string): SchemeUse[] => x.ctors.flatMap((c, j) => c.fields.flatMap((f, i) => (inGroup(x, f) && at.has((f.sort as {data: string}).data)
    ? [{subst: {[at.get((f.sort as {data: string}).data)!.v]: get(fieldMap(x, j, i), ev(xv))}, guard: eqC(get(tagMap(x.name), ev(xv)), k(j)), member: order.indexOf((f.sort as {data: string}).data)}] : [])))
  return {name: `mutual structure of ${v}`, on: {v, d}, uses: usesOf(d, v), companions: order.slice(1).map(n => { const x = dataNamed(n), a = at.get(n)!; return {law: a.law, on: {v: a.v, d: x}, uses: usesOf(x, a.v)} })}
}
// The width of a program's ranks' middle: its widest measure (1 when every recursion is structural).
const rankWidth = (p: Program) => Math.max(1, ...p.fns.map(f => (f.decreases === undefined ? f.measure?.comps.length ?? 1 : 1)))
// Where a well-founded scheme's node wants a datatype's shape: at the values its measure reads, and at those its measure
// reads at each use (a constructor's value a call passes: its size from its fields).
function rankShapes(shapes: E[], rank: E[], uses: SchemeUse[]): E[] {
  const out = new Map<string, E>(shapes.map(e => [tid(e), e]))
  walk(uses.map(u => rank.map(e => substE(e, {vars: u.subst, maps: {}, flags: {}}))), o => { if (o.op === 'get' && (o.map as string).endsWith('.size')) out.set(tid(o.key as E), o.key as E) })
  return [...out.values()]
}
// The parameters a function's definition is decided at when they are a constructor's value: a structural one's
// decreasing parameter (a datatype's), a well-founded one's parameters of a datatype its body matches on.
function unfoldAt(f: Fn): number[] {
  if (f.decreases !== undefined) return f.params[f.decreases]!.sort instanceof Data ? [f.decreases] : []
  if (!f.measure) return []
  const out = new Set<number>()
  walk(f.body(), o => { if (o.op === 'match' && (o.of as X).op === 'var') { const i = f.params.findIndex(q => `${f.name}.${q.name}` === (o.of as {name: string}).name); if (i >= 0 && f.params[i]!.sort instanceof Data) out.add(i) } })
  return [...out]
}
// The inductions the search tries for a law (its schemes), for tests.
export const schemesOf = (p: Program, l: DataLaw): Scheme[] => schemes(p, l)
function schemes(p: Program, l: DataLaw): Scheme[] {
  const out: Scheme[] = [], seen = new Set<string>()
  const add = (s: Scheme) => { const id = JSON.stringify(s.uses); if (!seen.has(id)) { seen.add(id); out.push(s) } }
  // Recursion induction: each call of the law to a recursive function at the law's variables, its recursive calls'
  // arguments as the uses' substitution (where the case's tag holds).
  walk(l.holds, o => {
    if (o.op !== 'call') return
    const f = fnOf(o.fn as string), args = o.args as X[]
    f.body()
    const m = f.decreases === undefined ? f.measure : undefined
    if (f.decreases === undefined && !m) return
    const at = args[f.decreases ?? 0]!
    if (!m && (at.op !== 'var' || !l.vars.some(v => v.name === at.name))) return
    const d = f.params[f.decreases ?? 0]!.sort as Data | 'nat'
    const formal = new Map(f.params.map((q, i) => [`${f.name}.${q.name}`, args[i]!.op === 'var' && l.vars.some(v => v.name === (args[i] as {name: string}).name) ? ev((args[i] as {name: string}).name) : undefined]))
    const uses: Scheme['uses'] = []
    const go = (x: unknown, env: Map<string, E>, guard: C[]): void => {
      if (!x || typeof x !== 'object') return
      if (Array.isArray(x)) { x.forEach(y => go(y, env, guard)); return }
      const t = x as X
      if (t.op === 'match') {
        go(t.of, env, guard)
        const dd = dataOf(p, t.data), of = encX(p, t.of, env)
        t.cases.forEach((c, j) => { const e2 = new Map(env); c.binds.forEach((b, i) => e2.set(b, get(fieldMap(dd, j, i), of))); go(c.body, e2, [...guard, eqC(get(tagMap(dd.name), of), k(j))]) })
        return
      }
      if (t.op === 'natmatch') {
        go(t.of, env, guard)
        const of = encX(p, t.of, env), e2 = new Map(env)
        go(t.zero, env, [...guard, eqC(of, k(0))])
        e2.set(t.pred, {op: 'sub', a: of, b: k(1)})
        go(t.succ, e2, [...guard, {op: 'not', x: eqC(of, k(0))}])
        return
      }
      // (a well-founded call's descent may need its if's condition: x − y below x where y ≤ x)
      if (m && t.op === 'if') {
        const c = encY(p, t.c, env)
        go(t.c, env, guard); go(t.then, env, [...guard, c]); go(t.else, env, [...guard, {op: 'not', x: c}])
        return
      }
      if (t.op === 'call' && t.fn === f.name) {
        const subst: Record<string, E> = {}
        let ok = true
        t.args.forEach((a, i) => {
          const lv = args[i]!
          if (lv.op !== 'var' || !l.vars.some(v => v.name === lv.name)) { ok = ok && JSON.stringify(a) === JSON.stringify({op: 'var', name: `${f.name}.${f.params[i]!.name}`}); return }
          const e = encX(p, a, env)
          if (JSON.stringify(e) !== JSON.stringify(ev(lv.name))) subst[lv.name] = e
        })
        if (ok && Object.keys(subst).length) uses.push({subst, guard: andC(yesC, ...guard)})
      }
      for (const v of Object.values(t)) go(v, env, guard)
    }
    const env = new Map<string, E>([...formal].flatMap(([key, e]) => (e ? [[key, e] as [string, E]] : [])))
    go(f.body(), env, [])
    if (!uses.length) return
    if (!m) { add({name: `recursion of ${f.name} on ${(at as {name: string}).name}`, on: {v: (at as {name: string}).name, d}, uses}); return }
    // Well-founded: ranked by the measure at the law's arguments; the law's variables it reads named.
    const read = f.params.flatMap((q, i) => (m.comps.some(c => c.coef[i]) && args[i]!.op === 'var' && l.vars.some(v => v.name === (args[i] as {name: string}).name) ? [{i, v: (args[i] as {name: string}).name}] : []))
    add({name: `recursion of ${f.name} on ${read.map(r => r.v).join(', ') || 'its arguments'}`, uses, rank: m.comps.map(c => encX(p, measureX(f, c, args), new Map())),
      shapes: read.filter(r => f.params[r.i]!.sort instanceof Data).map(r => ev(r.v))})
  })
  // Structural induction on each variable of a datatype, the others fixed; mutual where its fields reach another of its
  // group (the law and its companions), plain where they reach none or no companion is found.
  for (const v of l.vars) {
    if (!(v.sort instanceof Data)) continue
    const d = v.sort, x = ev(v.name), mut = mutualScheme(l, v.name, d)
    if (mut) { out.push(mut); continue }
    add({name: `structure of ${v.name}`, on: {v: v.name, d}, uses: d.ctors.flatMap((c, j) => c.fields.flatMap((f, i) => (isDataField(f.sort) && f.sort.data === d.name ? [{subst: {[v.name]: get(fieldMap(d, j, i), x)}, guard: eqC(get(tagMap(d.name), x), k(j))}] : [])))})
  }
  return out
}

// The facts a node's goal reads: each function's at the calls of `roots` (the conclusion), and at the calls in what that
// gives, `depth` rounds deep; each constructor's at every constructor read (no unfolding: the value's tag and fields);
// the shape at `shapesAt` (where a use's guard reads the tag), and from depth 2 at every value whose tag is read; eta at
// `etaAt`; congruences of reads the random models give equal arguments. `others` (the uses' conclusions) are read for
// constructors and congruences, and unfolded too from depth 3.
type Want = {roots: unknown[], others: unknown[], depth: number, shapesAt: E[], etaAt: E[], models: {m: Model, env: Record<string, number>}[], every?: boolean, until?: number}
function instancesOf(p: Program, fs: Facts, w: Want): NodeSpec['insts'] {
  // Past the attempt's time, what is found so far (the attempt then fails or proves with it).
  const late = () => w.until !== undefined && clock() > w.until
  const tt = performance.now(), lap = (what: string) => { if (dataTrace) console.error(`[data]   instances: ${what} at ${Math.round(performance.now() - tt)} ms`) }
  const insts: NodeSpec['insts'] = [], seen = new Set<string>()
  const inst = (fact: string, at: E[]) => { const i = fs.at.get(fact); if (i === undefined) return; const id = JSON.stringify([i, at]); if (!seen.has(id)) { seen.add(id); insts.push({fact: i, at}) } }
  const holdsAt = (fact: string, at: E[]) => { const f = fs.facts[fs.at.get(fact)!]!; return substC(f.holds, {vars: Object.fromEntries(f.keys.map((key, q) => [key, at[q]!])), maps: {}, flags: {}}) }
  const reads = (t: unknown): {map: string, key: E}[] => { const out: {map: string, key: E}[] = []; walk(t, o => { if (o.op === 'get') out.push({map: o.map as string, key: o.key as E}) }); return out }
  const fnOfMap = (map: string) => p.fns.find(g => g.name === map)
  const ctorOf = (map: string): number | undefined => { for (const d of p.datas) for (const [j, c] of d.ctors.entries()) if (c.fields.length && map === ctorMap(d, j)) return c.fields.length; return undefined }
  const all: {map: string, key: E}[] = [], had = new Set<string>()
  const note = (rs: {map: string, key: E}[]) => { const out: {map: string, key: E}[] = []; for (const r of rs) { const id = JSON.stringify(r); if (!had.has(id)) { had.add(id); all.push(r); out.push(r) } } return out }
  // Constructor facts at every constructor read, closed under the reads they bring.
  const ctors = (rs: {map: string, key: E}[]) => {
    let todo = rs
    while (todo.length) {
      const next: {map: string, key: E}[] = []
      for (const r of todo) { const n = ctorOf(r.map), as = n && argsOf(r.key, n); if (n && as) { inst(`ctor ${r.map}`, as); next.push(...note(reads(holdsAt(`ctor ${r.map}`, as)))) } }
      todo = next
    }
  }
  const unfolded = new Set<string>()
  let frontier = reads(w.depth >= 3 ? [w.roots, w.others] : w.roots)
  note(frontier); note(reads(w.others))
  ctors(all)
  for (let round = 0; round < w.depth && frontier.length; round++) {
    const next: {map: string, key: E}[] = []
    for (const r of frontier) {
      const f = fnOfMap(r.map), as = f && argsOf(r.key, f.params.length), rid = JSON.stringify(r)
      if (!f || !as || unfolded.has(rid)) continue
      unfolded.add(rid)
      inst(`fn ${f.name}`, as)
      const body = reads(holdsAt(`fn ${f.name}`, as))
      ctors(note(body))
      for (const b of body) next.push(b)
    }
    frontier = next
  }
  // Euclid's fact at every key a remainder or quotient is read at (a read the facts bring is read too).
  const ariths = () => {
    for (let pass = 0; pass < 2; pass++) for (const r of [...all]) {
      if (r.map === posMap || r.map === negMap) { inst('zcode', [r.key]); note(reads(holdsAt('zcode', [r.key]))) }
      const m = arithMap.exec(r.map)
      if (m) { inst(`arith ${m[1]}`, [r.key]); note(reads(holdsAt(`arith ${m[1]}`, [r.key]))) }
    }
  }
  ariths()
  lap(`unfolded, ${insts.length} instances, ${all.length} reads`)
  // The classes of a model (or, with none, of every branch): the equalities the instances give there (a function's read
  // equal to the branch of its body the model takes, a constructor's field to its argument, eta, an implication's
  // equalities where its premise holds, a use's where its guard does), closed under reading one map at arguments of one
  // class (by signatures: the map and the arguments' classes), each merge with why (a fact, or a congruence).
  type Closure = {find: (x: string) => string, terms: Map<string, E>, adj: Map<string, {to: string, cong?: {map: string, x: E[], y: E[]}}[]>, truthOf: (c: C) => boolean | undefined}
  const closure = (model?: M): Closure => {
    const parent = new Map<string, string>(), terms = new Map<string, E>(), adj: Closure['adj'] = new Map()
    const find = (x: string): string => { let r = x; while (parent.has(r)) r = parent.get(r)!; return r }
    const linked = new Set<string>()
    const edge = (x: E, y: E, cong?: {map: string, x: E[], y: E[]}) => {
      const a2 = tid(x), b2 = tid(y)
      terms.set(a2, x); terms.set(b2, y)
      if (a2 === b2) return false
      const merged = find(a2) !== find(b2)
      // A congruence is recorded even between reads already of one class (they may be so only through a constant).
      if (!merged && (!cong || linked.has(a2 < b2 ? `${a2}|${b2}` : `${b2}|${a2}`))) return false
      linked.add(a2 < b2 ? `${a2}|${b2}` : `${b2}|${a2}`)
      if (merged) parent.set(find(a2), find(b2))
      ;(adj.get(a2) ?? adj.set(a2, []).get(a2)!).push({to: b2, cong}); (adj.get(b2) ?? adj.set(b2, []).get(b2)!).push({to: a2, cong: cong && {map: cong.map, x: cong.y, y: cong.x}})
      return merged
    }
    const truthOf = (c: C): boolean | undefined => { if (!model) return undefined; try { return model.m.evalC(c, model.env) } catch { return undefined } }
    const leaves = (e: E): E[] => { if (e.op !== 'if') return [e]; const t = truthOf(e.c); return t === undefined ? [...leaves(e.then), ...leaves(e.else)] : leaves(t ? e.then : e.else) }
    const active = (c: C): void => {
      if (c.op === 'and') { c.xs.forEach(active); return }
      if (c.op === 'or') {
        if (!model) { c.xs.forEach(x => { if (x.op !== 'not') active(x) }); return }
        const open = c.xs.filter(x => truthOf(x) !== false)
        if (open.length === 1) active(open[0]!)
        else { const neg = c.xs.find(x => x.op === 'not' && truthOf(x.x) === true); if (neg) c.xs.filter(x => x !== neg).forEach(x => { if (truthOf(x) === true) active(x) }) }
        return
      }
      if (c.op === '=' && (!model || truthOf(c) === true)) for (const leaf of leaves(c.b)) edge(c.a, leaf)
    }
    for (const q of insts) active(holdsAt(fs.facts[q.fact]!.name, q.at))
    for (const c of w.others as C[]) active(c)
    const cells = new Map<string, {key: E, as: E[]}[]>()
    for (const r of all) { const n = fs.arity.get(r.map), as = n ? argsOf(r.key, n) : undefined; if (as) (cells.get(r.map) ?? cells.set(r.map, []).get(r.map)!).push({key: r.key, as}) }
    for (let changed = true; changed && !late();) {
      changed = false
      for (const [map, list] of cells) {
        const bySig = new Map<string, {key: E, as: E[]}>()
        for (const x of list) {
          const sig = x.as.map(t => find(tid(t))).join('\u0001'), y = bySig.get(sig)
          if (!y) { bySig.set(sig, x); continue }
          if (tid(y.key) !== tid(x.key) && edge(get(map, y.key), get(map, x.key), {map, x: y.as, y: x.as})) changed = true
        }
      }
    }
    return {find, terms, adj, truthOf}
  }
  // A function read whose decreasing argument a model's classes make a constructor's value (the argument itself, or a
  // term of its class) unfolds there too: where the definition's match is decided. Each such instance stands for the
  // reads it was unfolded for (`reached` keeps it in a case where it is one of them).
  if (w.depth >= 1) {
    let extra = 0
    for (const model of w.models.length ? w.models : [undefined]) {
      if (late()) break
      const cl = closure(model)
      // Once per function and class of its arguments (this model's): a term the facts already make equal to one
      // unfolded brings nothing new.
      const sigOf = (fn: string, as: E[]) => `${fn}(${as.map(a => cl.find(tid(a))).join(',')})`
      const done = new Set<string>()
      for (const q of insts) { const name = fs.facts[q.fact]!.name; if (name.startsWith('fn ')) done.add(sigOf(name.slice(3), q.at)) }
      for (const r of [...all]) {
        const f = fnOfMap(r.map)
        if (!f) continue
        const as = argsOf(r.key, f.params.length)
        if (!as) continue
        for (const di of unfoldAt(f)) {
        const own = as[di]!, d = f.params[di]!.sort as Data, root = cl.find(tid(own))
        const built = (t: E) => (t.op === 'get' && d.ctors.some((c, j) => c.fields.length && t.map === ctorMap(d, j))) || (t.op === 'const' && t.value < d.nullary)
        const cands = built(own) ? [own] : [...cl.terms.values()].filter(t => built(t) && cl.find(tid(t)) === root)
        for (const t of cands) {
          const as2 = as.map((a, i) => (i === di ? t : a)), rid = JSON.stringify({map: f.name, key: keyOf(as2)}), key2 = JSON.stringify([fs.at.get(`fn ${f.name}`), as2])
          const anchor = {read: tid(get(f.name, r.key)), arg: own, value: t}, had = anchoredAt.get(key2) ?? []
          if (!had.some(x => x.read === anchor.read)) anchoredAt.set(key2, [...had, anchor])
          if (unfolded.has(rid) || extra >= 12 || done.has(sigOf(f.name, as2))) continue
          unfolded.add(rid); extra++; done.add(sigOf(f.name, as2))
          if (dataTrace) console.error(`[data]     unfold ${f.name} at ${JSON.stringify(as2).slice(0, 160)} for ${JSON.stringify(r.key).slice(0, 80)}`)
          inst(`fn ${f.name}`, as2)
          note([{map: f.name, key: keyOf(as2)}])
          ctors(note(reads(holdsAt(`fn ${f.name}`, as2))))
        }
        }
      }
    }
  }
  lap(`by constructors, ${insts.length} instances, ${all.length} reads`)
  const dataOfTerm = (t: E): Data | undefined => {
    if (t.op === 'get') { for (const d of p.datas) if (t.map === tagMap(d.name) || t.map === sizeMap(d.name)) return d; const f = fnOfMap(t.map); if (f && f.ret instanceof Data) return f.ret; for (const d of p.datas) for (const [j, c] of d.ctors.entries()) { if (c.fields.length && t.map === ctorMap(d, j)) return d; for (const [i, fl] of c.fields.entries()) if (isDataField(fl.sort) && t.map === fieldMap(d, j, i)) return dataNamed(fl.sort.data) } }
    return undefined
  }
  const shape = (t: E, d?: Data) => { const dd = d ?? dataOfTerm(t); if (dd) { inst(`shape ${dd.name}`, [t]); ctors(note(reads(holdsAt(`shape ${dd.name}`, [t])))) } }
  for (const t of w.shapesAt) shape(t, typeOfVar(p, t))
  // A size the goal reads (a measure's, in a well-founded call's obligation): the shape of its value, which gives the
  // size from the fields.
  for (const r of reads([w.roots, w.others])) for (const d of p.datas) if (r.map === sizeMap(d.name)) shape(r.key, d)
  if (w.depth >= 2) for (const r of [...all]) for (const d of p.datas) if (r.map === tagMap(d.name)) shape(r.key, d)
  for (const t of w.etaAt) { const d = typeOfVar(p, t) ?? dataOfTerm(t); if (d) { inst(`eta ${d.name}`, [t]); shape(t, d); ctors(note(reads(holdsAt(`eta ${d.name}`, [t])))) } }
  // A constant's tag is read where its tag is (the nullary facts).
  for (const d of p.datas) if (d.nullary && all.some(r => r.map === tagMap(d.name))) { inst(`nullary ${d.name}`, []); for (let j = 0; j < d.nullary; j++) all.push({map: tagMap(d.name), key: k(j)}) }
  // Congruences (a map is a function), in each model: every value the model reads explained against one of its class
  // (the path between them, each congruence on it explained in turn); the congruences the explanations use are the
  // instances (with `every`, those that every model's explanations use).
  const used = new Map<string, {map: string, at: E[], n: number}>()
  for (const model of w.models) {
    if (late()) break
    const {find, adj, truthOf} = closure(model)
    const counted = new Set<string>(), explained = new Set<string>()
    const explain = (a2: string, b2: string): void => {
      const key = a2 < b2 ? `${a2}|${b2}` : `${b2}|${a2}`
      if (a2 === b2 || explained.has(key)) return
      explained.add(key)
      const back = new Map<string, {from: string, cong?: {map: string, x: E[], y: E[]}}>([[a2, {from: ''}]]), queue = [a2]
      // A path through no constant first: two terms the model gives one value aren't equal for that alone (each needs
      // its own facts), and a congruence between them is what the proof can use; else one through a constant.
      const isConst = (x: string) => x !== a2 && x !== b2 && x.startsWith('{"op":"const"')
      for (const avoid of [true, false]) {
        if (back.has(b2)) break
        back.clear(); back.set(a2, {from: ''}); queue.length = 0; queue.push(a2)
        while (queue.length && !back.has(b2)) { const x = queue.shift()!; if (avoid && isConst(x)) continue; for (const e of adj.get(x) ?? []) if (!back.has(e.to)) { back.set(e.to, {from: x, cong: e.cong}); queue.push(e.to) } }
      }
      if (!back.has(b2)) return
      for (let at = b2; at !== a2;) {
        const step = back.get(at)!
        if (step.cong) {
          const c = step.cong, k2 = JSON.stringify([c.map, c.x, c.y])
          if (!counted.has(k2)) { counted.add(k2); const had = used.get(k2) ?? used.get(JSON.stringify([c.map, c.y, c.x])); if (had) had.n++; else used.set(k2, {map: c.map, at: [...c.x, ...c.y], n: 1}) }
          c.x.forEach((t, q) => explain(tid(t), tid(c.y[q]!)))
        }
        at = step.from
      }
    }
    // The values this model reads: the conclusions' reads, and each fact's where the model takes it (an if's condition
    // and taken branch, an implication's conclusion where its premise holds).
    const read = new Set<string>()
    const look = (t: unknown, whole: boolean): void => {
      if (!t || typeof t !== 'object') return
      if (Array.isArray(t)) { t.forEach(x => look(x, whole)); return }
      const o = t as E | C
      if (!whole && o.op === 'if') { look(o.c, whole); const b2 = truthOf(o.c); if (b2 !== false) look(o.then, whole); if (b2 !== true) look(o.else, whole); return }
      if (!whole && o.op === 'or' && o.xs.length === 2 && o.xs[0]!.op === 'not') { look(o.xs[0], whole); if (truthOf(o.xs[0]!.x) !== false) look(o.xs[1], whole); return }
      if (o.op === 'get') { read.add(tid(o)); return }
      for (const v of Object.values(o)) look(v, whole)
    }
    look([w.roots, w.others], true)
    look(insts.map(q => holdsAt(fs.facts[q.fact]!.name, q.at)), false)
    const byClass = new Map<string, string[]>()
    for (const v of read) { const r = find(v); (byClass.get(r) ?? byClass.set(r, []).get(r)!).push(v) }
    // Within a class, first the parts that join without a constant (each value against its part's first), then the parts.
    const isConstId = (x: string) => x.startsWith('{"op":"const"')
    for (const vs of byClass.values()) {
      if (vs.length < 2) continue
      const part = new Map<string, string>()
      for (const v of vs) {
        if (part.has(v)) continue
        const seen = new Set([v]), queue = [v]
        while (queue.length) { const x = queue.shift()!; for (const e of adj.get(x) ?? []) if (!seen.has(e.to) && !isConstId(e.to)) { seen.add(e.to); queue.push(e.to) } }
        for (const u of vs) if (seen.has(u) && !part.has(u)) part.set(u, v)
      }
      for (const v of vs) if (part.get(v) !== v) explain(part.get(v)!, v)
      const heads = [...new Set(part.values())]
      for (const h of heads.slice(1)) explain(heads[0]!, h)
    }
    if (allCong) for (const es of adj.values()) for (const e of es) if (e.cong) { const k2 = JSON.stringify([e.cong.map, e.cong.x, e.cong.y]), k3 = JSON.stringify([e.cong.map, e.cong.y, e.cong.x]); if (!used.has(k2) && !used.has(k3)) used.set(k2, {map: e.cong.map, at: [...e.cong.x, ...e.cong.y], n: 1}) }
  }
  for (const d of used.values()) if (!w.every || d.n >= w.models.length) inst(`cong ${d.map}`, d.at)
  for (const q of [...insts]) note(reads(holdsAt(fs.facts[q.fact]!.name, q.at)))
  ariths()
  lap(`congruences, ${insts.length} instances, ${w.models.length} models`)
  return insts
}
let varSorts = new Map<string, Data>()
// A term's text, once per object (terms are compared by it, and some are large).
const idMemo = new WeakMap<object, string>()
const tid = (t: E): string => { let out = idMemo.get(t); if (out === undefined) idMemo.set(t, (out = JSON.stringify(t))); return out }
// An instance unfolded where a read's argument equals a constructor's value: the read it stands for (for `reached`).
const anchoredAt = new Map<string, {read: string, arg: E, value: E}[]>()
const typeOfVar = (_p: Program, t: E): Data | undefined => (t.op === 'var' ? varSorts.get(t.name) : undefined)

// The values a law's conclusion compares (eta is wanted at each: a variable equal to a value built is the constructor at
// its own fields).
function valuesCompared(p: Program, l: DataLaw): E[] {
  const out: E[] = []
  const dataTerm = (x: X): boolean => (x.op === 'var' ? l.vars.some(v => v.name === x.name && v.sort instanceof Data) : x.op === 'call' ? fnOf(x.fn).ret instanceof Data : x.op === 'ctor')
  walk(l.holds, o => { if (o.op === '=' && dataTerm(o.a as X)) for (const side of [o.a, o.b] as X[]) if (side.op === 'var') out.push(encX(p, side, new Map())) })
  return out
}

// Where a lemma's terms appear in a goal: a substitution of its variables by terms of the goal, for each term of the goal
// that one of the lemma's sides matches (its variables read anywhere, the rest exactly).
function matches(pattern: E, vars: Set<string>, t: E, s: Record<string, E>): Record<string, E> | undefined {
  if (pattern.op === 'var' && vars.has(pattern.name)) {
    const had = s[pattern.name]
    if (had) return JSON.stringify(had) === JSON.stringify(t) ? s : undefined
    return {...s, [pattern.name]: t}
  }
  if (pattern.op !== t.op) return undefined
  const po = pattern as unknown as Record<string, unknown>, to = t as unknown as Record<string, unknown>
  let out: Record<string, E> | undefined = s
  for (const key of Object.keys(po)) {
    if (!out) return undefined
    const a = po[key], b = to[key]
    if (a && typeof a === 'object' && 'op' in (a as object)) {
      if (!b || typeof b !== 'object') return undefined
      if ((a as {op: string}).op && ['<', '<=', '=', 'and', 'or', 'not'].includes((a as {op: string}).op)) out = JSON.stringify(a) === JSON.stringify(b) ? out : undefined
      else out = matches(a as E, vars, b as E, out)
    } else if (JSON.stringify(a) !== JSON.stringify(b)) return undefined
  }
  return out
}

export type Proven = {law: DataLaw, spec: NodeSpec, nodes: NodeSpec[]}
type M = {m: Model, env: Record<string, number>}
// The cases of a law: a decision tree over the guards its unfolded calls evaluate (a function's body's ifs, at the
// branch each random model takes), those over the law's variables and their fields alone, at most four deep. Each leaf
// is its guards (true or false) and the models that reach it; a side no model reaches is a leaf of none, the models of
// the node it parts from near it.
type Case = {lits: C[], models: M[] | undefined, near?: M[]}
function casesOf(p: Program, unfolded: C[], vars: Set<string>, models: M[]): Case[] {
  const plain = (e: E): boolean => (e.op === 'var' ? vars.has(e.name) : e.op === 'const' ? true : e.op === 'get' ? p.datas.some(d => e.map.startsWith(`${d.name}.`)) && !p.datas.some(d => d.ctors.some((c, j) => c.fields.length > 0 && e.map === ctorMap(d, j))) && plain(e.key)
    : e.op === 'add' || e.op === 'sub' || e.op === 'min' || e.op === 'max' ? plain(e.a) && plain(e.b) : e.op === 'mul' ? plain(e.a) : false)
  const plainC = (c: C): boolean => JSON.stringify(c).includes('"op":"var"') && (c.op === '<' || c.op === '<=' || c.op === '=' ? plain(c.a) && plain(c.b) : c.op === 'not' ? plainC(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.every(plainC) : false)
  // The functions' facts the goal unfolds.
  const roots: C[] = unfolded
  const sigs = models.map(({m, env}) => {
    const out = new Map<string, {c: C, t: boolean}>()
    const truthOf = (c: C) => { try { return m.evalC(c, env) } catch { return undefined } }
    const go = (t: unknown): void => {
      if (!t || typeof t !== 'object') return
      if (Array.isArray(t)) { t.forEach(go); return }
      const o = t as E
      if (o.op === 'if') {
        const v = truthOf(o.c)
        if (v === undefined) return
        if (plainC(o.c)) { const key = JSON.stringify(o.c); if (!out.has(key)) out.set(key, {c: o.c, t: v}) }
        go(v ? o.then : o.else)
        return
      }
      for (const val of Object.values(o)) go(val)
    }
    go(roots)
    return out
  })
  const build = (ms: number[], lits: C[], decided: Set<string>, depth: number): Case[] => {
    const count = new Map<string, number>()
    for (const i of ms) for (const key of sigs[i]!.keys()) if (!decided.has(key)) count.set(key, (count.get(key) ?? 0) + 1)
    const pick = [...count.entries()].sort((a2, b2) => b2[1] - a2[1])[0]
    if (!pick || depth >= 4) return [{lits, models: ms.length ? ms.map(i => models[i]!) : undefined}]
    const key = pick[0], c = ms.map(i => sigs[i]!.get(key)).find(x => x)!.c
    const side = (t: boolean) => ms.filter(i => sigs[i]!.get(key)?.t !== !t)
    const d2 = new Set([...decided, key])
    // A guard every one of many models takes one way is not split (its other side is likely no case at all).
    if (ms.length >= 20 && (!side(true).length || !side(false).length)) return build(ms, lits, d2, depth)
    return [true, false].flatMap(t => { const s2 = side(t), lit = t ? c : {op: 'not', x: c} as C; return s2.length ? build(s2, [...lits, lit], d2, depth + 1) : [{lits: [...lits, lit], models: undefined, near: ms.map(i => models[i]!)}] })
  }
  return build(models.map((_, i) => i), [], new Set(), 0)
}

// One attempt: the law's node (and the lemmas', proven before, with their own nodes) at a scheme and a depth. With
// several cases, a main node uses a node per case (each its guards as hypotheses, its own instances), at rank
// (level, size, 1) above theirs (level, size, 0); a case node uses the main node at the children.
const dataTrace = !!(globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env?.DATA_TRACE
// Debugging: every congruence a model's closure makes, not only those explanations use.
const allCong = !!(globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env?.DATA_ALLCONG
function attempt(p: Program, fs: Facts, l: DataLaw, scheme: Scheme | undefined, depth: number, lemmas: Proven[], level: number, pool: M[]): {verdict: CyclicVerdict, specs: NodeSpec[], main: number} {
  const t0 = clock()
  anchoredAt.clear()
  // A few models for the instances; the whole pool for the cases (a rare case gets its own models from it).
  const few = (ms: M[]) => ms.slice(0, 16)
  const specs: NodeSpec[] = [], where = new Map<string, number>()
  for (const lm of lemmas) {
    const local = new Map<number, number>()
    lm.nodes.forEach((n, i) => {
      if (where.has(n.name)) { local.set(i, where.get(n.name)!); return }
      local.set(i, specs.length); where.set(n.name, specs.length)
      specs.push({...n, uses: n.uses.map(u => ({...u, node: local.get(u.node) ?? u.node}))})
    })
  }
  // The scheme's nodes: the law's, then each companion's (a mutual induction), each its own models. A use of member i
  // reads node -1 - i until the nodes are placed.
  const members: {law: DataLaw, on?: Scheme['on'], uses: SchemeUse[], pool: M[], rank?: E[], shapes?: E[]}[] = [{law: l, on: scheme?.on, uses: scheme?.uses ?? [], pool, rank: scheme?.rank, shapes: scheme?.shapes}, ...(scheme?.companions ?? []).map(c => ({...c, pool: modelsFor(p, c.law, pool.length, 5)}))]
  const concls = members.map(mb => encY(p, mb.law.holds, new Map()))
  const base = specs.length, title = `${l.name}${scheme ? ` (${scheme.name})` : ''}`
  varSorts = new Map(members.flatMap(mb => mb.law.vars.flatMap(v => (v.sort instanceof Data ? [[v.name, v.sort] as [string, Data]] : []))))
  const lemmaNodes = lemmas.map(lm => ({law: lm.law, node: where.get(lm.spec.name)!, concl: specs[where.get(lm.spec.name)!]!.concl}))
  const useConcl = (u: NodeSpec['uses'][number]) => substC(u.node < 0 ? concls[-1 - u.node]! : specs[u.node]!.concl, {vars: u.subst, maps: {}, flags: {}})
  type Planned = Omit<NodeSpec, 'rank'> & {sub: number, cases?: C[]}
  const plans: Planned[][] = []
  for (const [mi, mb] of members.entries()) {
    const models = mb.pool.slice(0, 24), concl = concls[mi]!, name = mi === 0 ? title : `${title}, at ${(mb.on!.d as Data).name}`
    const ih = mb.uses.map(u => ({node: -1 - (u.member ?? mi), subst: u.subst, guard: u.guard}))
    const shapesAt = mb.rank ? rankShapes(mb.shapes ?? [], mb.rank, mb.uses) : mb.on && mb.on.d !== 'nat' ? [ev(mb.on.v)] : []
    const ihConcls = ih.map(useConcl)
    // Uses of the lemmas, where a lemma's largest read matches a read of this goal (unfolded), its key up to the
    // equalities the unfolded definitions give (any branch); twice over, the uses' own conclusions read the second time.
    const pre = instancesOf(p, fs, {roots: [concl], others: ihConcls, depth, shapesAt, etaAt: [], models: [], until: t0 + attemptMs.ms})
    const lemmaUses = lemmaUsesFor(p, fs, lemmaNodes, [concl, ihConcls], pre, models)
    const uses = [...ih, ...lemmaUses]
    if (dataTrace) for (const u of lemmaUses) console.error(`[data]   lemma use ${specs[u.node]!.name.slice(0, 40)} at ${Object.entries(u.subst).map(([x, t]) => `${x} := ${JSON.stringify(t).slice(0, 80)}`).join('; ')}`)
    // The lemmas' conclusions are unfolded like the law's (they are what the goal reads, said another way); the cycle's
    // own uses only from depth 3.
    const instsFor = (ms: M[], us: NodeSpec['uses'], every = false) => instancesOf(p, fs, {roots: [concl], others: us.map(useConcl), depth, shapesAt, etaAt: [...shapesAt, ...valuesCompared(p, mb.law)], models: ms, every, until: t0 + attemptMs.ms})
    const cases = scheme ? casesOf(p, pre.filter(q => fs.facts[q.fact]!.name.startsWith('fn ')).map(q => holdsAt(fs, q)), new Set(mb.law.vars.map(v => v.name)), mb.pool) : []
    if (cases.length <= 1) {
      // One node: four uses of a lemma, twelve in all, the best first (as lemmaUsesFor ranks them).
      const one = capUses(uses, 12)
      plans.push([{name, hyps: [], concl, sub: 0, insts: instsFor(models, one), uses: one}])
      continue
    }
    const plan: Planned[] = [{name, hyps: [], concl, sub: 1, insts: [], uses: [], cases: cases.map(c => andC(yesC, ...c.lits))}]
    for (const [i, c] of cases.entries()) {
      // The uses whose guard some model of the case meets (all, for a case no model reaches).
      const holdsIn = (g: C) => !c.models || c.models.some(({m, env}) => { try { return m.evalC(g, env) } catch { return true } })
      // A lemma's use where its read is the goal's read it matched, in every model of the case.
      const applies = (u: NodeSpec['uses'][number]) => { const at = matchedAt.get(u); return !at || !c.models || c.models.every(({m, env}) => { try { return m.evalE(at.goal, env) === m.evalE(at.lemma, env) } catch { return false } }) }
      const us = capUses(uses.filter(u => holdsIn(u.guard) && applies(u)))
      const ms = few(c.models ?? c.near ?? models)
      plan.push({name: `${name}, case ${i + 1}`, hyps: c.lits, concl, sub: 0, insts: reached(p, fs, instsFor(ms, us), [c.lits, concl, us.map(u => [u.guard, useConcl(u)]), shapesAt], ms), uses: us})
    }
    plans.push(plan)
  }
  // Placed: each member's node, then its cases; a main node with cases uses them, at rank (level, size, 1) above theirs.
  const offsets = plans.map((_, i) => base + plans.slice(0, i).reduce((n, q) => n + q.length, 0))
  for (const [mi, plan] of plans.entries()) {
    const mb = members[mi]!, size = !mb.on ? k(0) : mb.on.d === 'nat' ? ev(mb.on.v) : get(sizeMap(mb.on.d.name), ev(mb.on.v))
    // (level, the measure or the size, 0 or 1), the measure's place padded to the program's widest measure
    const comps = mb.rank ?? [size], mid = [...comps, ...Array.from({length: rankWidth(p) - comps.length}, () => k(0))]
    for (const {sub, cases, ...n} of plan) specs.push({...n, rank: [k(level), ...mid, k(sub)], uses: cases ? cases.map((g, i) => ({node: offsets[mi]! + 1 + i, subst: {}, guard: g})) : n.uses.map(u => (u.node < 0 ? {...u, node: offsets[-1 - u.node]!} : u))})
  }
  const name = title
  // Each attempt within its own time (a goal past it is left unknown, and the attempt fails).
  if (dataTrace) console.error(`[data] @${Math.round(performance.now())} ${l.name} (${scheme?.name}) depth ${depth}, ${lemmas.length} lemmas: built in ${Math.round(clock() - t0)} ms (counted), ${specs.length} nodes, ${specs.reduce((n, x) => n + x.insts.length, 0)} instances`)
  if (clock() > t0 + attemptMs.ms) return {verdict: {proven: false, checked: false, node: name, goal: name, stuck: 'unknown'}, specs, main: base}
  const was = pairedKeys.skip
  pairedKeys.skip = true
  try { return {verdict: withDeadline(t0 + attemptMs.ms, () => proveCyclic(fs.facts, specs)), specs, main: base} } finally { pairedKeys.skip = was }
}
export const attemptMs = {ms: 8000}
// A datatype search's budgets count work, not wall time (kernel/prove.ts's `counted`: the solver's rows and each node's),
// 300 units a millisecond: a search finds the same proof on any machine, at any load. On Modal (2 vCPU) the corpus's
// searches do 50 to 263 units a millisecond (`runs/modal/cover/data3`, data-cal), so a budget lets each do at least the
// work it did there in wall time.
const dataRate = 300
// A case node's instances, those its models reach: from every read of its conclusion and its uses' (and their guards),
// through each instance at a read reached (a function's at its call, a constructor's at its cell, a shape or eta at a
// value whose tag is read), the reads of what it gives where the models take it (an if's taken branch, an implication's
// conclusion where its premise holds); a congruence where both its reads are reached.
function reached(p: Program, fs: Facts, insts: NodeSpec['insts'], from: unknown[], ms: M[]): NodeSpec['insts'] {
  const reach = new Set<string>(), id = (t: E) => JSON.stringify(t)
  const active = (t: unknown, m: Model, env: Record<string, number>): void => {
    if (!t || typeof t !== 'object') return
    if (Array.isArray(t)) { t.forEach(x => active(x, m, env)); return }
    const o = t as E | C
    const truth = (c: C) => { try { return m.evalC(c, env) } catch { return undefined } }
    if (o.op === 'if') { active(o.c, m, env); const v = truth(o.c); if (v !== false) active(o.then, m, env); if (v !== true) active(o.else, m, env); return }
    if (o.op === 'or' && o.xs.length === 2 && o.xs[0]!.op === 'not') { active(o.xs[0], m, env); if (truth(o.xs[0]!.x) !== false) active(o.xs[1], m, env); return }
    if (o.op === 'get') reach.add(id(o))
    for (const v of Object.values(o)) active(v, m, env)
  }
  const each = (t: unknown) => { for (const {m, env} of ms) active(t, m, env) }
  // The conclusion and the uses' are read whole: the goal is where the law fails, which no model is.
  walk(from, o => { if (o.op === 'get') reach.add(JSON.stringify(o)) })
  const anchor = (q: NodeSpec['insts'][number]): E[] => {
    const name = fs.facts[q.fact]!.name
    if (name.startsWith('fn ')) return [get(name.slice(3), keyOf(q.at))]
    if (name.startsWith('ctor ')) return [get(name.slice(5), keyOf(q.at))]
    if (name.startsWith('arith ')) { const k2 = Number(name.slice(6)); return [get(divMap(k2), q.at[0]!), get(modMap(k2), q.at[0]!)] }
    if (name === 'zcode') return [get(posMap, q.at[0]!), get(negMap, q.at[0]!)]
    if (name.startsWith('shape ') || name.startsWith('eta ')) { const d = name.split(' ')[1]!; return [get(tagMap(d), q.at[0]!), get(sizeMap(d), q.at[0]!), ...p.datas.filter(x => x.name === d).flatMap(x => x.ctors.flatMap((c, j) => c.fields.map((_, i) => get(fieldMap(x, j, i), q.at[0]!))))] }
    return []
  }
  const kept = new Set<number>()
  // A constant's tag (the nullary facts) is read wherever its constant is.
  for (const [i, q] of insts.entries()) if (fs.facts[q.fact]!.name.startsWith('nullary ')) { kept.add(i); each(holdsAt(fs, q)) }
  for (let changed = true; changed;) {
    changed = false
    for (const [i, q] of insts.entries()) {
      if (kept.has(i)) continue
      const name = fs.facts[q.fact]!.name
      if (name.startsWith('cong ') || name.startsWith('nullary ')) continue
      const virtual = anchoredAt.get(JSON.stringify([q.fact, q.at])) ?? []
      const same = (v: {arg: E, value: E}) => ms.every(({m, env}) => { try { return m.evalE(v.arg, env) === m.evalE(v.value, env) } catch { return false } })
      if (!anchor(q).some(a => reach.has(id(a))) && !virtual.some(v => reach.has(v.read) && same(v))) continue
      kept.add(i); changed = true
      each(holdsAt(fs, q))
    }
  }
  return insts.filter((q, i) => {
    if (kept.has(i)) return true
    const name = fs.facts[q.fact]!.name
    if (name.startsWith('nullary ')) return true
    if (!name.startsWith('cong ')) return false
    const m = name.slice(5), n = q.at.length / 2
    return reach.has(id(get(m, keyOf(q.at.slice(0, n))))) && reach.has(id(get(m, keyOf(q.at.slice(n)))))
  })
}
// The uses of lemmas a goal's reads match: each lemma's largest reads (those inside no other) matched against the goal's
// reads of the same map at keys equal, by the instances' equations (every branch), to the read's key.
function lemmaUsesFor(p: Program, fs: Facts, lemmas: {law: DataLaw, node: number, concl: C}[], from: unknown[], insts: NodeSpec['insts'], models: M[] = []): NodeSpec['uses'] {
  const id = tid, parent = new Map<string, string>(), terms = new Map<string, E>()
  const find = (x: string): string => { let r = x; while (parent.has(r)) r = parent.get(r)!; return r }
  const union = (x: E, y: E) => { terms.set(id(x), x); terms.set(id(y), y); const a = find(id(x)), b = find(id(y)); if (a !== b) parent.set(a, b) }
  const leaves = (e: E): E[] => (e.op === 'if' ? [...leaves(e.then), ...leaves(e.else)] : [e])
  for (const q of insts) for (const [a, b] of equalities(holdsAt(fs, q))) for (const leaf of leaves(b)) union(a, leaf)
  // Closed under congruence (two reads of one map at arguments of one class), by signatures.
  const cells = new Map<string, {key: E, as: E[]}[]>()
  walk([from, insts.map(q => holdsAt(fs, q))], o => { if (o.op !== 'get') return; const n = fs.arity.get(o.map as string), as = n ? argsOf(o.key as E, n) : undefined; if (as) (cells.get(o.map as string) ?? cells.set(o.map as string, []).get(o.map as string)!).push({key: o.key as E, as}) })
  for (let changed = true, rounds = 0; changed && rounds < 8; rounds++) {
    changed = false
    for (const [map, list] of cells) {
      const bySig = new Map<string, E>()
      for (const x of list) {
        const sig = x.as.map(t => find(id(t))).join('\u0001'), y = bySig.get(sig), cx = get(map, x.key)
        if (!y) { bySig.set(sig, cx); continue }
        if (find(id(y)) !== find(id(cx))) { union(y, cx); changed = true }
      }
    }
  }
  const classes = new Map<string, E[]>()
  for (const [key, e] of terms) { const r = find(key); (classes.get(r) ?? classes.set(r, []).get(r)!).push(e) }
  const members = (t: E): E[] => { const k0 = tid(t); return [t, ...(classes.get(find(k0)) ?? []).filter(e => tid(e) !== k0)] }
  const out: NodeSpec['uses'] = [], seen = new Set<string>()
  let reads: E[] = []
  walk([from, insts.map(q => holdsAt(fs, q))], o => { if (o.op === 'get') reads.push(o as unknown as E) })
  for (let round = 0; round < 2; round++) {
    const fresh: E[] = []
    // The candidates of a round, each scored by the models where the lemma's read is the goal's (a match through every
    // branch's classes holds only in some), two that give the lemma's variables the same values in every model one.
    type Cand = {use: NodeSpec['uses'][number], at: {goal: E, lemma: E}, score: number, fp: string, size: number}
    const cands: Cand[] = []
    // The newest lemma first (the one the law is tried again for).
    for (const lm of [...lemmas].reverse()) {
      if (round > 0 && out.some(u => u.node === lm.node)) continue
      const vars = new Set(lm.law.vars.map(v => v.name)), sides: E[] = []
      walk(encY(p, lm.law.holds, new Map()), o => { if (o.op === 'get') sides.push(o as unknown as E) })
      const tops = sides.filter(a => !sides.some(b => b !== a && JSON.stringify(b).includes(JSON.stringify(a)))) as Extract<E, {op: 'get'}>[]
      for (const top of tops) for (const t of reads) {
        if (t.op !== 'get' || t.map !== top.map) continue
        // Each argument of the read matched up to its class (a key of several arguments is their pairing).
        const n = fs.arity.get(top.map) ?? 1, pats = argsOf(top.key, n), args = argsOf(t.key, n)
        if (!pats || !args) continue
        let subs: Record<string, E>[] = [{}]
        for (const [q, pat] of pats.entries()) subs = subs.flatMap(sb => members(args[q]!).slice(0, 256).flatMap(m => { const r = matches(pat, vars, m, sb); return r ? [r] : [] })).slice(0, 512)
        for (const sub of subs) {
          if (Object.keys(sub).length !== vars.size) continue
          // Where a model gives the lemma's arguments the goal read's (a match through every branch's classes may be none).
          const there = pats.map(a => substE(a, {vars: sub, maps: {}, flags: {}}))
          const score = models.length ? models.filter(({m, env}) => { try { return there.every((a, q) => m.evalE(a, env) === m.evalE(args[q]!, env)) } catch { return false } }).length : 1
          if (!score) continue
          const k2 = JSON.stringify([lm.node, sub])
          if (seen.has(k2)) continue
          seen.add(k2)
          const names = Object.keys(sub).sort()
          const fp = models.length ? JSON.stringify([lm.node, models.map(({m, env}) => names.map(x => { try { return m.evalE(sub[x]!, env) } catch { return -1 } }))]) : k2
          cands.push({use: {node: lm.node, subst: sub, guard: yesC}, at: {goal: t, lemma: substE(top, {vars: sub, maps: {}, flags: {}})}, score, fp, size: k2.length})
        }
      }
    }
    // First, as found: four of a lemma, twelve in all (the next round reads their conclusions). Then the rest, best first
    // (the most models, then the smallest terms), one of each set of values, up to `perLemma` of a lemma and `total` in
    // all: a case node keeps those its models meet, `perCase` of a lemma (attempt's `applies`), so a use that holds in
    // one case only (the insertion's other side) isn't crowded out by those found first.
    const fps = new Set<string>(), first = new Set<Cand>()
    const take = (c: Cand) => { fps.add(c.fp); out.push(c.use); matchedAt.set(c.use, c.at) }
    for (const c of cands) {
      if (out.length >= 12 || out.filter(u => u.node === c.use.node).length >= 4) continue
      take(c); first.add(c)
      walk(substC(lemmas.find(lm => lm.node === c.use.node)!.concl, {vars: c.use.subst, maps: {}, flags: {}}), o => { if (o.op === 'get') fresh.push(o as unknown as E) })
    }
    const rest = cands.filter(c => !first.has(c)).sort((a, b) => b.score - a.score || a.size - b.size)
    for (const c of rest) if (!fps.has(c.fp) && out.length < lemmaCaps.total && out.filter(u => u.node === c.use.node).length < lemmaCaps.perLemma) take(c)
    reads = fresh
  }
  return out
}
// How many uses of lemmas a goal gets: the candidates kept (`perLemma` of each lemma, `total`), and of those a case node
// keeps (`perCase` of each lemma, those its models meet).
export const lemmaCaps = {perLemma: 8, total: 24, perCase: 4}
// A node's uses: the scheme's (the cycle's, read at nodes not yet placed) all, `perCase` of each lemma, `total` lemma
// uses in all, in the order given.
function capUses(uses: NodeSpec['uses'], total = Infinity): NodeSpec['uses'] {
  const per = new Map<number, number>()
  let all = 0
  return uses.filter(u => {
    if (u.node < 0) return true
    const n = per.get(u.node) ?? 0
    if (n >= lemmaCaps.perCase || all >= total) return false
    per.set(u.node, n + 1); all++
    return true
  })
}
// The equalities a condition may give: those in a positive place (a conjunction's parts, a disjunction's disjuncts that
// aren't negations, so an implication's conclusion and never its premise).
function equalities(c: C): [E, E][] {
  if (c.op === '=') return [[c.a, c.b]]
  if (c.op === 'and' || c.op === 'or') return c.xs.flatMap(x => (x.op === 'not' ? [] : equalities(x)))
  return []
}
// A lemma use: the goal's read it matched, and the lemma's read there (equal where the use applies).
const matchedAt = new WeakMap<object, {goal: E, lemma: E}>()
const holdsAt = (fs: Facts, q: {fact: number, at: E[]}) => { const f = fs.facts[q.fact]!; return substC(f.holds, {vars: Object.fromEntries(f.keys.map((key, i) => [key, q.at[i]!])), maps: {}, flags: {}}) }

// The models a search compares terms in: random values of the law's variables.
function modelsFor(p: Program, l: DataLaw, n: number, seed: number) {
  return samples(l.vars, p.params, n, seed).map(s => {
    const m = new Model(p, s.params)
    const env = Object.fromEntries(l.vars.map(v => [v.name, m.code(v.sort, s.env.get(v.name)!)]))
    return {m, env}
  })
}

// Prove a law with the lemmas given (each proven, with its nodes), trying each scheme at each depth.
// `without`: 'plain', the law with no induction where no scheme applies; 'cases', no induction, then by the cases of
// each variable (a natural's zero and successor, a datatype's constructors), none of them using the law again.
function proveWith(p: Program, fs: Facts, l: DataLaw, lemmas: Proven[], level: number, opts: Options, until: number, per: number, depths: number[], without?: 'plain' | 'cases'): {out?: Proven, verdict?: CyclicVerdict, scheme?: string, tried: number, last?: CyclicVerdict} {
  const models = modelsFor(p, l, 240, opts.seed ?? 3)
  let tried = 0, last: CyclicVerdict | undefined
  const cases = l.vars.flatMap((v): Scheme[] => (v.sort === 'nat' || v.sort instanceof Data ? [{name: `cases of ${v.name}`, on: {v: v.name, d: v.sort}, uses: []}] : []))
  const found = opts.induction === false || without === 'cases' ? [] : schemes(p, l)
  const ss: (Scheme | undefined)[] = opts.induction === false ? [undefined] : without === 'cases' ? [undefined, ...cases] : without === 'plain' && !found.length ? [undefined] : found
  for (const depth of depths.filter(d => d <= (opts.depth ?? 3))) for (const s of ss) {
    if (clock() > until) return {tried, last}
    tried++
    const {verdict, specs, main} = (attemptMs.ms = Math.min(per * (opts.patience ?? 1), until - clock()), attempt(p, fs, l, s, depth, lemmas, level, models))
    last = verdict
    if (verdict.proven && verdict.checked) return {out: {law: l, spec: specs[main]!, nodes: specs}, verdict, scheme: s?.name ?? (without ? 'no induction' : undefined), tried}
  }
  return {tried, last}
}

// Conjectures from the values (theory exploration): equations between terms of the law's functions over a few
// variables (two of each datatype, two naturals; constructors, the functions, sums of naturals, up to five symbols), met
// by every random value, smallest first, each named canonically (its variables in order of appearance), none ground,
// none the law, none that follows by rewriting with smaller ones; and for each predicate the law reads, that a function
// returning a datatype keeps it (p(x) implies p(f(x, ...)), under a comparison of two naturals where that is needed).
export function conjectures(p: Program, l: DataLaw, max = 24, maxSize = 6): DataLaw[] {
  const sortsOf = (s: Sort) => (s instanceof Data ? s.name : s)
  const vars: {name: string, sort: Sort}[] = [...p.datas.flatMap(d => [{name: `${d.name.toLowerCase()}1`, sort: d as Sort}, {name: `${d.name.toLowerCase()}2`, sort: d as Sort}]), {name: 'n1', sort: 'nat'}, {name: 'n2', sort: 'nat'}]
  const sortOfVar = new Map(vars.map(v => [v.name, v.sort]))
  const ss = samples(vars, p.params, 80, 11)
  type T = {x: X, sort: Sort, size: number}
  const used = new Set<string>(); walk(l.holds, o => { if (o.op === 'call') used.add(o.fn as string) })
  const callees = (f: Fn): string[] => { const out: string[] = []; walk(f.body(), o => { if (o.op === 'call') out.push(o.fn as string) }); return out }
  for (let changed = true; changed;) { changed = false; for (const f of p.fns) if (used.has(f.name)) for (const g of callees(f)) if (!used.has(g)) { used.add(g); changed = true } }
  const fnsUsed = p.fns.filter(f => used.has(f.name))
  const fp = (x: X): string | undefined => { try { return JSON.stringify(ss.map(s => evalX(x, s.env, s.params))) } catch { return undefined } }
  const classes = new Map<string, T[]>()
  const addT = (t: T) => { const f = fp(t.x); if (f === undefined) return; const key = `${sortsOf(t.sort)}:${f}`; const c = classes.get(key) ?? []; c.push(t); classes.set(key, c) }
  for (const v of vars) addT({x: {op: 'var', name: v.name}, sort: v.sort, size: 1})
  addT({x: {op: 'nat', value: 0}, sort: 'nat', size: 1})
  for (const d of p.datas) d.ctors.forEach((c, j) => { if (!c.fields.length) addT({x: {op: 'ctor', data: d.name, ctor: j, args: []}, sort: d, size: 1}) })
  for (let size = 2; size <= maxSize; size++) {
    const reps = [...classes.values()].map(c => [...c].sort((a, b) => a.size - b.size)[0]!)
    const build = (sorts: Sort[], budget: number): T[][] => {
      if (!sorts.length) return budget === 0 ? [[]] : []
      const out: T[][] = []
      for (const t of reps) if (sortsOf(t.sort) === sortsOf(sorts[0]!) && t.size <= budget - (sorts.length - 1)) for (const rest of build(sorts.slice(1), budget - t.size)) out.push([t, ...rest])
      return out
    }
    for (const f of fnsUsed) for (const args of build(f.params.map(q => q.sort), size - 1)) addT({x: {op: 'call', fn: f.name, args: args.map(a => a.x)}, sort: f.ret, size})
    for (const d of p.datas) d.ctors.forEach((c, j) => { if (c.fields.length) for (const args of build(c.fields.map(f => fieldSort(f)), size - 1)) addT({x: {op: 'ctor', data: d.name, ctor: j, args: args.map(a => a.x)}, sort: d, size}) })
    for (const [a2, b2] of build(['nat', 'nat'], size - 1)) if (JSON.stringify(a2!.x) <= JSON.stringify(b2!.x)) addT({x: {op: 'add', a: a2!.x, b: b2!.x}, sort: 'nat', size})
    if (classes.size > 6000) break
  }
  // Canonical names: each sort's variables renamed in order of appearance.
  const canon = (t: unknown): {t: unknown, vs: Set<string>} => {
    const order: string[] = []
    walk(t, o => { if (o.op === 'var' && sortOfVar.has(o.name as string) && !order.includes(o.name as string)) order.push(o.name as string) })
    const count = new Map<string, number>(), ren = new Map<string, string>()
    for (const v of order) { const s2 = sortOfVar.get(v)!, key = s2 instanceof Data ? s2.name.toLowerCase() : 'n', i = (count.get(key) ?? 0) + 1; count.set(key, i); ren.set(v, `${key}${i}`) }
    const go = (x: unknown): unknown => (Array.isArray(x) ? x.map(go) : x && typeof x === 'object' ? ((x as {op?: string}).op === 'var' && ren.has((x as {name: string}).name) ? {op: 'var', name: ren.get((x as {name: string}).name)} : Object.fromEntries(Object.entries(x).map(([key, v]) => [key, go(v)]))) : x)
    return {t: go(t), vs: new Set(ren.values())}
  }
  const callIn = (x: X) => JSON.stringify(x).includes('"op":"call"')
  const size = (x: unknown): number => { let n = 0; walk(x, o => { if (['var', 'nat', 'call', 'ctor', 'add'].includes(o.op as string)) n++ }); return n }
  const eqs: {a: X, b: X, size: number}[] = []
  for (const c of classes.values()) {
    const ts = [...c].sort((a, b) => a.size - b.size), rep = ts[0]!
    const repVars = new Set<string>(); walk(rep.x, o => { if (o.op === 'var') repVars.add(o.name as string) })
    for (const t of ts.slice(1)) {
      if (!callIn(t.x)) continue
      const tv = new Set<string>(); walk(t.x, o => { if (o.op === 'var') tv.add(o.name as string) })
      if (![...repVars].every(v => tv.has(v))) continue
      const {t: ct} = canon([t.x, rep.x]), [ca, cb] = ct as [X, X]
      eqs.push({a: ca, b: cb, size: t.size + rep.size})
    }
  }
  // Smallest first, and of one size the most general first (an instance of a kept one is then dropped).
  const nvars = (e: {a: X, b: X}) => { const vs = new Set<string>(); walk(e, o => { if (o.op === 'var') vs.add(o.name as string) }); return vs.size }
  eqs.sort((a, b) => a.size - b.size || nvars(b) - nvars(a))
  // Rewriting with the equations kept, each oriented from its larger side; one that rewrites to itself is dropped.
  type Rule = {l: X, r: X, vs: Set<string>}
  const rules: Rule[] = []
  const matchX = (pat: X, t: X, vs: Set<string>, sub: Map<string, X>): boolean => {
    if (pat.op === 'var' && vs.has(pat.name)) { const had = sub.get(pat.name); if (had) return JSON.stringify(had) === JSON.stringify(t); sub.set(pat.name, t); return true }
    if (pat.op !== t.op) return false
    const po = pat as Record<string, unknown>, to = t as Record<string, unknown>
    for (const key of Object.keys(po)) {
      const a2 = po[key], b2 = to[key]
      if (Array.isArray(a2)) { if (!Array.isArray(b2) || a2.length !== b2.length || !a2.every((x, i) => matchX(x as X, b2[i] as X, vs, sub))) return false }
      else if (a2 && typeof a2 === 'object') { if (!b2 || typeof b2 !== 'object' || !matchX(a2 as X, b2 as X, vs, sub)) return false }
      else if (a2 !== b2) return false
    }
    return true
  }
  const substX = (x: X, sub: Map<string, X>): X => JSON.parse(JSON.stringify(x), (_, v) => (v && typeof v === 'object' && v.op === 'var' && sub.has(v.name) ? sub.get(v.name) : v))
  const norm = (x: X, depth = 0): X => {
    if (depth > 30) return x
    let t: X = JSON.parse(JSON.stringify(x))
    if (t.op === 'call' || t.op === 'ctor') t = {...t, args: t.args.map(a2 => norm(a2, depth + 1))}
    if (t.op === 'add') { const [a2, b2] = [norm(t.a, depth + 1), norm(t.b, depth + 1)]; if (a2.op === 'nat' && a2.value === 0) return b2; if (b2.op === 'nat' && b2.value === 0) return a2; t = JSON.stringify(a2) <= JSON.stringify(b2) ? {op: 'add', a: a2, b: b2} : {op: 'add', a: b2, b: a2} }
    for (const r of rules) { const sub = new Map<string, X>(); if (matchX(r.l, t, r.vs, sub)) return norm(substX(r.r, sub), depth + 1) }
    return t
  }
  // The law in the same names (its variables by sort, in order of appearance).
  const lawText = (() => {
    const count = new Map<string, number>(), ren = new Map<string, string>()
    walk(l.holds, o => { if (o.op === 'var' && !ren.has(o.name as string)) { const v = l.vars.find(w => w.name === o.name); if (!v) return; const key = v.sort instanceof Data ? v.sort.name.toLowerCase() : 'n', i = (count.get(key) ?? 0) + 1; count.set(key, i); ren.set(v.name, `${key}${i}`) } })
    return JSON.stringify(l.holds, (_, v) => (v && typeof v === 'object' && v.op === 'var' && ren.has(v.name) ? {op: 'var', name: ren.get(v.name)} : v))
  })()
  const out: DataLaw[] = [], seen = new Set<string>()
  const lawOf = (y: Y, vs: Set<string>, name: string): DataLaw => ({name, vars: [...vs].map(v => ({name: v, sort: sortOfVar.get(v)!})), holds: y, params: [...new Set(paramsIn(y))]})
  const kept: {a: X, b: X, vs: Set<string>}[] = []
  // The definitions, unfolded at a constructor: f(.., C(x, y), ..) → its case's body, where that is a plain term.
  for (const f of fnsUsed) {
    // (a structural function's decreasing parameter, a well-founded one's the body matches on first)
    const body = f.body(), top = body.op === 'match' && body.of.op === 'var' ? f.params.findIndex(q => `${f.name}.${q.name}` === (body.of as {name: string}).name) : -1
    const di = f.decreases ?? (f.measure ? top : -1)
    if (body.op !== 'match' || di < 0 || di !== top) continue
    const d = f.params[di]!.sort as Data
    body.cases.forEach((c, j) => {
      if (JSON.stringify(c.body).match(/"op":"(match|if|bool|apply)"/)) return
      const names = new Map<string, X>(f.params.map((q, i) => [`${f.name}.${q.name}`, {op: 'var', name: `$p${i}`} as X]))
      c.binds.forEach((b, i) => names.set(b, {op: 'var', name: `$f${i}`}))
      const ren = (x: X): X => JSON.parse(JSON.stringify(x), (_, v) => (v && typeof v === 'object' && v.op === 'var' && names.has(v.name) ? names.get(v.name) : v))
      const lhs: X = {op: 'call', fn: f.name, args: f.params.map((_, i) => (i === di ? {op: 'ctor', data: d.name, ctor: j, args: c.binds.map((_, q) => ({op: 'var', name: `$f${q}`} as X))} : {op: 'var', name: `$p${i}`} as X))}
      const vs = new Set<string>(); walk(lhs, o => { if (o.op === 'var') vs.add(o.name as string) })
      rules.push({l: lhs, r: ren(c.body), vs})
    })
  }
  const lawY = JSON.parse(lawText) as Y
  if (lawY.op === '=') { const vs = new Set<string>(); walk(lawY, o => { if (o.op === 'var') vs.add(o.name as string) }); const [big, small] = size(lawY.a) >= size(lawY.b) ? [lawY.a, lawY.b] : [lawY.b, lawY.a]; if (size(big) > size(small)) rules.push({l: big, r: small, vs}) }
  for (const e of eqs) {
    const na = norm(e.a), nb = norm(e.b)
    if (JSON.stringify(na) === JSON.stringify(nb)) continue
    // An instance of one kept (both sides at one substitution) adds nothing.
    if (kept.some(q => [[q.a, q.b], [q.b, q.a]].some(([x1, x2]) => { const sub = new Map<string, X>(); return matchX(x1!, e.a, q.vs, sub) && matchX(x2!, e.b, q.vs, sub) }))) continue
    const y: Y = {op: '=', a: e.a, b: e.b}, text = JSON.stringify(y)
    if (seen.has(text) || text === lawText || JSON.stringify({op: '=', a: e.b, b: e.a}) === lawText) continue
    seen.add(text)
    const vs = new Set<string>(); walk(y, o => { if (o.op === 'var') vs.add(o.name as string) })
    // A ground equation only rewrites (a definition unfolded proves it where it is needed).
    if (vs.size && out.length < max) out.push(lawOf(y, vs, `${showX(e.a)} = ${showX(e.b)}`))
    kept.push({a: e.a, b: e.b, vs})
    const [big, small] = size(e.a) >= size(e.b) ? [e.a, e.b] : [e.b, e.a]
    if (size(big) > size(small)) rules.push({l: big, r: small, vs})
  }
  // Predicates kept by a function returning a datatype.
  const preds = p.fns.filter(f => f.ret === 'bool' && used.has(f.name)), makers = p.fns.filter(f => f.ret instanceof Data && used.has(f.name))
  const nats = vars.filter(v => v.sort === 'nat').map(v => v.name)
  for (const pr of preds) for (const mk of makers) {
    const di = pr.params.findIndex(q => q.sort === mk.ret)
    if (di < 0) continue
    const dvar = vars.find(v => v.sort === mk.ret)!.name
    const argSets = (qs: {sort: Sort}[]): X[][] => qs.reduce<X[][]>((acc, q) => acc.flatMap(a2 => (q.sort === 'nat' ? nats.map(n => [...a2, {op: 'var', name: n} as X]) : q.sort === 'bool' ? [] : [[...a2, {op: 'var', name: vars.find(v => v.sort === q.sort)!.name} as X]])), [[]])
    for (const margs of argSets(mk.params)) for (const pargs of argSets(pr.params.filter((_, i) => i !== di))) {
      const pAt = (x: X): Y => { const as = [...pargs]; as.splice(di, 0, x); return {op: 'holds', x: {op: 'call', fn: pr.name, args: as}} }
      const premise = pAt({op: 'var', name: dvar}), conclusion = pAt({op: 'call', fn: mk.name, args: margs})
      const conds: (Y | undefined)[] = [undefined, ...nats.flatMap(a2 => nats.filter(b2 => b2 !== a2).flatMap(b2 => [{op: '<', a: {op: 'var', name: a2}, b: {op: 'var', name: b2}} as Y, {op: '<=', a: {op: 'var', name: a2}, b: {op: 'var', name: b2}} as Y]))]
      for (const c of conds) {
        const hyp: Y = c ? {op: 'and', xs: [premise, c]} : premise
        const {t: cy, vs} = canon({op: 'or', xs: [{op: 'not', x: hyp}, conclusion]})
        const y = cy as Y, text = JSON.stringify(y)
        if (seen.has(text) || text === lawText) break
        let held = 0, ok = true
        for (const sm of ss) { try { if (evalY(hyp, sm.env, sm.params)) { held++; if (!evalY(conclusion, sm.env, sm.params)) { ok = false; break } } } catch { ok = false; break } }
        if (ok && held >= 5) { seen.add(text); out.push(lawOf(y, vs, `${showY((y as {xs: Y[]}).xs[0]!.op === 'not' ? ((y as {xs: Y[]}).xs[0] as {x: Y}).x : y)} implies ${showY((y as {xs: Y[]}).xs[1]!)}`)); break }
      }
    }
  }
  return out
}
export const showX = (x: X): string => {
  switch (x.op) {
    case 'var': return x.name.replace(/#\d+$/, '')
    case 'nat': return String(x.value)
    case 'add': return `${showX(x.a)} + ${showX(x.b)}`
    case 'sub': return `${showX(x.a)} − ${showX(x.b)}`
    case 'min': case 'max': return `${x.op}(${showX(x.a)}, ${showX(x.b)})`
    case 'mul': return `${x.k}·${showX(x.a)}`
    case 'prod': return `${showX(x.a)}·${showX(x.b)}`
    case 'mod': case 'imod': return `${showX(x.a)} mod ${x.k}`
    case 'div': case 'idiv': return `${showX(x.a)} div ${x.k}`
    case 'int': return String(x.value)
    case 'iadd': return `${showX(x.a)} + ${showX(x.b)}`
    case 'isub': return `${showX(x.a)} − ${showX(x.b)}`
    case 'ineg': return `−${showX(x.a)}`
    case 'imul': return `${x.k}·${showX(x.a)}`
    case 'ofnat': return showX(x.a)
    case 'if': return `if ${showY(x.c)} then ${showX(x.then)} else ${showX(x.else)}`
    case 'bool': return showY(x.c)
    case 'apply': return `${x.param}(${showX(x.arg)})`
    case 'size': return `size(${showX(x.of)})`
    case 'call': return `${x.fn}(${x.args.map(showX).join(', ')})`
    case 'ctor': { const d = [...fns.values()].length >= 0 ? x.data : x.data; return `${d}.${x.ctor}${x.args.length ? `(${x.args.map(showX).join(', ')})` : ''}` }
    case 'match': return `match ${showX(x.of)}`
    case 'natmatch': return `match ${showX(x.of)}`
  }
}
export const showY = (y: Y): string => {
  switch (y.op) {
    case '<': case '<=': case '=': return `${showX(y.a)} ${y.op} ${showX(y.b)}`
    case 'i<': case 'i<=': return `${showX(y.a)} ${y.op.slice(1)} ${showX(y.b)}`
    case 'and': return y.xs.map(showY).join(' and ')
    case 'or': return y.xs.map(showY).join(' or ')
    case 'not': return `not (${showY(y.x)})`
    case 'is': return `${showX(y.of)} is ${y.ctor}`
    case 'holds': return showX(y.x)
  }
}

// Prove a law over datatypes: refuted by a random value where one breaks it; else proven by a cycle the search finds,
// with lemmas found from the values when the law alone isn't (`lemmas: false` turns that off; an array gives lemmas to
// prove and use instead, which the corpus never does).
export function proveData(l: DataLaw, opts: Options = {}): DataVerdict { return counted(dataRate, () => bounded(() => proveDataCounted(l, opts))) }
function proveDataCounted(l: DataLaw, opts: Options): DataVerdict {
  const t0 = performance.now(), until = clock() + (opts.ms ?? 120_000)
  // Where the law calls a non-recursive function, or reaches a recursive one that agrees with a built-in (core/transfer.ts):
  // the law alone at one unfolding first, then the law said through them, then the rest of the search on the law.
  const plan = opts.transfer === false || opts.induction === false || Array.isArray(opts.lemmas) ? undefined : transferPlan(l)
  if (!plan) return searchIn(l, opts, until).verdict
  const quick = searchIn(l, opts, until, undefined, 'first').verdict
  if (quick.proven || quick.counterexample) return quick
  // (a law said through its definitions past what the encoding's terms take is left as stated)
  let through: ReturnType<typeof proveThrough>
  try { through = proveThrough(l, plan, opts, until) } catch (e) { if (!(e instanceof RangeError)) throw e }
  if (through?.proven) return {...through, ms: Math.round(performance.now() - t0)}
  const rest = searchIn(l, opts, until, undefined, 'rest').verdict
  return {...rest, tried: rest.tried + quick.tried + (through?.tried ?? 0), ms: Math.round(performance.now() - t0), ...(rest.goal || rest.proven ? {} : {goal: quick.goal, stuck: quick.stuck})}
}
// The search on a law: in its own program, or (`ctx`) in one given, above lemmas proven before in it (`base`, its nodes at
// levels up to `level`), where `out` is the proof's nodes, for a proof that reads it (core/transfer.ts). `phase`: 'first'
// is the refutation and the law alone at one unfolding, 'rest' all after those.
export type SearchCtx = {p: Program, fs: Facts, base: Proven[], level: number}
export function searchIn(l: DataLaw, opts: Options, until: number, ctx?: SearchCtx, phase: 'all' | 'first' | 'rest' = 'all'): {verdict: DataVerdict, out?: Proven} {
  const t0 = performance.now(), w0 = work.n
  const p = ctx?.p ?? programOf([l, ...(Array.isArray(opts.lemmas) ? opts.lemmas : [])]), fs = ctx?.fs ?? factsOf(p)
  const base = ctx?.base ?? [], lv = ctx?.level ?? 0
  let out: Proven | undefined
  const done = (v: Omit<DataVerdict, 'ms' | 'law'>): {verdict: DataVerdict, out?: Proven} => {
    if (dataTrace) console.error(`[data] ${l.name}: ${work.n - w0} units of work in ${Math.round(performance.now() - t0)} ms`)
    return {verdict: {law: l.name, ...v, ms: Math.round(performance.now() - t0)}, out}
  }
  if (phase !== 'rest') {
    const cex = refute(l, opts.samples ?? 400)
    if (cex) return done({proven: false, checked: false, counterexample: cex, lemmas: [], tried: 0})
  }
  // The law alone at one unfolding; then lemmas at one unfolding each (the law tried again after each its goal
  // matches); then the law at two; then lemmas at two; last the law at three, and without induction (by cases). A lemma
  // is named in the verdict when the proof uses it.
  let tried = 0
  const used = (r: NonNullable<ReturnType<typeof proveWith>['out']>, lemmas: Proven[]) => {
    const nodes = r.nodes, seen = new Set<number>(), todo = [nodes.indexOf(r.spec)]
    while (todo.length) { const i = todo.pop()!; if (seen.has(i)) continue; seen.add(i); for (const u of nodes[i]!.uses) todo.push(u.node) }
    return lemmas.filter(q => seen.has(nodes.indexOf(nodes.find(n => n.name === q.spec.name)!))).map(q => q.law.name)
  }
  const ok = (r: ReturnType<typeof proveWith>, lemmas: Proven[], prog = p) => (tried += r.tried, r.out ? (out = r.out, done({proven: true, checked: true, proof: r.verdict, lemmas: used(r.out, lemmas), scheme: r.scheme, tried, program: prog, node: r.out.nodes.indexOf(r.out.spec)})) : undefined)
  // A law that calls no function (arithmetic alone: an integer's, a remainder's) has nothing to induct on: its cases.
  if (phase !== 'rest' && opts.induction !== false && !JSON.stringify(l.holds).includes('"op":"call"')) { const c = ok(proveWith(p, fs, l, base, lv + 1, opts, until, 3000, [1, 2], 'cases'), base); if (c) return c }
  const first = phase === 'rest' ? undefined : proveWith(p, fs, l, base, lv + 1, opts, until, 6000, [1], 'plain')
  const one = first && ok(first, base)
  if (one) return one
  if (phase === 'first') return done({proven: false, checked: false, lemmas: [], tried, ...stuckOf(first!.last)})
  const without = opts.lemmas === false || opts.induction === false
  if (without) return ok(proveWith(p, fs, l, base, lv + 1, opts, until, 20000, [2, 3]), base) ?? (opts.induction === false ? undefined : ok(proveWith(p, fs, l, base, lv + 1, opts, until, 3000, [1, 2], 'cases'), base)) ?? done({proven: false, checked: false, lemmas: [], tried, ...stuckOf(first?.last)})
  const cands = Array.isArray(opts.lemmas) ? opts.lemmas : conjectures(p, l)
  const p2 = ctx ? p : programOf([l, ...cands]), fs2 = ctx ? fs : factsOf(p2)
  // Each scheme's goals: the law's, and each companion's (a lemma may be what only a companion's goal reads).
  const goalOf = (law: DataLaw, uses: SchemeUse[], on: Scheme['on'], concls: C[], shapes?: E[]) => {
    const concl = encY(p2, law.holds, new Map()), ihc = uses.map(u => substC(concls[u.member ?? 0] ?? concl, {vars: u.subst, maps: {}, flags: {}}))
    return {from: [concl, ihc], insts: instancesOf(p2, fs2, {roots: [concl], others: ihc, depth: 2, shapesAt: shapes ?? (on && on.d !== 'nat' ? [ev(on.v)] : []), etaAt: [], models: []})}
  }
  const goals = schemes(p2, l).flatMap(s => {
    const all = [{law: l, uses: s.uses, on: s.on, shapes: s.shapes}, ...(s.companions ?? [])], concls = all.map(m => encY(p2, m.law.holds, new Map()))
    return all.map((m, i) => goalOf(m.law, m.uses.map(u => ({...u, member: u.member ?? i})), m.on, concls, 'shapes' in m ? m.shapes : undefined))
  })
  const matchesGoal = (c: DataLaw) => goals.some(g => lemmaUsesFor(p2, fs2, [{law: c, node: 0, concl: encY(p2, c.holds, new Map())}], g.from, g.insts).length > 0)
  // Those the goal matches first, of those the ones of the law's shape (an implication for an implication) first.
  const implication = (y: Y) => y.op === 'or' && y.xs.length === 2 && y.xs[0]!.op === 'not'
  const score = (c: DataLaw, hit: boolean) => (hit ? 2 : 0) + (implication(c.holds) === implication(l.holds) ? 1 : 0)
  if (dataTrace) console.error(`[data] ${l.name}: ${cands.length} conjectures at ${Math.round(clock())} of ${Math.round(until)}`)
  const ranked = cands.map(c => ({c, hit: matchesGoal(c)})).sort((a, b) => score(b.c, b.hit) - score(a.c, a.hit))
  // The lemmas proven: those given (`base`) and those found, each found one a level above the last.
  const proven: Proven[] = [...base], failed = new Set<DataLaw>(), level = () => lv + 1 + proven.length - base.length
  const lemmasAt = (depth: number) => {
    for (const {c, hit} of ranked) {
      if (clock() > until) return undefined
      if (proven.some(q => q.law === c) || (depth === 2 && !failed.has(c)) || refute(c, 200)) continue
      const r = proveWith(p2, fs2, c, proven, level(), opts, Math.min(until, clock() + (depth === 1 ? 8000 : 12000) * (opts.patience ?? 1)), 5000, [depth])
      tried += r.tried
      if (!r.out) { failed.add(c); continue }
      failed.delete(c)
      proven.push(r.out)
      if (!hit && implication(c.holds) !== implication(l.holds)) continue
      const again = ok(proveWith(p2, fs2, l, proven, level(), opts, until, 6000, depth === 1 ? [1] : [1, 2]), proven, p2)
      if (again) return again
    }
    return undefined
  }
  const steps: (() => ReturnType<typeof done> | undefined)[] = [
    () => lemmasAt(1),
    () => ok(proveWith(p, fs, l, base, lv + 1, opts, until, 30000, [2]), base),
    () => (proven.length > base.length ? ok(proveWith(p2, fs2, l, proven, level(), opts, until, 30000, [2]), proven, p2) : undefined),
    () => lemmasAt(2),
    () => ok(proveWith(p2, fs2, l, proven, level(), opts, until, 12000, [3]), proven, p2),
    // No induction: the law by the cases of a variable (or none), its definitions unfolded.
    () => ok(proveWith(p, fs, l, base, lv + 1, opts, until, 3000, [1, 2], 'cases'), base),
  ]
  for (const [i, step] of steps.entries()) { if (clock() > until) break; if (dataTrace) console.error(`[data] ${l.name}: step ${i} at ${Math.round(clock())} of ${Math.round(until)}`); const r = step(); if (r) return r }
  return done({proven: false, checked: false, lemmas: [], tried, ...stuckOf(first?.last)})
}
const stuckOf = (v?: CyclicVerdict) => (v && !v.proven ? {goal: v.goal, stuck: v.stuck} : v && !v.checked ? {goal: 'check', stuck: v.why} : {})

// The law with no cycle: its definitions unfolded, the kernel's prover alone (what the library proves without the search).
export const proveDataToday = (l: DataLaw): DataVerdict => proveData(l, {induction: false})
