// Recursive datatypes as values, proven by cyclic proofs. Untrusted: this file states facts and nodes, kernel/prove.ts
// grows a tree for every goal, and kernel/cyclic.ts checks the whole, as for every cyclic proof (nothing here is new to
// the kernel). Lean's twin of a proof (lean-kernel/Data.lean and the export's own definitions) is about the datatype as
// declared: a Lean `inductive`, the functions by pattern matching, the law over them.
//
// The encoding: every natural is a value of every datatype (a bijection between the naturals and the datatype's values,
// which Lean's twin defines and proves), so a value is a natural and two values are equal exactly when they are the same
// natural. A datatype D is read through maps: `D.tag[x]` (which constructor), `D.<ctor>.<field>[x]` (its fields, 0 under
// another constructor), `D.size[x]` (1 plus the sizes of its fields of type D: the rank). A constructor of no field is
// the constant of its tag; one with fields is a map read at its fields (`D.<ctor>[key]`); a function is a map read at
// its arguments; several arguments are read at their pairing, left-nested (a + b)² + b, as the library reads a function
// of several arguments (core/dsl.ts's argsKey). The facts, each at every value of its keys:
//   - the shape: D.tag[x] is a constructor's tag, and under tag j, D.size[x] = 1 + the sizes of x's fields of type D
//   - eta: under tag j, x is constructor j at its own fields (every natural is a value)
//   - each constructor: D.tag[C[key]] = j and each field of C[key] is its argument
//   - each function: f[key] = its body, a match read as ifs on the tag, a field bound by a case read from its map
//   - congruence of each map read at a pairing: equal arguments, equal cells (the kernel compares a pairing's
//     monomials, not its arguments)
// A law is a node at rank (level, D.size[x]) for an argument x; its uses read it at x's fields (structural induction),
// or at the arguments of a function's own recursive calls (recursion induction, other arguments changing with them),
// each where the tag is the case's. Lemmas the law needs are found by the values (theory exploration: equations between
// terms the random values agree on, then the shapes of a predicate kept), proven the same way at lower levels, and used
// at the terms of the law they match.
import type {C, E} from './machine.ts'
import {type Fact} from '../kernel/cyclic.ts'
import {substC} from '../kernel/kernel.ts'
import {type CyclicVerdict, type NodeSpec, proveCyclic} from './cyclic.ts'
import {pairedKeys, withDeadline} from '../kernel/prove.ts'

// --- sorts and the AST ------------------------------------------------------------------------------------------------

export const self = {self: true} as const
export const natural = 'nat' as const
export const boolean = 'bool' as const
type FieldSort = 'nat' | 'self'
export type Sort = 'nat' | 'bool' | Data
export type Ctor = {name: string, fields: {name: string, sort: FieldSort}[]}

// Terms: naturals, conditions as values (0 or 1), datatype values; `match` binds a case's fields by name.
export type X =
  | {op: 'var', name: string}
  | {op: 'nat', value: number}
  | {op: 'add' | 'sub' | 'min' | 'max', a: X, b: X}
  | {op: 'mul', k: number, a: X}
  | {op: 'if', c: Y, then: X, else: X}
  | {op: 'call', fn: string, args: X[]}
  | {op: 'ctor', data: string, ctor: number, args: X[]}
  | {op: 'match', data: string, of: X, cases: {binds: string[], body: X}[]}
  | {op: 'apply', param: string, arg: X}
  | {op: 'bool', c: Y}
export type Y =
  | {op: '<' | '<=' | '=', a: X, b: X}
  | {op: 'and' | 'or', xs: Y[]}
  | {op: 'not', x: Y}
  | {op: 'is', data: string, of: X, ctor: number}
  | {op: 'holds', x: X}

// --- the surface ------------------------------------------------------------------------------------------------------

let fresh = 0
const bindName = (field: string) => `${field}#${++fresh}`

export class Nat {
  constructor(readonly x: X) {}
  plus(b: NatLike): Nat { return new Nat({op: 'add', a: this.x, b: natX(b)}) }
  minus(b: NatLike): Nat { return new Nat({op: 'sub', a: this.x, b: natX(b)}) }
  times(k: number): Nat { return new Nat({op: 'mul', k, a: this.x}) }
  lt(b: NatLike): Bool { return new Bool({op: '<', a: this.x, b: natX(b)}) }
  atMost(b: NatLike): Bool { return new Bool({op: '<=', a: this.x, b: natX(b)}) }
  gt(b: NatLike): Bool { return new Bool({op: '<', a: natX(b), b: this.x}) }
  atLeast(b: NatLike): Bool { return new Bool({op: '<=', a: natX(b), b: this.x}) }
  eq(b: NatLike): Bool { return new Bool({op: '=', a: this.x, b: natX(b)}) }
  ne(b: NatLike): Bool { return this.eq(b).not() }
}
export type NatLike = Nat | number
const natX = (t: NatLike): X => (typeof t === 'number' ? {op: 'nat', value: t} : t.x)
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
  match(cases: Record<string, (fields: Record<string, any>) => Nat | Bool | Val | number>): any {
    const d = this.data
    const built = d.ctors.map(c => {
      const f = cases[c.name]
      if (!f) throw new Error(`${d.name}: match has no case ${c.name}`)
      const binds = c.fields.map(fl => bindName(fl.name))
      const fields = Object.fromEntries(c.fields.map((fl, i) => [fl.name, wrap(fl.sort === 'nat' ? 'nat' : d, {op: 'var', name: binds[i]!})]))
      return {binds, out: f(fields)}
    })
    const first = built[0]!.out
    const body = (o: unknown): X => (typeof o === 'number' ? natX(o) : o instanceof Bool ? {op: 'bool', c: o.y} : (o as Nat | Val).x)
    const x: X = {op: 'match', data: d.name, of: this.x, cases: built.map(b => ({binds: b.binds, body: body(b.out)}))}
    return (first instanceof Bool ? new Bool({op: 'holds', x}) : first instanceof Val ? new Val(first.data, x) : new Nat(x)) as never
  }
  is(ctor: string): Bool { return new Bool({op: 'is', data: this.data.name, of: this.x, ctor: this.data.index(ctor)}) }
  eq(b: Val): Bool { return new Bool({op: '=', a: this.x, b: b.x}) }
  ne(b: Val): Bool { return this.eq(b).not() }
}
// A value of a sort from its term.
export const wrap = (s: Sort, x: X): Nat | Bool | Val => (s === 'nat' ? new Nat(x) : s === 'bool' ? new Bool({op: 'holds', x}) : new Val(s, x))
const xOf = (s: Sort, v: unknown): X => (s === 'nat' ? natX(v as NatLike) : s === 'bool' ? {op: 'bool', c: (v as Bool).y} : (v as Val).x)
export function when<T extends Nat | Val | Bool | number>(c: Bool, a: T, b: T): T extends number ? Nat : T {
  if (a instanceof Bool) return new Bool({op: 'or', xs: [{op: 'and', xs: [c.y, a.y]}, {op: 'and', xs: [{op: 'not', x: c.y}, (b as Bool).y]}]}) as never
  const ax = typeof a === 'number' ? natX(a) : (a as Nat | Val).x, bx = typeof b === 'number' ? natX(b) : (b as Nat | Val).x
  const x: X = {op: 'if', c: c.y, then: ax, else: bx}
  return (a instanceof Val ? new Val(a.data, x) : new Nat(x)) as never
}

// A datatype: its constructors, each with fields that are naturals or values of the datatype itself (`self`). Its
// constructors are ordered as Lean's bijection numbers them: those of no field, then those with no field of the
// datatype, then the rest; a datatype with no constructor of the first two kinds has no value and is refused.
export class Data {
  readonly ctors: Ctor[]
  constructor(readonly name: string, decl: Record<string, Record<string, typeof self | 'nat' | {nat: true}>>) {
    const all: Ctor[] = Object.entries(decl).map(([c, fs]) => ({name: c, fields: Object.entries(fs).map(([f, s]) => ({name: f, sort: s === self ? 'self' as const : 'nat' as const}))}))
    const rank = (c: Ctor) => (!c.fields.length ? 0 : c.fields.every(f => f.sort === 'nat') ? 1 : 2)
    this.ctors = [...all].sort((a, b) => rank(a) - rank(b))
    if (!this.ctors.some(c => rank(c) < 2)) throw new Error(`${name}: every constructor has a field of ${name}, so it has no value`)
    if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(name)) throw new Error(`${name}: a datatype's name is letters and digits`)
  }
  index(ctor: string): number { const i = this.ctors.findIndex(c => c.name === ctor); if (i < 0) throw new Error(`${this.name} has no constructor ${ctor}`); return i }
  get nullary(): number { return this.ctors.filter(c => !c.fields.length).length }
  make(ctor: string, ...args: (Val | NatLike)[]): Val {
    const j = this.index(ctor), c = this.ctors[j]!
    if (args.length !== c.fields.length) throw new Error(`${this.name}.${ctor} takes ${c.fields.length} fields`)
    return new Val(this, {op: 'ctor', data: this.name, ctor: j, args: c.fields.map((f, i) => xOf(f.sort === 'nat' ? 'nat' : this, args[i]))})
  }
}
type Decl = Record<string, Record<string, unknown>>
// `data('List', {nil: {}, cons: {head: nat, tail: self}})`: `List.nil`, `List.cons(h, t)`, and `xs.match({...})`.
export function data<const D extends Decl>(name: string, decl: D): Data & {[c in keyof D]: keyof D[c] extends never ? Val : (...args: (Val | NatLike)[]) => Val} {
  const norm = Object.fromEntries(Object.entries(decl).map(([c, fs]) => [c, Object.fromEntries(Object.entries(fs as object).map(([f, s]) => [f, s === self ? self : 'nat' as const]))]))
  const d = new Data(name, norm)
  for (const c of d.ctors) Object.defineProperty(d, c.name, c.fields.length ? {value: (...args: (Val | NatLike)[]) => d.make(c.name, ...args)} : {get: () => d.make(c.name)})
  return d as never
}

// A function by structural recursion: its parameters' sorts, the sort it returns, its body over the parameters (it may
// call itself, and functions defined before it). `define` checks the recursion is structural: every call to itself
// passes, at one parameter fixed for the function, a field of that parameter bound by a match.
export type Fn = {name: string, params: {name: string, sort: Sort}[], ret: Sort, body: () => X, decreases?: number, paramFns: string[]}
export type Callable = ((...args: (Val | NatLike | Bool)[]) => any) & {fn: Fn}
const fns = new Map<string, Fn>()
export function define(name: string, params: Record<string, Sort>, ret: Sort, body: (args: Record<string, any>) => Nat | Bool | Val | number): Callable {
  if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(name)) throw new Error(`${name}: a function's name is letters and digits`)
  const ps = Object.entries(params).map(([n, s]) => ({name: n, sort: s}))
  let built: X | undefined
  const fn: Fn = {name, params: ps, ret, paramFns: [], body: () => {
    if (!built) {
      const args = Object.fromEntries(ps.map(p => [p.name, wrap(p.sort, {op: 'var', name: `${name}.${p.name}`})]))
      built = xOf(ret, body(args))
      fn.decreases = decreasing(fn, built)
      fn.paramFns = [...new Set(paramsIn(built))]
    }
    return built
  }}
  fns.set(name, fn)
  const call = (...args: (Val | NatLike | Bool)[]) => {
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

// The parameter every recursive call passes a field of (bound by a match on that parameter), or a refusal.
function decreasing(fn: Fn, body: X): number | undefined {
  const calls: {args: X[], fieldsOf: Map<string, string>}[] = []
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
    if (o.op === 'call' && o.fn === fn.name) calls.push({args: o.args, fieldsOf})
    if (o.op === 'call' && o.fn !== fn.name && !fns.has(o.fn)) throw new Error(`${fn.name} calls ${o.fn}, which isn't defined`)
    for (const v of Object.values(o)) go(v, fieldsOf)
  }
  go(body, new Map())
  if (!calls.length) return undefined
  for (const [i, p] of fn.params.entries()) {
    if (p.sort === 'nat' || p.sort === 'bool') continue
    const own = `${fn.name}.${p.name}`
    if (calls.every(c => { const a = c.args[i]!; return a.op === 'var' && c.fieldsOf.get(a.name) === own })) return i
  }
  throw new Error(`${fn.name}: not structural recursion (no parameter whose field every recursive call passes)`)
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
const asNat = (v: Value) => v as number
export function evalX(x: X, env: Env, params: Record<string, (n: number) => number>): Value {
  switch (x.op) {
    case 'var': { const v = env.get(x.name); if (v === undefined) throw new Error(`unbound ${x.name}`); return v }
    case 'nat': return x.value
    case 'add': return asNat(evalX(x.a, env, params)) + asNat(evalX(x.b, env, params))
    case 'sub': return Math.max(0, asNat(evalX(x.a, env, params)) - asNat(evalX(x.b, env, params)))
    case 'min': return Math.min(asNat(evalX(x.a, env, params)), asNat(evalX(x.b, env, params)))
    case 'max': return Math.max(asNat(evalX(x.a, env, params)), asNat(evalX(x.b, env, params)))
    case 'mul': return x.k * asNat(evalX(x.a, env, params))
    case 'if': return evalY(x.c, env, params) ? evalX(x.then, env, params) : evalX(x.else, env, params)
    case 'bool': return evalY(x.c, env, params) ? 1 : 0
    case 'apply': return params[x.param]!(asNat(evalX(x.arg, env, params)))
    case 'ctor': return {c: x.ctor, f: x.args.map(a => evalX(a, env, params))}
    case 'match': {
      const v = evalX(x.of, env, params) as {c: number, f: Value[]}, cs = x.cases[v.c]!
      const e2 = new Map(env)
      cs.binds.forEach((b, i) => e2.set(b, v.f[i]!))
      return evalX(cs.body, e2, params)
    }
    case 'call': {
      const f = fnOf(x.fn), body = f.body()
      const e2: Env = new Map(f.params.map((p, i) => [`${f.name}.${p.name}`, evalX(x.args[i]!, env, params)]))
      return evalX(body, e2, params)
    }
  }
}
export function evalY(y: Y, env: Env, params: Record<string, (n: number) => number>): boolean {
  switch (y.op) {
    case '<': return asNat(evalX(y.a, env, params)) < asNat(evalX(y.b, env, params))
    case '<=': return asNat(evalX(y.a, env, params)) <= asNat(evalX(y.b, env, params))
    case '=': return same(evalX(y.a, env, params), evalX(y.b, env, params))
    case 'and': return y.xs.every(z => evalY(z, env, params))
    case 'or': return y.xs.some(z => evalY(z, env, params))
    case 'not': return !evalY(y.x, env, params)
    case 'is': return (evalX(y.of, env, params) as {c: number}).c === y.ctor
    case 'holds': return evalX(y.x, env, params) === 1
  }
}
const same = (a: Value, b: Value): boolean => (typeof a === 'number' || typeof b === 'number' ? a === b : a.c === b.c && a.f.every((x, i) => same(x, b.f[i]!)))
export const showValue = (d: Sort, v: Value): string => {
  if (typeof v === 'number') return String(v)
  if (d === 'nat' || d === 'bool') return JSON.stringify(v)
  const c = d.ctors[v.c]!
  return c.fields.length ? `${c.name}(${c.fields.map((f, i) => showValue(f.sort === 'nat' ? 'nat' : d, v.f[i]!)).join(', ')})` : c.name
}

// Random values: small naturals (so that comparisons and equalities between them happen), values of up to `size`
// constructors of fields of the datatype.
type Rand = () => number
export const rng = (seed: number): Rand => () => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed / 2147483648 }
export function randomValue(s: Sort, rand: Rand, size: number, natMax = 5): Value {
  if (s === 'nat') return Math.floor(rand() * (natMax + 1))
  if (s === 'bool') return rand() < 0.5 ? 0 : 1
  const leaves = s.ctors.filter(c => c.fields.every(f => f.sort === 'nat'))
  const pick = size <= 0 || rand() < 0.25 ? leaves : s.ctors
  const c = pick[Math.floor(rand() * pick.length)]!, j = s.ctors.indexOf(c)
  const rec = c.fields.filter(f => f.sort === 'self').length
  return {c: j, f: c.fields.map(f => randomValue(f.sort === 'nat' ? 'nat' : s, rand, Math.floor((size - 1) / Math.max(1, rec)), natMax))}
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
function argsOf(key: E, n: number): E[] | undefined {
  if (n === 1) return [key]
  if (key.op !== 'add' || key.a.op !== 'prod' || key.a.a.op !== 'add') return undefined
  const left = argsOf(key.a.a.a, n - 1)
  return left && [...left, key.b]
}
export const tagMap = (d: string) => `${d}.tag`, sizeMap = (d: string) => `${d}.size`
export const fieldMap = (d: Data, j: number, i: number) => `${d.name}.${d.ctors[j]!.name}.${d.ctors[j]!.fields[i]!.name}`
export const ctorMap = (d: Data, j: number) => `${d.name}.${d.ctors[j]!.name}`

export type Program = {datas: Data[], fns: Fn[], params: string[]}
// Everything a law reads: the datatypes, the functions (with those they call), the function parameters.
export function programOf(laws: DataLaw[], extra: Fn[] = []): Program {
  const fs = new Map<string, Fn>(), ds = new Map<string, Data>(), ps = new Set<string>()
  const addSort = (s: Sort) => { if (s instanceof Data) ds.set(s.name, s) }
  const visit = (t: unknown) => walk(t, o => {
    if (o.op === 'call' && !fs.has(o.fn as string)) { const f = fnOf(o.fn as string); fs.set(f.name, f); f.params.forEach(p => addSort(p.sort)); addSort(f.ret); visit(f.body()) }
    if (o.op === 'apply') ps.add(o.param as string)
  })
  for (const l of laws) { l.vars.forEach(v => addSort(v.sort)); visit(l.holds) }
  for (const f of extra) visit({op: 'call', fn: f.name, args: []})
  const datas = [...new Map([...ds.values()].map(d => [d.name, d])).values()]
  // Functions in definition order (each after those it calls).
  const order: Fn[] = [], seen = new Set<string>()
  const place = (f: Fn) => { if (seen.has(f.name)) return; seen.add(f.name); walk(f.body(), o => { if (o.op === 'call' && o.fn !== f.name) place(fnOf(o.fn as string)) }); order.push(f) }
  for (const f of fs.values()) place(f)
  return {datas, fns: order, params: [...ps]}
}

const dataOf = (p: Program, name: string) => p.datas.find(d => d.name === name)!
export function encX(p: Program, x: X, env: Map<string, E>): E {
  switch (x.op) {
    case 'var': return env.get(x.name) ?? ev(x.name)
    case 'nat': return k(x.value)
    case 'add': case 'sub': case 'min': case 'max': return {op: x.op, a: encX(p, x.a, env), b: encX(p, x.b, env)}
    case 'mul': return {op: 'mul', k: x.k, a: encX(p, x.a, env)}
    case 'if': return {op: 'if', c: encY(p, x.c, env), then: encX(p, x.then, env), else: encX(p, x.else, env)}
    case 'bool': return {op: 'if', c: encY(p, x.c, env), then: k(1), else: k(0)}
    case 'apply': return get(x.param, encX(p, x.arg, env))
    case 'call': return get(x.fn, keyOf(x.args.map(a => encX(p, a, env))))
    case 'ctor': { const d = dataOf(p, x.data); return x.args.length ? get(ctorMap(d, x.ctor), keyOf(x.args.map(a => encX(p, a, env)))) : k(x.ctor) }
    case 'match': {
      const d = dataOf(p, x.data), of = encX(p, x.of, env)
      const bodies = x.cases.map((c, j) => { const e2 = new Map(env); c.binds.forEach((b, i) => e2.set(b, get(fieldMap(d, j, i), of))); return encX(p, c.body, e2) })
      return bodies.slice(0, -1).reduceRight<E>((acc, b, j) => ({op: 'if', c: eqC(get(tagMap(d.name), of), k(j)), then: b, else: acc}), bodies.at(-1)!)
    }
  }
}
export function encY(p: Program, y: Y, env: Map<string, E>): C {
  switch (y.op) {
    case '<': case '<=': case '=': return {op: y.op, a: encX(p, y.a, env), b: encX(p, y.b, env)}
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
    put(`shape ${d.name}`, {name: '', keys: ['x$'], holds: andC(leC(tag, k(d.ctors.length - 1)), ...d.ctors.map((c, j) =>
      implies(eqC(tag, k(j)), eqC(size(x), c.fields.flatMap((f, i) => (f.sort === 'self' ? [size(get(fieldMap(d, j, i), x))] : [])).reduce<E>((a, b) => ({op: 'add', a, b}), k(1))))))})
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
  code(s: Sort, v: Value): number { return s instanceof Data ? this.id(s, v) : (v as number) }
  decode(s: Sort, n: number): Value { return s instanceof Data ? this.value(s, n) : n }
  read(map: string, key: number): number {
    const p = this.p
    for (const d of p.datas) {
      if (map === tagMap(d.name)) return (this.value(d, key) as {c: number}).c
      if (map === sizeMap(d.name)) return sizeOf(d, this.value(d, key))
      for (const [j, c] of d.ctors.entries()) {
        for (const [i, f] of c.fields.entries()) if (map === fieldMap(d, j, i)) { const v = this.value(d, key) as {c: number, f: Value[]}; return v.c === j ? this.code(f.sort === 'nat' ? 'nat' : d, v.f[i]!) : 0 }
        if (c.fields.length && map === ctorMap(d, j)) { const as = unkey(key, c.fields.length); return this.id(d, {c: j, f: c.fields.map((f, i) => this.decode(f.sort === 'nat' ? 'nat' : d, as[i]!))}) }
      }
    }
    const f = p.fns.find(g => g.name === map)
    if (f) {
      const as = unkey(key, f.params.length)
      const env: Env = new Map(f.params.map((q, i) => [`${f.name}.${q.name}`, this.decode(q.sort, as[i]!)]))
      const out = evalX(f.body(), env, this.params)
      return f.ret === 'nat' || f.ret === 'bool' ? out as number : this.id(f.ret, out)
    }
    const prm = this.params[map]
    if (prm) return prm(key)
    throw new Error(`no map ${map}`)
  }
  evalE(e: E, env: Record<string, number>): number {
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
export const sizeOf = (d: Data, v: Value): number => { const o = v as {c: number, f: Value[]}; return 1 + d.ctors[o.c]!.fields.reduce((s, f, i) => s + (f.sort === 'self' ? sizeOf(d, o.f[i]!) : 0), 0) }
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
export type DataVerdict = {proven: boolean, checked: boolean, law: string, counterexample?: Record<string, string>, proof?: CyclicVerdict, lemmas: string[], scheme?: string, ms: number, goal?: string, stuck?: string, tried: number, program?: Program, node?: number}
export type Options = {samples?: number, depth?: number, lemmas?: boolean | DataLaw[], ms?: number, induction?: boolean, seed?: number}

// Random values of the law's variables: a law false at one is refuted with it.
export function refute(l: DataLaw, n = 400, seed = 7): Record<string, string> | undefined {
  for (const s of samples(l.vars, programOf([l]).params, n, seed)) {
    let ok: boolean
    try { ok = evalY(l.holds, s.env, s.params) } catch (e) { throw new Error(`${l.name}: ${(e as Error).message}`) }
    if (!ok) return Object.fromEntries(l.vars.map(v => [v.name, showValue(v.sort, s.env.get(v.name)!)]))
  }
  return undefined
}

// The node of a law: its variables (each a plain variable of the encoding), its conclusion, rank (level, size of the
// variable inducted on), the uses of the scheme, and the facts at every term its goal reads, to `depth` unfoldings.
type Scheme = {name: string, on?: {v: string, d: Data}, uses: {subst: Record<string, E>, guard: C}[]}
function schemes(p: Program, l: DataLaw): Scheme[] {
  const out: Scheme[] = [], seen = new Set<string>()
  const add = (s: Scheme) => { const id = JSON.stringify(s.uses); if (!seen.has(id)) { seen.add(id); out.push(s) } }
  // Recursion induction: each call of the law to a recursive function at the law's variables, its recursive calls'
  // arguments as the uses' substitution (where the case's tag holds).
  walk(l.holds, o => {
    if (o.op !== 'call') return
    const f = fnOf(o.fn as string), args = o.args as X[]
    f.body()
    if (f.decreases === undefined) return
    const at = args[f.decreases]!
    if (at.op !== 'var' || !l.vars.some(v => v.name === at.name)) return
    const d = f.params[f.decreases]!.sort as Data
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
    if (uses.length) add({name: `recursion of ${f.name} on ${at.name}`, on: {v: at.name, d}, uses})
  })
  // Structural induction on each variable of a datatype, the others fixed.
  for (const v of l.vars) {
    if (!(v.sort instanceof Data)) continue
    const d = v.sort, x = ev(v.name)
    add({name: `structure of ${v.name}`, on: {v: v.name, d}, uses: d.ctors.flatMap((c, j) => c.fields.flatMap((f, i) => (f.sort === 'self' ? [{subst: {[v.name]: get(fieldMap(d, j, i), x)}, guard: eqC(get(tagMap(d.name), x), k(j))}] : [])))})
  }
  return out
}

// The facts a node's goal reads: each function's at the calls of `roots` (the conclusion), and at the calls in what that
// gives, `depth` rounds deep; each constructor's at every constructor read (no unfolding: the value's tag and fields);
// the shape at `shapesAt` (where a use's guard reads the tag), and from depth 2 at every value whose tag is read; eta at
// `etaAt`; congruences of reads the random models give equal arguments. `others` (the uses' conclusions) are read for
// constructors and congruences, and unfolded too from depth 3.
type Want = {roots: unknown[], others: unknown[], depth: number, shapesAt: E[], etaAt: E[], models: {m: Model, env: Record<string, number>}[], every?: boolean}
function instancesOf(p: Program, fs: Facts, w: Want): NodeSpec['insts'] {
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
      next.push(...body)
    }
    frontier = next
  }
  // A function read whose decreasing argument equals a constructor's value (by the equalities the instances give, every
  // branch, and the uses' conclusions) unfolds there too: where the definition's match is decided.
  if (w.depth >= 1) {
    const id0 = (t: E) => JSON.stringify(t), parent = new Map<string, string>(), terms = new Map<string, E>()
    const find = (x: string): string => { let r = x; while (parent.has(r)) r = parent.get(r)!; return r }
    const union = (x: E, y: E) => { terms.set(id0(x), x); terms.set(id0(y), y); const a = find(id0(x)), b = find(id0(y)); if (a !== b) parent.set(a, b) }
    const leaves = (e: E): E[] => (e.op === 'if' ? [...leaves(e.then), ...leaves(e.else)] : [e])
    for (const q of insts) for (const [a, b] of equalities(holdsAt(fs.facts[q.fact]!.name, q.at))) for (const leaf of leaves(b)) union(a, leaf)
    for (const c of w.others as C[]) for (const [a, b] of equalities(c)) union(a, b)
    // Closed under congruence: two reads of one map at arguments already equal are equal.
    const readsBy = new Map<string, {key: E, as: E[]}[]>()
    for (const r of all) { const n = fs.arity.get(r.map), as = n ? argsOf(r.key, n) : undefined; if (as) { const list = readsBy.get(r.map) ?? []; list.push({key: r.key, as}); readsBy.set(r.map, list) } }
    for (let changed = true; changed;) {
      changed = false
      for (const [map, list] of readsBy) for (const [i, x] of list.entries()) for (const y of list.slice(i + 1)) {
        if (!x.as.every((t, q) => find(id0(t)) === find(id0(y.as[q]!)))) continue
        const cx = get(map, x.key), cy = get(map, y.key)
        if (find(id0(cx)) !== find(id0(cy))) { union(cx, cy); changed = true }
      }
    }
    const built = (t: E) => (t.op === 'get' && p.datas.some(d => d.ctors.some((c, j) => c.fields.length && t.map === ctorMap(d, j)))) || t.op === 'const'
    let extra = 0
    for (const r of [...all]) {
      const f = fnOfMap(r.map)
      if (!f || f.decreases === undefined) continue
      const as = argsOf(r.key, f.params.length)
      if (!as) continue
      const root = find(id0(as[f.decreases]!))
      for (const [key, t] of terms) {
        if (key === id0(as[f.decreases]!) || find(key) !== root || !built(t) || extra >= 24) continue
        const as2 = as.map((a, i) => (i === f.decreases ? t : a)), rid = JSON.stringify({map: f.name, key: keyOf(as2)})
        if (unfolded.has(rid)) continue
        unfolded.add(rid); extra++
        inst(`fn ${f.name}`, as2)
        anchoredAt.set(JSON.stringify([fs.at.get(`fn ${f.name}`), as2]), {read: JSON.stringify(get(f.name, r.key)), arg: as[f.decreases]!, value: t})
        note([{map: f.name, key: keyOf(as2)}])
        ctors(note(reads(holdsAt(`fn ${f.name}`, as2))))
      }
    }
  }
  const dataOfTerm = (t: E): Data | undefined => {
    if (t.op === 'get') { for (const d of p.datas) if (t.map === tagMap(d.name) || t.map === sizeMap(d.name)) return d; const f = fnOfMap(t.map); if (f && f.ret instanceof Data) return f.ret; for (const d of p.datas) for (const [j, c] of d.ctors.entries()) { if (c.fields.length && t.map === ctorMap(d, j)) return d; for (const [i, fl] of c.fields.entries()) if (fl.sort === 'self' && t.map === fieldMap(d, j, i)) return d } }
    return undefined
  }
  const shape = (t: E, d?: Data) => { const dd = d ?? dataOfTerm(t); if (dd) { inst(`shape ${dd.name}`, [t]); ctors(note(reads(holdsAt(`shape ${dd.name}`, [t])))) } }
  for (const t of w.shapesAt) shape(t, typeOfVar(p, t))
  if (w.depth >= 2) for (const r of [...all]) for (const d of p.datas) if (r.map === tagMap(d.name)) shape(r.key, d)
  for (const t of w.etaAt) { const d = typeOfVar(p, t) ?? dataOfTerm(t); if (d) { inst(`eta ${d.name}`, [t]); shape(t, d); ctors(note(reads(holdsAt(`eta ${d.name}`, [t])))) } }
  // Congruences (a map is a function), found in each random model: the equalities the facts give there (a function's
  // read equal to the branch of its body the model takes, a constructor's field to its argument, eta, an implication's
  // equalities where its premise holds, a use's where its guard does), closed under reading one map at equal arguments;
  // each pair of reads the closure makes equal in some model is a congruence instance.
  for (const d of p.datas) if (d.nullary && all.some(r => r.map === tagMap(d.name))) { inst(`nullary ${d.name}`, []); for (let j = 0; j < d.nullary; j++) all.push({map: tagMap(d.name), key: k(j)}) }
  const id = (t: E) => JSON.stringify(t)
  const cellsOf = new Map<string, {key: E, as: E[]}[]>()
  for (const r of all) {
    const n = fs.arity.get(r.map), as = n ? argsOf(r.key, n) : undefined
    if (!as) continue
    const list = cellsOf.get(r.map) ?? []
    if (!list.some(x => id(x.key) === id(r.key))) list.push({key: r.key, as})
    cellsOf.set(r.map, list)
  }
  const sources = [...insts.map(q => holdsAt(fs.facts[q.fact]!.name, q.at)), ...(w.others as C[])]
  // The values the goal reads (each read, but not as a key of another read): what the congruences must connect.
  const values = new Map<string, E>()
  const valueWalk = (t: unknown): void => {
    if (!t || typeof t !== 'object') return
    if (Array.isArray(t)) { t.forEach(valueWalk); return }
    const o = t as E
    if (o.op === 'get') { values.set(id(o), o); return }
    for (const v of Object.values(o)) valueWalk(v)
  }
  valueWalk([sources, w.roots])
  // In each model: the classes of the equalities the facts give there, with why each merged (a fact, or a congruence
  // whose arguments are merged); every value in a class is explained against one, and the congruences the explanations
  // use are the instances (with `every`, those that every model's explanations use).
  const used = new Map<string, {map: string, at: E[], n: number}>()
  for (const {m, env} of w.models) {
    const parent = new Map<string, string>(), adj = new Map<string, {to: string, cong?: {map: string, x: E[], y: E[]}}[]>()
    const find = (x: string): string => { let r = x; while (parent.has(r)) r = parent.get(r)!; return r }
    const edge = (x: E, y: E, cong?: {map: string, x: E[], y: E[]}) => {
      const a2 = id(x), b2 = id(y)
      if (a2 === b2 || find(a2) === find(b2)) return false
      parent.set(find(a2), find(b2))
      ;(adj.get(a2) ?? adj.set(a2, []).get(a2)!).push({to: b2, cong}); (adj.get(b2) ?? adj.set(b2, []).get(b2)!).push({to: a2, cong: cong && {map: cong.map, x: cong.y, y: cong.x}})
      return true
    }
    const truthOf = (c: C): boolean | undefined => { try { return m.evalC(c, env) } catch { return undefined } }
    const taken = (e: E): E | undefined => { if (e.op !== 'if') return e; const t = truthOf(e.c); return t === undefined ? undefined : taken(t ? e.then : e.else) }
    const active = (c: C): void => {
      if (c.op === 'and') { c.xs.forEach(active); return }
      if (c.op === 'or') { const open = c.xs.filter(x => truthOf(x) !== false); if (open.length === 1) active(open[0]!); else { const neg = c.xs.find(x => x.op === 'not' && truthOf(x.x) === true); if (neg) c.xs.filter(x => x !== neg).forEach(x => { if (truthOf(x) === true) active(x) }) } return }
      if (c.op === '=' && truthOf(c) === true) { const leaf = taken(c.b); if (leaf) edge(c.a, leaf) }
    }
    sources.forEach(active)
    for (let changed = true; changed;) {
      changed = false
      for (const [map, list] of cellsOf) for (const [i, x] of list.entries()) for (const y of list.slice(i + 1)) {
        if (x.as.every((t, q) => id(t) === id(y.as[q]!)) || !x.as.every((t, q) => find(id(t)) === find(id(y.as[q]!)))) continue
        if (edge(get(map, x.key), get(map, y.key), {map, x: x.as, y: y.as})) changed = true
      }
    }
    // Explanations: the path between two terms of a class (each edge a fact, or a congruence explained in turn).
    const counted = new Set<string>(), explained = new Set<string>()
    const explain = (a2: string, b2: string): void => {
      const key = a2 < b2 ? `${a2}|${b2}` : `${b2}|${a2}`
      if (a2 === b2 || explained.has(key)) return
      explained.add(key)
      const back = new Map<string, {from: string, cong?: {map: string, x: E[], y: E[]}}>([[a2, {from: ''}]]), queue = [a2]
      while (queue.length && !back.has(b2)) { const x = queue.shift()!; for (const e of adj.get(x) ?? []) if (!back.has(e.to)) { back.set(e.to, {from: x, cong: e.cong}); queue.push(e.to) } }
      if (!back.has(b2)) return
      for (let at = b2; at !== a2;) {
        const step = back.get(at)!
        if (step.cong) {
          const c = step.cong, k2 = JSON.stringify([c.map, c.x, c.y])
          if (!counted.has(k2)) { counted.add(k2); const had = used.get(k2) ?? used.get(JSON.stringify([c.map, c.y, c.x])); if (had) had.n++; else used.set(k2, {map: c.map, at: [...c.x, ...c.y], n: 1}) }
          c.x.forEach((t, q) => explain(id(t), id(c.y[q]!)))
        }
        at = step.from
      }
    }
    const byClass = new Map<string, string[]>()
    for (const v of values.keys()) { const r = find(v); (byClass.get(r) ?? byClass.set(r, []).get(r)!).push(v) }
    for (const vs of byClass.values()) for (const v of vs.slice(1)) explain(vs[0]!, v)
  }
  for (const d of used.values()) if (!w.every || d.n >= w.models.length) inst(`cong ${d.map}`, d.at)
  return insts
}
let varSorts = new Map<string, Data>()
// An instance unfolded where a read's argument equals a constructor's value: the read it stands for (for `reached`).
const anchoredAt = new Map<string, {read: string, arg: E, value: E}>()
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

type Proven = {law: DataLaw, spec: NodeSpec, nodes: NodeSpec[]}
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
    return [true, false].flatMap(t => { const s2 = side(t), lit = t ? c : {op: 'not', x: c} as C; return s2.length ? build(s2, [...lits, lit], d2, depth + 1) : [{lits: [...lits, lit], models: undefined, near: ms.map(i => models[i]!)}] })
  }
  return build(models.map((_, i) => i), [], new Set(), 0)
}

// One attempt: the law's node (and the lemmas', proven before, with their own nodes) at a scheme and a depth. With
// several cases, a main node uses a node per case (each its guards as hypotheses, its own instances), at rank
// (level, size, 1) above theirs (level, size, 0); a case node uses the main node at the children.
function attempt(p: Program, fs: Facts, l: DataLaw, scheme: Scheme | undefined, depth: number, lemmas: Proven[], level: number, pool: M[]): {verdict: CyclicVerdict, specs: NodeSpec[]} {
  // A few models for the instances; the whole pool for the cases (a rare case gets its own models from it).
  const models = pool.slice(0, 24), few = (ms: M[]) => ms.slice(0, 16)
  const concl = encY(p, l.holds, new Map())
  const specs: NodeSpec[] = [], where = new Map<string, number>()
  for (const lm of lemmas) {
    const local = new Map<number, number>()
    lm.nodes.forEach((n, i) => {
      if (where.has(n.name)) { local.set(i, where.get(n.name)!); return }
      local.set(i, specs.length); where.set(n.name, specs.length)
      specs.push({...n, uses: n.uses.map(u => ({...u, node: local.get(u.node) ?? u.node}))})
    })
  }
  const me = specs.length, name = `${l.name}${scheme ? ` (${scheme.name})` : ''}`
  varSorts = new Map(l.vars.flatMap(v => (v.sort instanceof Data ? [[v.name, v.sort] as [string, Data]] : [])))
  const size = scheme?.on ? get(sizeMap(scheme.on.d.name), ev(scheme.on.v)) : k(0)
  const rank = (sub: number): E[] => [k(level), size, k(sub)]
  const ih = (scheme?.uses ?? []).map(u => ({node: me, subst: u.subst, guard: u.guard}))
  const shapesAt = scheme?.on ? [ev(scheme.on.v)] : []
  const ihConcls = ih.map(u => substC(concl, {vars: u.subst, maps: {}, flags: {}}))
  // Uses of the lemmas, where a lemma's largest read matches a read of this goal (unfolded), its key up to the equalities
  // the unfolded definitions give (any branch); twice over, the uses' own conclusions read the second time.
  const pre = instancesOf(p, fs, {roots: [concl], others: ihConcls, depth, shapesAt, etaAt: [], models: []})
  const lemmaUses = lemmaUsesFor(p, fs, lemmas.map(lm => ({law: lm.law, node: where.get(lm.spec.name)!, concl: specs[where.get(lm.spec.name)!]!.concl})), [concl, ihConcls], pre)
  const uses = [...ih, ...lemmaUses]
  const useConcl = (u: NodeSpec['uses'][number]) => substC(u.node === me ? concl : specs[u.node]!.concl, {vars: u.subst, maps: {}, flags: {}})
  // The lemmas' conclusions are unfolded like the law's (they are what the goal reads, said another way); the cycle's
  // own uses only from depth 3.
  const instsFor = (ms: M[], us: NodeSpec['uses'], every = false) => instancesOf(p, fs, {roots: [concl, us.filter(u => u.node !== me).map(useConcl)], others: us.filter(u => u.node === me).map(useConcl), depth, shapesAt, etaAt: [...shapesAt, ...valuesCompared(p, l)], models: ms, every})
  const cases = scheme ? casesOf(p, pre.filter(q => fs.facts[q.fact]!.name.startsWith('fn ')).map(q => holdsAt(fs, q)), new Set(l.vars.map(v => v.name)), pool) : []
  if (cases.length <= 1) {
    specs.push({name, hyps: [], concl, rank: rank(0), insts: instsFor(models, uses), uses})
  } else {
    specs.push({name, hyps: [], concl, rank: rank(1), insts: [], uses: cases.map((c, i) => ({node: me + 1 + i, subst: {}, guard: andC(yesC, ...c.lits)}))})
    for (const [i, c] of cases.entries()) {
      // The uses whose guard some model of the case meets (all, for a case no model reaches).
      const holdsIn = (g: C) => !c.models || c.models.some(({m, env}) => { try { return m.evalC(g, env) } catch { return true } })
      const us = uses.filter(u => holdsIn(u.guard))
      const ms = few(c.models ?? c.near ?? models)
      specs.push({name: `${name}, case ${i + 1}`, hyps: c.lits, concl, rank: rank(0), insts: reached(p, fs, instsFor(ms, us), [c.lits, concl, us.map(u => [u.guard, useConcl(u)]), shapesAt], ms), uses: us})
    }
  }
  // Each attempt within its own time (a goal past it is left unknown, and the attempt fails).
  const was = pairedKeys.skip
  pairedKeys.skip = true
  try { return {verdict: withDeadline(performance.now() + attemptMs.ms, () => proveCyclic(fs.facts, specs)), specs} } finally { pairedKeys.skip = was }
}
export const attemptMs = {ms: 8000}
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
    if (name.startsWith('shape ') || name.startsWith('eta ')) { const d = name.split(' ')[1]!; return [get(tagMap(d), q.at[0]!), get(sizeMap(d), q.at[0]!), ...p.datas.filter(x => x.name === d).flatMap(x => x.ctors.flatMap((c, j) => c.fields.map((_, i) => get(fieldMap(x, j, i), q.at[0]!))))] }
    return []
  }
  const kept = new Set<number>()
  for (let changed = true; changed;) {
    changed = false
    for (const [i, q] of insts.entries()) {
      if (kept.has(i)) continue
      const name = fs.facts[q.fact]!.name
      if (name.startsWith('cong ') || name.startsWith('nullary ')) continue
      const virtual = anchoredAt.get(JSON.stringify([q.fact, q.at]))
      const same = (v: NonNullable<typeof virtual>) => ms.every(({m, env}) => { try { return m.evalE(v.arg, env) === m.evalE(v.value, env) } catch { return false } })
      if (!anchor(q).some(a => reach.has(id(a))) && !(virtual && reach.has(virtual.read) && same(virtual))) continue
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
function lemmaUsesFor(p: Program, fs: Facts, lemmas: {law: DataLaw, node: number, concl: C}[], from: unknown[], insts: NodeSpec['insts']): NodeSpec['uses'] {
  const id = (t: E) => JSON.stringify(t), parent = new Map<string, string>(), terms = new Map<string, E>()
  const find = (x: string): string => { let r = x; while (parent.has(r)) r = parent.get(r)!; return r }
  const union = (x: E, y: E) => { terms.set(id(x), x); terms.set(id(y), y); const a = find(id(x)), b = find(id(y)); if (a !== b) parent.set(a, b) }
  const leaves = (e: E): E[] => (e.op === 'if' ? [...leaves(e.then), ...leaves(e.else)] : [e])
  for (const q of insts) for (const [a, b] of equalities(holdsAt(fs, q))) for (const leaf of leaves(b)) union(a, leaf)
  const members = (t: E): E[] => { const r = find(id(t)); return [t, ...[...terms.entries()].filter(([key]) => key !== id(t) && find(key) === r).map(([, e]) => e)] }
  const out: NodeSpec['uses'] = [], seen = new Set<string>()
  let reads: E[] = []
  walk([from, insts.map(q => holdsAt(fs, q))], o => { if (o.op === 'get') reads.push(o as unknown as E) })
  for (let round = 0; round < 2; round++) {
    const fresh: E[] = []
    for (const lm of lemmas) {
      const vars = new Set(lm.law.vars.map(v => v.name)), sides: E[] = []
      walk(encY(p, lm.law.holds, new Map()), o => { if (o.op === 'get') sides.push(o as unknown as E) })
      const tops = sides.filter(a => !sides.some(b => b !== a && JSON.stringify(b).includes(JSON.stringify(a)))) as Extract<E, {op: 'get'}>[]
      for (const top of tops) for (const t of reads) {
        if (t.op !== 'get' || t.map !== top.map) continue
        for (const key of members(t.key)) {
          const sub = matches(top.key, vars, key, {})
          if (!sub || Object.keys(sub).length !== vars.size) continue
          const k2 = JSON.stringify([lm.node, sub])
          if (seen.has(k2) || out.length >= 8 || out.filter(u => u.node === lm.node).length >= 4) continue
          seen.add(k2)
          out.push({node: lm.node, subst: sub, guard: yesC})
          walk(substC(lm.concl, {vars: sub, maps: {}, flags: {}}), o => { if (o.op === 'get') fresh.push(o as unknown as E) })
        }
      }
    }
    reads = fresh
  }
  return out
}
// The equalities a condition may give: those in a positive place (a conjunction's parts, a disjunction's disjuncts that
// aren't negations, so an implication's conclusion and never its premise).
function equalities(c: C): [E, E][] {
  if (c.op === '=') return [[c.a, c.b]]
  if (c.op === 'and' || c.op === 'or') return c.xs.flatMap(x => (x.op === 'not' ? [] : equalities(x)))
  return []
}
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
function proveWith(p: Program, fs: Facts, l: DataLaw, lemmas: Proven[], level: number, opts: Options, until: number, per: number, depths: number[]): {out?: Proven, verdict?: CyclicVerdict, scheme?: string, tried: number, last?: CyclicVerdict} {
  const models = modelsFor(p, l, 240, opts.seed ?? 3)
  let tried = 0, last: CyclicVerdict | undefined
  const ss: (Scheme | undefined)[] = opts.induction === false ? [undefined] : schemes(p, l)
  for (const depth of depths.filter(d => d <= (opts.depth ?? 3))) for (const s of ss) {
    if (performance.now() > until) return {tried, last}
    tried++
    attemptMs.ms = Math.min(per, until - performance.now())
    const {verdict, specs} = attempt(p, fs, l, s, depth, lemmas, level, models)
    last = verdict
    if (verdict.proven && verdict.checked) return {out: {law: l, spec: specs.find(n => n.name === specs[specs.length - 1]!.name.replace(/, case \d+$/, ''))!, nodes: specs}, verdict, scheme: s?.name, tried}
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
    for (const d of p.datas) d.ctors.forEach((c, j) => { if (c.fields.length) for (const args of build(c.fields.map(f => (f.sort === 'nat' ? 'nat' : d)), size - 1)) addT({x: {op: 'ctor', data: d.name, ctor: j, args: args.map(a => a.x)}, sort: d, size}) })
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
    const body = f.body(), di = f.decreases
    if (body.op !== 'match' || di === undefined || body.of.op !== 'var' || body.of.name !== `${f.name}.${f.params[di]!.name}`) continue
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
    case 'if': return `if ${showY(x.c)} then ${showX(x.then)} else ${showX(x.else)}`
    case 'bool': return showY(x.c)
    case 'apply': return `${x.param}(${showX(x.arg)})`
    case 'call': return `${x.fn}(${x.args.map(showX).join(', ')})`
    case 'ctor': { const d = [...fns.values()].length >= 0 ? x.data : x.data; return `${d}.${x.ctor}${x.args.length ? `(${x.args.map(showX).join(', ')})` : ''}` }
    case 'match': return `match ${showX(x.of)}`
  }
}
export const showY = (y: Y): string => {
  switch (y.op) {
    case '<': case '<=': case '=': return `${showX(y.a)} ${y.op} ${showX(y.b)}`
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
export function proveData(l: DataLaw, opts: Options = {}): DataVerdict {
  const t0 = performance.now(), until = t0 + (opts.ms ?? 90_000)
  const p = programOf([l, ...(Array.isArray(opts.lemmas) ? opts.lemmas : [])]), fs = factsOf(p)
  const done = (v: Omit<DataVerdict, 'ms' | 'law'>): DataVerdict => ({law: l.name, ...v, ms: Math.round(performance.now() - t0)})
  const cex = refute(l, opts.samples ?? 400)
  if (cex) return done({proven: false, checked: false, counterexample: cex, lemmas: [], tried: 0})
  // The law alone: one unfolding, then two.
  let tried = 0
  const ok = (r: ReturnType<typeof proveWith>, lemmas: Proven[], prog = p) => (tried += r.tried, r.out ? done({proven: true, checked: true, proof: r.verdict, lemmas: lemmas.map(q => q.law.name), scheme: r.scheme, tried, program: prog, node: r.out.nodes.indexOf(r.out.spec)}) : undefined)
  const first = proveWith(p, fs, l, [], 1, opts, until, 6000, [1])
  const one = ok(first, [])
  if (one) return one
  const without = opts.lemmas === false || opts.induction === false
  if (!Array.isArray(opts.lemmas)) { const two = ok(proveWith(p, fs, l, [], 1, opts, until, without ? 20000 : 8000, [2, ...(without ? [3] : [])]), []); if (two) return two }
  if (without) return done({proven: false, checked: false, lemmas: [], tried, ...stuckOf(first.last)})
  // Lemmas: conjectures from the values, those a read of the law's goal matches first. Each is proven (with those
  // proven before it, at the level after theirs); after each that the goal matches, the law is tried again with all.
  const cands = Array.isArray(opts.lemmas) ? opts.lemmas : conjectures(p, l)
  const p2 = programOf([l, ...cands]), fs2 = factsOf(p2)
  const goalOf = (s: Scheme | undefined) => {
    const concl = encY(p2, l.holds, new Map()), ihc = (s?.uses ?? []).map(u => substC(concl, {vars: u.subst, maps: {}, flags: {}}))
    return {from: [concl, ihc], insts: instancesOf(p2, fs2, {roots: [concl], others: ihc, depth: 2, shapesAt: s?.on ? [ev(s.on.v)] : [], etaAt: [], models: []})}
  }
  const goals = schemes(p2, l).map(goalOf)
  const matchesGoal = (c: DataLaw) => goals.some(g => lemmaUsesFor(p2, fs2, [{law: c, node: 0, concl: encY(p2, c.holds, new Map())}], g.from, g.insts).length > 0)
  const ranked = cands.map(c => ({c, hit: matchesGoal(c)})).sort((a, b) => Number(b.hit) - Number(a.hit))
  const proven: Proven[] = []
  for (const {c, hit} of ranked) {
    if (performance.now() > until) break
    if (refute(c, 200)) continue
    const r = proveWith(p2, fs2, c, proven, 1 + proven.length, opts, Math.min(until, performance.now() + 12000), 5000, [1, 2])
    tried += r.tried
    if (!r.out) continue
    proven.push(r.out)
    if (!hit) continue
    const again = ok(proveWith(p2, fs2, l, proven, 1 + proven.length, opts, until, 8000, [1, 2]), proven, p2)
    if (again) return again
  }
  // Last, deeper, with every lemma proven.
  if (proven.length && performance.now() < until) { const deep = ok(proveWith(p2, fs2, l, proven, 1 + proven.length, opts, until, 12000, [3]), proven, p2); if (deep) return deep }
  return done({proven: false, checked: false, lemmas: proven.map(q => q.law.name), tried, ...stuckOf(first.last)})
}
const stuckOf = (v?: CyclicVerdict) => (v && !v.proven ? {goal: v.goal, stuck: v.stuck} : v && !v.checked ? {goal: 'check', stuck: v.why} : {})

// The law with no cycle: its definitions unfolded, the kernel's prover alone (what the library proves without the search).
export const proveDataToday = (l: DataLaw): DataVerdict => proveData(l, {induction: false})
