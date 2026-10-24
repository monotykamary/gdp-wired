// Step machines: the one source for a stateful rule (a budget, caps, a ledger). From a Machine the library derives
//   - interpret / compileJs: the runtime, as an interpreter and as generated JavaScript
//   - prove: each law by induction (holds at the start, one step preserves it), with every case decided by solver.ts
//   - search: real counterexample traces from the start, by bounded enumeration of short request sequences
// Arithmetic is linear: +, −, × by a constant, min, max, if. Maps are naturals indexed by naturals, every cell starting
// at the same value; a law about a map holds for every key x, and is proven at one arbitrary x (with the law assumed at
// every other key the step reads).
import {boundOf, crossFree, historyMachine, keyTerm, plainKey, scope} from '../kernel/kernel.ts'
import {type Constraint, type Lin, type Verdict, add, env, eq, k, le, lt, nat, scale, show, solve, sub, v} from './solver.ts'

// The searches' random draws: the high bits of a linear congruence (the low ones repeat with a short period).
export type Rand = (k: number) => number
export const seeded = (seed: number): Rand => { let x = seed; return k => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) } }
// Every object in a term, the term first.
export const walk = (t: unknown, f: (o: Record<string, unknown>) => void): void => {
  if (Array.isArray(t)) { for (const x of t) walk(x, f); return }
  if (!t || typeof t !== 'object') return
  const o = t as Record<string, unknown>
  f(o)
  for (const x of Object.values(o)) walk(x, f)
}
// Every object in a term once (arrays too), a part shared by several uses read at its first: a witness read at each of
// its uses in a goal is one object, and a walk of the goal written out would read it at each.
export const walkOnce = (t: unknown, f: (o: object) => void): void => {
  const seen = new Set<object>()
  const go = (x: unknown): void => {
    if (!x || typeof x !== 'object' || seen.has(x)) return
    seen.add(x); f(x)
    for (const y of Object.values(x)) go(y)
  }
  go(t)
}

export type E =
  | {op: 'var', name: string}
  | {op: 'const', value: number}
  | {op: 'add' | 'sub' | 'min' | 'max', a: E, b: E}
  | {op: 'mul', k: number, a: E}
  | {op: 'prod', a: E, b: E} // a product of two terms: only the kernel proves with it (its monomials as atoms)
  | {op: 'if', c: C, then: E, else: E}
  | {op: 'get', map: string, key: E}
export type C =
  | {op: '<' | '<=' | '=', a: E, b: E}
  | {op: 'and', xs: C[]}
  | {op: 'or', xs: C[]}
  | {op: 'not', x: C}
  | {op: 'flag', name: string} // a named condition of the step, decided once per step
  | {op: 'all', key: string, keys?: string[], c: C, witness?: E} // c at every key: only as a whole flag (a quantified flag), the key only as a map's key;
  // in a law, under a not (some key where a condition holds), `witness` may name the key (kernel/prove.ts). A flag may
  // hold at every tuple of keys (`keys` the further ones), each read on its own and compared with another plainly

export type Machine = {
  name: string
  params: string[]
  inputs: string[]
  state: Record<string, E> // initial values, over params
  maps?: Record<string, number> // initial value of every cell
  inputMaps?: string[] // maps each request carries whole (a set of names, say), read like any map; every cell a natural
  step: {flags?: Record<string, C>, state?: Record<string, E>, maps?: Record<string, MapUpdate>}
  pre?: C // about the params alone: a precondition, holding at the start and at every step
  assume?: C // about each request (inputs, and params), e.g. a flag is 0 or 1; holds at a step, not at the start
  history?: History
  // Functions the rule reads and never writes, defined outside it (in Lean, say): each read like a map, at any key.
  // The kernel knows a function only through `facts`; the runtimes compute it with its `js`.
  fns?: Record<string, Fn>
  // What is given about the functions: laws over the params and the functions alone (at every key, with `forall`),
  // assumed in every goal and never proven here. The Lean export states them as the hypothesis they are.
  facts?: Law[]
}
// A function from a key to a natural. `js`: its JavaScript source (k => ...), what the runtimes call; `lean`: a Lean term
// of type Nat → Nat, for an export that proves the facts of this function in Lean.
// A function of several arguments is read at their pairing (core/dsl.ts's argsKey, left-nested (a + b)² + b), which the
// kernel and Lean reason about; `call`, its JavaScript on the `arity` arguments themselves, is what the runtimes call
// where a read's key is that pairing, so no paired key (which passes 2^53 at modest arguments) is ever computed.
export type Fn = {js: string, lean?: string, recur?: Recurrence, arity?: number, call?: string}
// A function defined by a recurrence on its first argument: f(0, args) = zero, f(x + 1, args) = next, which reads x, prev
// (f(x, args)), the further arguments by name and the functions in `uses` by name (a map read at its key); each lemma
// reads x, fx and the arguments, each law between two points x, fx, y, fy (for every x <= y) and the arguments, all
// proven by induction where the function is made. The kernel knows the function by its facts alone; the Lean export
// defines it by the recurrence and proves them there.
export type Recurrence = {args: string[], zero: E, next: E, lemmas: {name: string, holds: C}[], between: {name: string, holds: C}[], uses: Record<string, {arity: number, lean?: string}>,
  // The machines the lemmas and the laws between were proven by (each with its laws), for the Lean export to check again.
  proofs?: {lemmas?: {machine: Machine, laws: Law[]}, between?: {machine: Machine, laws: Law[]}}}
// The events kept so far, each a record of some of its inputs (read as r.<input>). A sum is a state variable worth the
// sum over the history of a term of the record and the params (a count, a total); a query is an input worth the sum over
// the history of a term of the record, the params and the request's other inputs (what code reads from a log at the
// request's own time). A relation, `when` (params and the request's other inputs) implies a <= b (homogeneous, over sums
// and queries), may be assumed at every step once it holds for each single record: both sides are sums over one list.
// With `prune`, the runtimes drop a record once its `order` (a recorded input) plus `after` (a term over the params) is at
// most the request's: the kernel proves such a record adds nothing to any query, and the runtimes refuse a request whose
// order goes back.
export type History = {keep: C, record: string[], sums: Record<string, E>, queries: Record<string, E>, relations?: {when: C, holds: C}[], prune?: {order: string, after: E}}
// A step writes a map at one key, or at every key at once: `each` names the key, read in `value` only as a map's key
// (M[k]), so every key the maps hold nothing at reads alike.
export type MapUpdate = {key: E, value: E} | {each: string, value: E}
// A write at one key, for the parts that take no write at every key (the symbolic prover, the GPU synthesizers, the
// hand-written shader, the first Lean export): they refuse one by name.
export const pointWrite = (w: MapUpdate, where: string): {key: E, value: E} => { if ('each' in w) throw new Error(`${where} takes no write at every key`); return w }
// The same for a quantified flag.
export const noQuantifier = (where: string): never => { throw new Error(`${where} takes no quantified flag`) }
// A law: a condition on the state and params, and for a map law, `forall` names the key variable it holds at.
// `keys`: the further keys, for a law about every two keys or more (after `forall`). `stated`: the law as written, when
// `holds` is the stronger one the prover proved (some key named by a witness).
export type Law = {name: string, holds: C, forall?: string, keys?: string[], stated?: C, some?: string[], witness?: SomeWitness, ex?: SomeProof}
// "There exists" (core/exists.ts): a law with `some` is ∃ those naturals. holds (each read by name in `holds`; an
// integer is two of them, `x` and `x$neg`), after its `forall` key when it has one. The kernel never sees one: it is
// proven through a witness, `witness` if given, else one the prover finds: a term of the state for each (`terms`, the
// law proven is holds with them in place), or each a ghost of the machine (`ghost`: a value at the start, over the
// params, and after each step, over the state before, the request and the ghosts' own values before), the law proven
// is holds over the ghosts. `ex`, on the law the kernel proved, is what it states: ∃ vars. body, with `sub` the
// witnesses in place (holds = body with them substituted) or `ghost` (holds = body, its vars the machine's ghosts).
export type SomeWitness = {terms?: Record<string, E>, ghost?: Record<string, {start: E, step: E}>}
export type SomeProof = {vars: string[], body: C, sub?: Record<string, E>, ghost?: true}

export {unreachable} from '../kernel/kernel.ts'

// Builders.
export const x = (name: string): E => ({op: 'var', name})
export const n = (value: number): E => ({op: 'const', value})
export const plus = (a: E, b: E): E => ({op: 'add', a, b})
export const minus = (a: E, b: E): E => ({op: 'sub', a, b})
export const times = (factor: number, a: E): E => ({op: 'mul', k: factor, a})
export const min = (a: E, b: E): E => ({op: 'min', a, b})
export const max = (a: E, b: E): E => ({op: 'max', a, b})
export const prod = (a: E, b: E): E => ({op: 'prod', a, b})
export const ite = (c: C, then: E, otherwise: E): E => ({op: 'if', c, then, else: otherwise})
export const get = (map: string, key: E): E => ({op: 'get', map, key})
export const less = (a: E, b: E): C => ({op: '<', a, b})
export const atMost = (a: E, b: E): C => ({op: '<=', a, b})
export const same = (a: E, b: E): C => ({op: '=', a, b})
export const all = (...xs: C[]): C => ({op: 'and', xs})
export const any = (...xs: C[]): C => ({op: 'or', xs})
export const not = (c: C): C => ({op: 'not', x: c})
export const bit = (name: string): C => any(same(x(name), n(0)), same(x(name), n(1)))

// --- division and remainder by a constant ------------------------------------------------------------------------
// x div k and x mod k, for a constant k >= 1, are reads of two functions of the rule, div$k and mod$k, at x. The kernel
// knows them by two facts: x = k·div$k(x) + mod$k(x), and mod$k(x) < k (both naturals, as every value is), which fix
// both values (Euclid's division), so a goal about them is Presburger arithmetic the kernel already decides: nothing
// new is trusted. The runtimes compute them as Math.floor(x / k) and x % k; the Lean export defines them as Lean's
// x / k and x % k and proves the two facts of those by omega.
export const divName = (k: number): string => `div$${k}`
export const modName = (k: number): string => `mod$${k}`
const arithRe = /^(div|mod)\$(\d+)$/
export const isArithmetic = (name: string): boolean => arithRe.test(name)
export const divisor = (k: number, what: string): number => {
  if (!Number.isSafeInteger(k) || k < 1) throw new RangeError(`${what} divides by a whole number at least 1, not ${k}`)
  return k
}
// The constants some terms divide by.
export function divisorsIn(ts: readonly (E | C)[], out: Set<number> = new Set()): Set<number> {
  for (const t of ts) for (const m of JSON.stringify(t).matchAll(/"op":"get","map":"(?:div|mod)\$(\d+)"/g)) out.add(Number(m[1]))
  return out
}
// The two functions and their facts for each divisor: what a machine that divides by k declares.
export function arithmetic(ks: Iterable<number>): {fns: Record<string, Fn>, facts: Law[]} {
  const fns: Record<string, Fn> = {}, facts: Law[] = []
  for (const k of [...new Set(ks)].sort((a, b) => a - b)) {
    const d = divName(k), r = modName(k), key = `x$${r}`, at = (map: string): E => get(map, x(key))
    fns[d] = {js: `x => Math.floor(x / ${k})`, lean: `fun x => x / ${k}`}
    fns[r] = {js: `x => x % ${k}`, lean: `fun x => x % ${k}`}
    facts.push({name: `${r}: x = ${k}·(x div ${k}) + x mod ${k}`, forall: key, holds: same(x(key), plus(times(k, at(d)), at(r)))},
      {name: `${r}: x mod ${k} < ${k}`, forall: key, holds: less(at(r), n(k))})
  }
  return {fns, facts}
}
// A machine with the functions and facts of every divisor its terms (or the laws given) read, those it lacks added.
export function withArithmetic(m: Machine, more: readonly (E | C)[] = [], ks: Iterable<number> = []): Machine {
  const all = divisorsIn(more, divisorsIn(machineTerms(m), new Set(ks)))
  const {fns, facts} = arithmetic([...all].filter(k => !m.fns?.[modName(k)]))
  if (!Object.keys(fns).length) return m
  return {...m, fns: {...m.fns, ...fns}, facts: [...(m.facts ?? []), ...facts]}
}
// Every term and condition a machine holds.
export const machineTerms = (m: Machine): (E | C)[] => [...Object.values(m.state), ...Object.values(m.step.flags ?? {}), ...Object.values(m.step.state ?? {}),
  ...Object.values(m.step.maps ?? {}).flatMap(w => ('key' in w ? [w.key, w.value] : [w.value])), ...(m.pre ? [m.pre] : []), ...(m.assume ? [m.assume] : []),
  ...(m.facts ?? []).map(f => f.holds), ...(m.history ? [m.history.keep, ...Object.values(m.history.sums), ...Object.values(m.history.queries), ...(m.history.relations ?? []).flatMap(r => [r.when, r.holds])] : [])]

// --- the runtime ---------------------------------------------------------------------------------------------------

// Both runtimes compute over the naturals the proofs are about only while values stay JavaScript's exact integers: every
// param and input must be a natural below 2^53, and a sum or product past 2^53 - 1 throws rather than rounds. A machine
// runs only once the kernel's scope check accepts it, and the runtimes read only the params and inputs it declares, so a
// misspelled name, a missing input or a stray one fails loudly instead of running as undefined.
//
// A machine with a history runs as kernel.ts's plain machine (its sums as state) beside the records it keeps: each
// query is computed from the records at the request's own time. With `prune`, a request whose order goes back is
// refused and the records the kernel proved spent are dropped.

// history and last only with a history (last only when it is pruned). A map reads its cells, and past them its
// default: the map's initial value until a write at every key sets a new one (defaults).
export type State = {scalars: Record<string, number>, maps: Record<string, Map<number, number>>, defaults?: Record<string, number>, history?: Env[], last?: number}
type Env = Record<string, number>
// A request: its inputs, and the maps it carries (a ReadonlyMap each, cells past it read 0).
export type Request = Record<string, number | ReadonlyMap<number, number>>
// A condition at every key, or a value at every key. Where the bound key is read only as a map's key, each key a map
// read holds a cell at, and one key past them all (where every map reads its default), are every case there is.
const mapsIn = (t: E | C): string[] => [...new Set([...JSON.stringify(t).matchAll(/"op":"get","map":"([^"]+)"/g)].map(x => x[1]!))]
function keysAt(st: State, maps: string[]): number[] {
  const keys = new Set<number>()
  let past = 0
  for (const cells of Object.values(st.maps)) for (const key of cells.keys()) past = Math.max(past, key + 1)
  for (const map of maps) for (const key of st.maps[map]?.keys() ?? []) keys.add(key)
  return [...keys, past]
}
// Where it is read in key terms (k + e, k ∸ e, compared): the value changes only next to a breakpoint (a cell of a map
// read at a key term, or a compared value, shifted by the term's offset; and the offset itself for k ∸ e), so each
// breakpoint p with p - 1 .. p + 2, 0, and one past them all are every case: between two keys that are none of those,
// no comparison turns and no read moves onto a cell.
type Breaks = {reads: {map: string, off?: E, minus: boolean}[], cmps: {value: E, off?: E, minus: boolean}[]}
const breaksCache = new WeakMap<object, Map<string, Breaks>>()
function breaksOf(t: E | C, key: string): Breaks {
  const hit = breaksCache.get(t)?.get(key)
  if (hit) return hit
  const out: Breaks = {reads: [], cmps: []}
  const termOf = (e: E): {off?: E, minus: boolean} => (e.op === 'var' ? {minus: false} : e.op === 'add' ? {off: e.a.op === 'var' && e.a.name === key ? e.b : e.a, minus: false} : {off: (e as {b: E}).b, minus: true})
  const walk = (u: E | C): void => {
    if (u.op === 'get' && keyTerm(u.key, key)) { out.reads.push({map: u.map, ...termOf(u.key)}); return }
    if ((u.op === '<' || u.op === '<=' || u.op === '=') && (keyTerm(u.a, key) || keyTerm(u.b, key))) {
      const [kt, other] = keyTerm(u.a, key) ? [u.a, u.b] : [u.b, u.a]
      out.cmps.push({value: other, ...termOf(kt)}); walk(other); return
    }
    for (const v of Object.values(u)) if (v && typeof v === 'object') (Array.isArray(v) ? v : [v]).forEach(y => walk(y as E | C))
  }
  walk(t)
  if (!breaksCache.has(t)) breaksCache.set(t, new Map())
  breaksCache.get(t)!.set(key, out)
  return out
}
function breakKeys(b: Breaks, env: Env, st: State, m: Machine): number[] {
  const points = new Set<number>([0])
  for (const r of b.reads) {
    const d = r.off ? evalE(r.off, env, st, m) : 0
    for (const s of st.maps[r.map]?.keys() ?? []) { if (r.minus) points.add(s + d); else if (s >= d) points.add(s - d) }
    if (r.minus) points.add(d)
  }
  for (const c of b.cmps) {
    const v = evalE(c.value, env, st, m), d = c.off ? evalE(c.off, env, st, m) : 0
    if (c.minus) { points.add(v + d); points.add(d) } else if (v >= d) points.add(v - d)
  }
  const keys = new Set<number>()
  for (const p of points) for (let i = -1; i <= 2; i++) if (p + i >= 0) keys.add(p + i)
  const sorted = [...keys].sort((a, b) => a - b)
  return [...sorted, sorted.at(-1)! + 1]
}
// A condition at every tuple of n keys: the breakpoints of each key (each read on its own, the comparisons between two
// of them set aside) together, each case with the n - 1 keys after it. Every stretch where no read moves and no
// comparison turns starts at one of those cases (a breakpoint, the key after one, or 0), so the keys after its start
// place n keys there in every order they can take; keys read only as a map's key need only the cells and one past them.
// Keys read only as a map's key and compared with each other: a read changes only at a cell, so each cell, the n keys
// after it (the stretch up to the next cell), 0 and the n after it, and past the last cell are every case.
function tupleKeys(c: Extract<C, {op: 'all'}>, env: Env, st: State, m: Machine): number[] {
  const names = boundOf(c)
  if (names.every(n => plainKey(c.c, n))) return keysAt(st, mapsIn(c.c))
  if (names.length === 1) return breakKeys(breaksOf(c.c, c.key), env, st, m)
  const body = crossFree(c.c, names)
  if (names.every(n => plainKey(body, n))) return spread([0, ...keysAt(st, mapsIn(c.c))], names.length + 1)
  const parts = names.map(n => breaksOf(body, n))
  return spread(breakKeys({reads: parts.flatMap(b => b.reads), cmps: parts.flatMap(b => b.cmps)}, env, st, m), names.length)
}
const spread = (keys: number[], n: number): number[] => [...new Set(keys.flatMap(k => Array.from({length: n}, (_, i) => k + i)))].sort((a, b) => a - b)
export const naturalIn = (v: unknown, what: string): number => {
  if (typeof v !== 'number' || !Number.isSafeInteger(v) || v < 0) throw new RangeError(`${what} must be a natural below 2^53, not ${String(v)}`)
  return v
}
const exact = (v: number): number => {
  if (v > Number.MAX_SAFE_INTEGER) throw new RangeError('a value passed 2^53 - 1, past which the proofs over the naturals no longer describe the run')
  return v
}

export function evalE(e: E, env: Env, st: State, m: Machine): number {
  switch (e.op) {
    case 'var': { const v = env[e.name] ?? st.scalars[e.name]; if (v === undefined) throw new Error(`no value for ${e.name}`); return v }
    case 'const': return e.value
    case 'add': return exact(evalE(e.a, env, st, m) + evalE(e.b, env, st, m))
    case 'sub': return Math.max(0, evalE(e.a, env, st, m) - evalE(e.b, env, st, m))
    case 'mul': return exact(e.k * evalE(e.a, env, st, m))
    case 'prod': return exact(evalE(e.a, env, st, m) * evalE(e.b, env, st, m))
    case 'min': return Math.min(evalE(e.a, env, st, m), evalE(e.b, env, st, m))
    case 'max': return Math.max(evalE(e.a, env, st, m), evalE(e.b, env, st, m))
    case 'if': return evalC(e.c, env, st, m) ? evalE(e.then, env, st, m) : evalE(e.else, env, st, m)
    case 'get': {
      const fn = m.fns?.[e.map], args = fn?.call ? pairedArgs(e.key, fn.arity!) : undefined
      if (args) { const xs = args.map(a => evalE(a, env, st, m)); return naturalIn(callOf(fn!)(...xs), `${e.map}(${xs.join(', ')})`) }
      const key = evalE(e.key, env, st, m)
      return fn ? naturalIn(fnOf(fn)(key), `${e.map}(${key})`) : st.maps[e.map]!.get(key) ?? st.defaults?.[e.map] ?? m.maps![e.map]!
    }
  }
}
// A function's value at a key (the GPU search tabulates functions with it).
export const fnValue = (fn: Fn, key: number): number => naturalIn(fnOf(fn)(key), `a function at ${key}`)
// A function's JavaScript, compiled once.
const compiledFns = new WeakMap<Fn, (key: number) => number>()
const fnOf = (fn: Fn): ((key: number) => number) => {
  let f = compiledFns.get(fn)
  if (!f) { f = compileFunction<(key: number) => number>(['k'], `return (${fn.js})(k)`); compiledFns.set(fn, f) }
  return f
}
const compiledCalls = new WeakMap<Fn, (...args: number[]) => number>()
const callOf = (fn: Fn): ((...args: number[]) => number) => {
  let f = compiledCalls.get(fn)
  if (!f) { f = compileFunction<() => (...args: number[]) => number>([], `return (${fn.call})`)(); compiledCalls.set(fn, f) }
  return f
}
// A key of several arguments: their pairing, left-nested, ((a, b), c)..., each pair (s)² + b with s = a + b.
export const pairE = (a: E, b: E): E => { const s = plus(a, b); return plus(prod(s, s), b) }
export const argsKey = (args: E[]): E => args.slice(1).reduce(pairE, args[0]!)
// The n arguments a key pairs (argsKey's), if it is their pairing.
const paired = new WeakMap<E, Map<number, E[] | undefined>>()
export function pairedArgs(key: E, n: number): E[] | undefined {
  let byN = paired.get(key)
  if (!byN) paired.set(key, (byN = new Map()))
  if (byN.has(n)) return byN.get(n)
  let out: E[] | undefined
  if (n === 1) out = [key]
  else if (key.op === 'add' && key.a.op === 'prod' && key.a.a.op === 'add' && alike(key.a.a, key.a.b) && alike(key.a.a.b, key.b)) {
    const first = pairedArgs(key.a.a.a, n - 1)
    out = first && [...first, key.b]
  }
  byN.set(n, out)
  return out
}
const alike = (a: E, b: E): boolean => a === b || JSON.stringify(a) === JSON.stringify(b)
export function evalC(c: C, env: Env, st: State, m: Machine): boolean {
  switch (c.op) {
    case '<': return evalE(c.a, env, st, m) < evalE(c.b, env, st, m)
    case '<=': return evalE(c.a, env, st, m) <= evalE(c.b, env, st, m)
    case '=': return evalE(c.a, env, st, m) === evalE(c.b, env, st, m)
    case 'and': return c.xs.every(y => evalC(y, env, st, m))
    case 'or': return c.xs.some(y => evalC(y, env, st, m))
    case 'not': return !evalC(c.x, env, st, m)
    case 'flag': return env[`?${c.name}`] === 1
    case 'all': {
      const names = boundOf(c), keys = tupleKeys(c, env, st, m)
      const go = (i: number, at: Env): boolean => (i === names.length ? evalC(c.c, at, st, m) : keys.every(key => go(i + 1, {...at, [names[i]!]: key})))
      return go(0, env)
    }
  }
}
// A write at every key: its value at each key the maps it reads hold a cell at, and its new default past them.
// With the key in key terms, every key up to the last breakpoint is computed (the stretches between breakpoints hold the
// same value, which need not be the default), and past it the value is the new default.
function writeEvery(w: {each: string, value: E}, env: Env, st: State, m: Machine): {cells: Map<number, number>, default: number} {
  if (!plainKey(w.value, w.each)) {
    const top = breakKeys(breaksOf(w.value, w.each), env, st, m).at(-1)!
    if (top > 1_000_000) throw new RangeError(`a write at every key reads its key in arithmetic past a million keys (${top})`)
    const fallback = evalE(w.value, {...env, [w.each]: top}, st, m), cells = new Map<number, number>()
    for (let key = 0; key < top; key++) { const v = evalE(w.value, {...env, [w.each]: key}, st, m); if (v !== fallback) cells.set(key, v) }
    return {cells, default: fallback}
  }
  const keys = keysAt(st, mapsIn(w.value)), past = keys.at(-1)!
  const fallback = evalE(w.value, {...env, [w.each]: past}, st, m), cells = new Map<number, number>()
  for (const key of keys.slice(0, -1)) { const v = evalE(w.value, {...env, [w.each]: key}, st, m); if (v !== fallback) cells.set(key, v) }
  return {cells, default: fallback}
}

// The machine a runtime steps (with a history, kernel.ts's plain machine), its queries, and the inputs a request carries.
function runnable(m: Machine) {
  const h = m.history
  if (!h) scope(m)
  const plain = h ? historyMachine(m).machine : m
  const queries = h ? Object.keys(h.queries) : []
  return {h, plain, queries, carried: m.inputs.filter(i => !queries.includes(i))}
}
const empty: State = {scalars: {}, maps: {}}

// The state as a step reads it: with the maps the request carries (cells past them read 0), each checked natural.
export function carriedView(m: Machine, st: State, input: Request, rename: (map: string) => string = map => map): State {
  if (!m.inputMaps?.length) return st
  const maps = {...st.maps}, defaults = {...st.defaults}
  for (const map of m.inputMaps) {
    const cells = input[map]
    if (!(cells instanceof Map)) throw new RangeError(`input ${map} must be a Map of naturals`)
    for (const [key, v] of cells) { naturalIn(key, `a key of ${map}`); naturalIn(v, `a cell of ${map}`) }
    maps[rename(map)] = cells as Map<number, number>
    defaults[rename(map)] = 0
  }
  return {...st, maps, defaults}
}
// A request's numbers (its inputs), without the maps it carries.
export const numbersOf = (input: Request): Record<string, number> => Object.fromEntries(Object.entries(input).filter((e): e is [string, number] => typeof e[1] === 'number'))

// A request the rule's assumption refuses: the proofs say nothing about the step it would take, so neither runtime takes
// it (a caller that may send one checks first, as gdp-wired/gdp's gate does).
const refused = (m: Machine) => `${m.name}: the request fails the rule's assumption, so no proof covers the step it would take`
// The interpreter: persistent (a step leaves the state it was given as it was), so searches can branch from any state.
export function interpret(m: Machine) {
  const {h, plain, carried} = runnable(m)
  const args = (params: Env, input?: Request): Env => {
    const env: Env = {}
    for (const p of m.params) env[p] = naturalIn(params[p], `param ${p}`)
    if (input) for (const i of carried) env[i] = naturalIn(input[i], `input ${i}`)
    return env
  }
  const viewed = (st: State, input: Request): State => carriedView(m, st, input)
  // The records a request's queries read: with pruning, those not yet spent at its order.
  const live = (env: Env, st: State): Env[] => {
    const records = st.history!
    if (!h!.prune) return records
    const {order, after} = h!.prune, by = evalE(after, env, empty, m)
    let first = 0
    while (first < records.length && exact(records[first]![order]! + by) <= env[order]!) first++
    return first ? records.slice(first) : records
  }
  const queriesOf = (env: Env, records: Env[]): Env => {
    const out: Env = {}
    for (const [q, g] of Object.entries(h!.queries)) {
      let total = 0
      for (const r of records) { for (const f of h!.record) env[`r.${f}`] = r[f]!; total = exact(total + evalE(g, env, empty, m)) }
      out[q] = total
    }
    return out
  }
  const ordered = (env: Env, st: State) => {
    if (h?.prune && st.last !== undefined && env[h.prune.order]! < st.last) throw new RangeError(`${m.name}: requests come in nondecreasing ${h.prune.order} (${env[h.prune.order]} after ${st.last})`)
  }
  return {
    init: (params: Env): State => {
      const env = args(params)
      return {
        scalars: Object.fromEntries(Object.entries(plain.state).map(([name, e]) => [name, evalE(e, env, empty, plain)])),
        maps: Object.fromEntries(Object.keys(plain.maps ?? {}).map(name => [name, new Map()])),
        ...(h ? {history: []} : {}),
      }
    },
    // The queries a request would read (none without a history).
    queries: (params: Env, st: State, input: Request): Env => {
      if (!h) return {}
      const env = args(params, input)
      ordered(env, st)
      return queriesOf(env, live(env, st))
    },
    step: (params: Env, given: State, input: Request): State => {
      const env = args(params, input), st = viewed(given, input)
      let records: Env[] = []
      if (h) { ordered(env, st); records = live(env, st); Object.assign(env, queriesOf(env, records)) }
      for (const [name, c] of Object.entries(plain.step.flags ?? {})) env[`?${name}`] = evalC(c, env, st, plain) ? 1 : 0
      if (m.assume && !evalC(m.assume, env, st, plain)) throw new RangeError(refused(m))
      const scalars = {...st.scalars}
      for (const [name, e] of Object.entries(plain.step.state ?? {})) scalars[name] = evalE(e, env, st, plain)
      const writes = Object.entries(plain.step.maps ?? {}).map(([name, w]) => [name, 'each' in w ? writeEvery(w, env, st, plain) : {key: evalE(w.key, env, st, plain), value: evalE(w.value, env, st, plain)}] as const)
      const maps = Object.fromEntries(Object.entries(given.maps).map(([name, cells]) => [name, new Map(cells)]))
      const defaults = {...given.defaults}
      for (const [name, w] of writes) if ('cells' in w) { maps[name] = w.cells; defaults[name] = w.default } else maps[name]!.set(w.key, w.value)
      const withDefaults = Object.keys(defaults).length ? {defaults} : {}
      if (!h) return {scalars, maps, ...withDefaults}
      const kept = evalC(h.keep, env, st, plain)
      return {scalars, maps, history: kept ? [...records, Object.fromEntries(h.record.map(f => [f, env[f]!]))] : records, ...(h.prune ? {last: env[h.prune.order]} : {})}
    },
  }
}

// The same machine as JavaScript source: what an app ships. A step reads the state it was given (every query, flag,
// scalar, key and value first), then writes the maps and the records in place, so it costs the same however large they
// grow; the state passed in is consumed. fork copies a state to branch from.
// The runtime's helpers: a compiled module declares the ones it calls (and the ones those call), no others.
const RUNTIME: [string, string][] = [
  ['$n', `function $n(v, what) { if (typeof v !== 'number' || !Number.isSafeInteger(v) || v < 0) throw new RangeError(what + ' must be a natural below 2^53, not ' + v); return v; }`],
  ['$x', `function $x(v) { if (v > 9007199254740991) throw new RangeError('a value passed 2^53 - 1, past which the proofs over the naturals no longer describe the run'); return v; }`],
  ['$m', `function $m(v, what) { if (!(v instanceof Map)) throw new RangeError(what + ' must be a Map of naturals'); for (const [key, x] of v) { $n(key, 'a key of ' + what); $n(x, 'a cell of ' + what); } return v; }`],
  ['$keys', `function $keys(maps, names) { const keys = new Set(); let past = 0; for (const c of Object.values(maps)) for (const key of c.keys()) past = Math.max(past, key + 1); for (const n of names) for (const key of maps[n].keys()) keys.add(key); return [...keys, past]; }`],
  ['$breaks', `function $breaks(maps, reads, cmps) { const p = new Set([0]); for (const [n, d, minus] of reads) { for (const s of maps[n].keys()) { if (minus) p.add(s + d); else if (s >= d) p.add(s - d); } if (minus) p.add(d); } for (const [v, d, minus] of cmps) { if (minus) { p.add(v + d); p.add(d); } else if (v >= d) p.add(v - d); } const keys = new Set(); for (const q of p) for (let i = -1; i <= 2; i++) if (q + i >= 0) keys.add(q + i); const sorted = [...keys].sort((a, b) => a - b); sorted.push(sorted[sorted.length - 1] + 1); return sorted; }`],
  // A condition at every two keys that holds wherever x(k) differs from y(k1): only the pairs whose values match are read.
  ['$join', `function $join(ks, x, y, f) { const by = new Map(); for (const k1 of ks) { const v = y(k1), l = by.get(v); if (l) l.push(k1); else by.set(v, [k1]); } return ks.every(k => { const l = by.get(x(k)); return l === undefined || l.every(k1 => f(k, k1)); }); }`],
  ['$spread', `function $spread(keys, n) { const out = new Set(); for (const k of keys) for (let i = 0; i < n; i++) out.add(k + i); return [...out].sort((a, b) => a - b); }`],
  ['$dense', `function $dense(keys, f) { const top = keys[keys.length - 1]; if (top > 1000000) throw new RangeError('a write at every key reads its key in arithmetic past a million keys (' + top + ')'); const d = f(top), cells = new Map(); for (let k = 0; k < top; k++) { const v = f(k); if (v !== d) cells.set(k, v); } return {cells, d}; }`],
  ['$every', `function $every(keys, f) { const past = keys[keys.length - 1], d = f(past), cells = new Map(); for (let i = 0; i < keys.length - 1; i++) { const v = f(keys[i]); if (v !== d) cells.set(keys[i], v); } return {cells, d}; }`],
]
function runtimeFor(code: string): string {
  const used = new Set<string>()
  for (let grew = true; grew;) {
    grew = false
    const text = code + RUNTIME.filter(([name]) => used.has(name)).map(([, src]) => src).join('')
    for (const [name] of RUNTIME) if (!used.has(name) && text.includes(`${name}(`)) { used.add(name); grew = true }
  }
  return RUNTIME.filter(([name]) => used.has(name)).map(([, src]) => `${src}\n`).join('')
}

// A condition over two keys, k and k1, that holds wherever a term of k alone differs from a term of k1 alone: an
// implication (a not-and, or an or with one) whose premises include x(k) = y(k1). The runtime then reads only the pairs
// whose values match ($join), the rest holding by the premise: rows plus matches, not rows squared.
function joinOf(c: C, k: string, k1: string): {x: E, y: E} | undefined {
  const reads = (t: E | C, key: string) => JSON.stringify(t).includes(`"op":"var","name":${JSON.stringify(key)}`)
  const premises = c.op === 'not' && c.x.op === 'and' ? c.x.xs : c.op === 'or' ? c.xs.flatMap(x => (x.op === 'not' ? (x.x.op === 'and' ? x.x.xs : [x.x]) : [])) : []
  for (const p of premises) {
    if (p.op !== '=') continue
    if (reads(p.a, k) && !reads(p.a, k1) && reads(p.b, k1) && !reads(p.b, k)) return {x: p.a, y: p.b}
    if (reads(p.b, k) && !reads(p.b, k1) && reads(p.a, k1) && !reads(p.a, k)) return {x: p.b, y: p.a}
  }
  return undefined
}

export function compileJs(m: Machine): string {
  const {h, plain, queries, carried} = runnable(m)
  const id = (name: string) => JSON.stringify(name)
  const flags = Object.keys(plain.step.flags ?? {}), carriedMaps = m.inputMaps ?? [], fns = Object.keys(m.fns ?? {})
  // A key bound by a quantified flag or a write at every key is the JS parameter k (k1, k2 for a flag's further keys).
  let bound: Record<string, string> = {}
  const ex = (e: E): string => {
    switch (e.op) {
      case 'var': return bound[e.name] ?? (e.name.startsWith('r.') ? `r[${id(e.name.slice(2))}]` : plain.params.includes(e.name) || plain.inputs.includes(e.name) ? `env[${id(e.name)}]` : `s[${id(e.name)}]`)
      case 'const': return String(e.value)
      case 'add': return `$x(${ex(e.a)} + ${ex(e.b)})`
      case 'sub': return `Math.max(0, ${ex(e.a)} - ${ex(e.b)})`
      case 'mul': return `$x(${e.k} * ${ex(e.a)})`
      case 'prod': return `$x(${ex(e.a)} * ${ex(e.b)})`
      case 'min': return `Math.min(${ex(e.a)}, ${ex(e.b)})`
      case 'max': return `Math.max(${ex(e.a)}, ${ex(e.b)})`
      case 'if': return `(${cx(e.c)} ? ${ex(e.then)} : ${ex(e.else)})`
      case 'get': {
        const fn = m.fns?.[e.map], args = fn?.call ? pairedArgs(e.key, fn.arity!) : undefined
        if (args) return `$n(fnc${fns.indexOf(e.map)}(${args.map(ex).join(', ')}), ${id(`${e.map}()`)})`
        return fns.includes(e.map) ? `$n(fn${fns.indexOf(e.map)}(${ex(e.key)}), ${id(`${e.map}()`)})` : `(maps[${id(e.map)}].get(${ex(e.key)}) ?? ${carriedMaps.includes(e.map) ? '0' : `dft[${id(e.map)}] ?? ${plain.maps![e.map]}`})`
      }
    }
  }
  const cx = (c: C): string => {
    switch (c.op) {
      case '<': return `(${ex(c.a)} < ${ex(c.b)})`
      case '<=': return `(${ex(c.a)} <= ${ex(c.b)})`
      case '=': return `(${ex(c.a)} === ${ex(c.b)})`
      case 'and': return `(${c.xs.map(cx).join(' && ')})`
      case 'or': return `(${c.xs.map(cx).join(' || ')})`
      case 'not': return `(!${cx(c.x)})`
      case 'flag': return `flag${flags.indexOf(c.name)}`
      case 'all': {
        const names = boundOf(c), ks = names.map((_, i) => (i ? `k${i}` : 'k')), keys = names.length === 1 ? keysJs(c.c, c.key) : tupleJs(c), outer = bound
        bound = {...bound, ...Object.fromEntries(names.map((n, i) => [n, ks[i]!]))}
        const body = cx(c.c)
        bound = outer
        if (names.length === 2) {
          const j = joinOf(c.c, names[0]!, names[1]!)
          if (j) {
            bound = {...bound, [names[0]!]: 'k', [names[1]!]: 'k1'}
            const x = ex(j.x), y = ex(j.y)
            bound = outer
            return `$join(${keys}, k => ${x}, k1 => ${y}, (k, k1) => ${body})`
          }
        }
        return names.length === 1 ? `${keys}.every(k => ${body})` : `(ks => ${ks.map(k => `ks.every(${k} => `).join('')}${body}${')'.repeat(ks.length)})(${keys})`
      }
    }
  }
  // The keys a quantifier or a write at every key is decided on (the interpreter's keysAt, or its breakKeys).
  const keysJs = (t: E | C, key: string): string => {
    if (plainKey(t, key)) return `$keys(maps, ${JSON.stringify(mapsIn(t).filter(mp => !fns.includes(mp)))})`
    return breaksJs(breaksOf(t, key))
  }
  const breaksJs = (b: Breaks): string => {
    const off = (o?: E) => (o ? ex(o) : '0')
    return `$breaks(maps, [${b.reads.map(r => `[${id(r.map)}, ${off(r.off)}, ${r.minus}]`).join(', ')}], [${b.cmps.map(c => `[${ex(c.value)}, ${off(c.off)}, ${c.minus}]`).join(', ')}])`
  }
  // The interpreter's tupleKeys.
  const tupleJs = (c: Extract<C, {op: 'all'}>): string => {
    const names = boundOf(c)
    if (names.every(n => plainKey(c.c, n))) return `$keys(maps, ${JSON.stringify(mapsIn(c.c).filter(mp => !fns.includes(mp)))})`
    const body = crossFree(c.c, names)
    if (names.every(n => plainKey(body, n))) return `$spread([0, ...$keys(maps, ${JSON.stringify(mapsIn(c.c).filter(mp => !fns.includes(mp)))})], ${names.length + 1})`
    const parts = names.map(n => breaksOf(body, n))
    return `$spread(${breaksJs({reads: parts.flatMap(b => b.reads), cmps: parts.flatMap(b => b.cmps)})}, ${names.length})`
  }
  const every = (w: {each: string, value: E}) => { const keys = keysJs(w.value, w.each), dense = !plainKey(w.value, w.each), outer = bound; bound = {[w.each]: 'k'}; const body = ex(w.value); bound = outer; return `${dense ? '$dense' : '$every'}(${keys}, k => ${body})` }
  const writes = Object.entries(plain.step.maps ?? {})
  const env = (input: boolean) => `{${[...m.params.map(p => `${id(p)}: $n(params[${id(p)}], ${id(`param ${p}`)})`), ...(input ? carried.map(i => `${id(i)}: $n(input[${id(i)}], ${id(`input ${i}`)})`) : [])].join(', ')}}`
  // Reads go through `maps` (with the maps the request carries); writes go to the state's own.
  const lines = [`const env = ${env(true)}, s = state.scalars, dft = {...state.defaults}, maps = ${carriedMaps.length ? `{...state.maps, ${carriedMaps.map(mp => `${id(mp)}: $m(input[${id(mp)}], ${id(`input ${mp}`)})`).join(', ')}}` : 'state.maps'};`]
  if (h) {
    lines.push('const records = state.history;', 'let head = state.head;')
    if (h.prune) {
      const order = id(h.prune.order)
      lines.push(`const order = env[${order}];`,
        `if (state.last !== undefined && order < state.last) throw new RangeError(${id(`${m.name}: requests come in nondecreasing ${h.prune.order}`)} + \` (\${order} after \${state.last})\`);`,
        `const after = ${ex(h.prune.after)};`,
        `while (head < records.length && $x(records[head][${order}] + after) <= order) head++;`)
    }
    lines.push(`let ${queries.map((_, i) => `q${i} = 0`).join(', ')};`,
      `for (let i = head; i < records.length; i++) { const r = records[i]; ${queries.map((q, i) => `q${i} = $x(q${i} + ${ex(h.queries[q]!)});`).join(' ')} }`,
      ...queries.map((q, i) => `env[${id(q)}] = q${i};`))
  }
  lines.push(...flags.map((name, i) => `const flag${i} = ${cx(plain.step.flags![name]!)};`),
    // The rule's own assumption, as `allowed` (core/watch.ts) reads it (a history's machine assumes more: its relations).
    ...(m.assume ? [`if (!${cx(m.assume)}) throw new RangeError(${id(refused(m))});`] : []),
    `const scalars = {...s, ${Object.entries(plain.step.state ?? {}).map(([name, e]) => `${id(name)}: ${ex(e)}`).join(', ')}};`,
    ...writes.map(([, w], i) => ('each' in w ? `const write${i} = ${every(w)};` : `const key${i} = ${ex(w.key)}, value${i} = ${ex(w.value)};`)))
  if (h) lines.push(`const keep = ${cx(h.keep)};`)
  lines.push(...writes.map(([name, w], i) => ('each' in w ? `state.maps[${id(name)}] = write${i}.cells; dft[${id(name)}] = write${i}.d;` : `state.maps[${id(name)}].set(key${i}, value${i});`)))
  if (h) lines.push(`if (keep) records.push({${h.record.map(f => `${id(f)}: env[${id(f)}]`).join(', ')}});`,
    // Drop the spent prefix now and then, not every step: amortized, each record is moved a bounded number of times.
    'if (head > 1024 && 2 * head > records.length) { records.splice(0, head); head = 0; }',
    `return {scalars, maps: state.maps, history: records, head${h.prune ? ', last: order' : ''}};`)
  else lines.push('return Object.keys(dft).length ? {scalars, maps: state.maps, defaults: dft} : {scalars, maps: state.maps};')
  const fnDefs = fns.map((name, i) => `const fn${i} = (${m.fns![name]!.js});\n${m.fns![name]!.call ? `const fnc${i} = (${m.fns![name]!.call});\n` : ''}`).join('')
  const code = `export function init(params) {
  const env = ${env(false)}, s = {};
  return {scalars: {${Object.entries(plain.state).map(([name, e]) => `${id(name)}: ${ex(e)}`).join(', ')}}, maps: {${Object.keys(plain.maps ?? {}).map(name => `${id(name)}: new Map()`).join(', ')}}${h ? ', history: [], head: 0' : ''}};
}
export function fork(state) {
  return {scalars: {...state.scalars}, maps: Object.fromEntries(Object.entries(state.maps).map(([name, cells]) => [name, new Map(cells)])), ...(state.defaults ? {defaults: {...state.defaults}} : {})${h ? ', history: state.history.slice(state.head), head: 0, last: state.last' : ''}};
}
export function step(params, state, input) {
  ${lines.join('\n  ')}
}
`
  return `// Generated from the machine ${m.name}. step consumes its state: keep the one it returns (fork to branch).
${runtimeFor(fnDefs + code)}${fnDefs}${code}`
}

// Generated code as a function. Every caller passes source this library generated from its own terms, or a function's
// `js` the rule's author wrote (code, as the rule itself is), never data; the lint's implied-eval rule is waived here
// and nowhere else.
export function compileFunction<F>(params: string[], body: string): F {
  // oxlint-disable-next-line typescript/no-implied-eval
  return new Function(...params, body) as F
}
// compileJs's module, loaded: init, fork and step.
export type Compiled = {init: (params: object) => State & {head?: number}, fork: (st: State) => State, step: (params: object, st: State, input: object) => State & {head?: number}}
export const loadJs = (m: Machine): Compiled => compileFunction<() => Compiled>([], `${compileJs(m).replace(/^export function/gm, 'function')}\nreturn {init, fork, step}`)()

// --- symbolic: from expressions to cases of linear constraints -------------------------------------------------------

type Cases<T> = {path: Constraint[], value: T}[]
// How map reads resolve. A focus cell is a map cell the law under proof talks about, at a key expression; a read at a
// key equal to a focus key is that cell. Any other read is a cell named by its map and key (the same cell for the same
// key within one case), about which the laws that hold at every key are assumed.
type Focus = {map: string, key: Lin, cell: string}
type Reads = {focus: Focus[], other: (map: string, key: Lin) => {cell: string, assume: Constraint[][]}}
// decided: how a step's key compares with each focus key, chosen once per case ('eq' or 'apart'), so reads don't re-split.
type Sym = {names: Record<string, Lin>, reads: Reads, flags?: Record<string, boolean>, decided?: Record<string, 'eq' | 'apart'>}

const cross = <A, B>(as: Cases<A>, f: (a: A) => Cases<B>): Cases<B> => as.flatMap(a => f(a.value).map(b => ({path: [...a.path, ...b.path], value: b.value})))
// Every way a key can differ from each of some focus keys.
const apartFrom = (key: Lin, keys: Lin[]): Constraint[][] => keys.reduce<Constraint[][]>((acc, f) => acc.flatMap(p => [[...p, ...lt(key, f)], [...p, ...lt(f, key)]]), [[]])

function symE(e: E, s: Sym): Cases<Lin> {
  switch (e.op) {
    case 'var': return [{path: [], value: s.names[e.name] ?? v(e.name)}]
    case 'const': return [{path: [], value: k(e.value)}]
    case 'add': return cross(symE(e.a, s), a => symE(e.b, s).map(b => ({path: b.path, value: add(a, b.value)})))
    case 'mul': return symE(e.a, s).map(a => ({path: a.path, value: scale(a.value, e.k)}))
    case 'prod': throw new Error('a product of two terms: kernel/prove.ts proves with products, this prover does not')
    case 'sub': // truncated at 0, as on naturals
      return cross(symE(e.a, s), a => symE(e.b, s).flatMap(b => [
        {path: [...b.path, ...le(b.value, a)], value: sub(a, b.value)},
        {path: [...b.path, ...lt(a, b.value)], value: k(0)},
      ]))
    case 'min': case 'max':
      return cross(symE(e.a, s), a => symE(e.b, s).flatMap(b => {
        const aFirst = e.op === 'min' ? le(a, b.value) : le(b.value, a)
        const bFirst = e.op === 'min' ? lt(b.value, a) : lt(a, b.value)
        return [{path: [...b.path, ...aFirst], value: a}, {path: [...b.path, ...bFirst], value: b.value}]
      }))
    case 'if':
      return [...cross(symC(e.c, s, true), () => symE(e.then, s)), ...cross(symC(e.c, s, false), () => symE(e.else, s))]
    case 'get':
      return symE(e.key, s).flatMap(key => {
        const focus = s.reads.focus.filter(f => f.map === e.map)
        const ids = focus.map(f => `${show(key.value)}|${show(f.key)}`)
        if (s.decided && ids.every(id => id in s.decided!)) {
          const hit = focus.find((_, i) => s.decided![ids[i]!] === 'eq')
          if (hit) return [{path: key.path, value: v(hit.cell)}]
          const other = s.reads.other(e.map, key.value)
          return (other.assume.length ? other.assume : [[]]).map(a => ({path: [...key.path, ...a], value: v(other.cell)}))
        }
        const at = focus.map(f => ({path: [...key.path, ...eq(key.value, f.key)], value: v(f.cell)}))
        const other = s.reads.other(e.map, key.value)
        const assumes = other.assume.length ? other.assume : [[]]
        const elsewhere = apartFrom(key.value, focus.map(f => f.key)).flatMap(apart => assumes.map(a => ({path: [...key.path, ...apart, ...a], value: v(other.cell)})))
        return [...at, ...elsewhere]
      })
  }
}
// The cases in which c has the given truth value.
function symC(c: C, s: Sym, truth: boolean): Cases<null> {
  switch (c.op) {
    case 'all': throw new Error('the symbolic prover takes no quantified flag (the kernel does)')
    case '<': case '<=': case '=':
      return cross(symE(c.a, s), a => symE(c.b, s).flatMap(b => {
        const [p, q] = [a, b.value]
        const holds = c.op === '<' ? (truth ? [lt(p, q)] : [le(q, p)])
          : c.op === '<=' ? (truth ? [le(p, q)] : [lt(q, p)])
          : truth ? [eq(p, q)] : [lt(p, q), lt(q, p)]
        return holds.map(constraints => ({path: [...b.path, ...constraints], value: null}))
      }))
    case 'not': return symC(c.x, s, !truth)
    case 'flag': {
      if (s.flags === undefined || !(c.name in s.flags)) throw new Error(`the flag ${c.name} is read outside its step`)
      return s.flags[c.name] === truth ? [{path: [], value: null}] : []
    }
    case 'and': case 'or': {
      if ((c.op === 'and') === truth) return c.xs.reduce<Cases<null>>((acc, y) => cross(acc, () => symC(y, s, truth)), [{path: [], value: null}])
      return c.xs.flatMap(y => symC(y, s, truth))
    }
  }
}


// PROVE_DEBUG=1 logs the case counts to stderr; read through globalThis so the module also loads where there is no process.
const proveDebug = !!env.PROVE_DEBUG
const debug = (label: string, n: number) => { if (proveDebug) console.error(`[prove] ${label}: ${n} (${Math.round(performance.now())} ms)`) }
// Drops the cases whose path is already impossible, so impossible branches don't multiply.
function feasible<T>(cases: Cases<T>): Cases<T> {
  return cases.filter(c => {
    const names = [...new Set(c.path.flatMap(x => Object.keys(x.lin).filter(key => key !== '1')))]
    return solve([...nat(...names), ...c.path]).kind !== 'refuted'
  })
}

// --- proofs ----------------------------------------------------------------------------------------------------------

export type Obligation = {phase: 'start' | 'step', law: string, constraints: Constraint[], verdict: Verdict}
export type Proof = {law: Law, proven: boolean, obligations: Obligation[]}

// The map reads a condition makes, as (map, key expression).
function readsOf(c: C): {map: string, key: E}[] {
  const inE = (e: E): {map: string, key: E}[] => e.op === 'get' ? [{map: e.map, key: e.key}, ...inE(e.key)]
    : e.op === 'if' ? [...readsOfC(e.c), ...inE(e.then), ...inE(e.else)] : 'a' in e ? [...inE(e.a), ...('b' in e ? inE(e.b) : [])] : []
  const readsOfC = (y: C): {map: string, key: E}[] => y.op === 'flag' || y.op === 'all' ? [] : y.op === 'not' ? readsOfC(y.x) : y.op === 'and' || y.op === 'or' ? y.xs.flatMap(readsOfC) : [...inE(y.a), ...inE(y.b)]
  return readsOfC(c)
}
const keyLin = (e: E, names: Record<string, Lin>): Lin => symE(e, {names, reads: noReads})[0]!.value
const cellName = (map: string, key: Lin, when: string) => `${map}[${show(key)}]${when}`

// Proves `goal` by induction, assuming `invariants` (which include goal) hold before the step. A law with `forall`
// holds at every key; it is proven at a fresh key, and assumed at every key the step reads.
export function prove(m: Machine, goal: Law, invariants: Law[] = [goal]): Proof {
  const obligations: Obligation[] = []
  const naturals = [...m.params, ...m.inputs, ...Object.keys(m.state)]
  const preCases = m.pre ? symC(m.pre, {names: {}, reads: noReads}, true) : [{path: [], value: null}]
  const stepAssume = m.pre && m.assume ? all(m.pre, m.assume) : m.pre ?? m.assume
  const assumeCases = stepAssume ? symC(stepAssume, {names: {}, reads: noReads}, true) : [{path: [], value: null}]
  const goalNames: Record<string, Lin> = goal.forall ? {[goal.forall]: v(`${goal.forall}*`)} : {}
  const forallLaws = invariants.filter(law => law.forall !== undefined)
  const scalarLaws = invariants.filter(law => law.forall === undefined)

  // At the start: every scalar and every map cell is its initial value.
  const startNames: Record<string, Lin> = {...goalNames}
  const startPath: Constraint[] = []
  for (const [name, e] of Object.entries(m.state)) {
    const [only] = symE(e, {names: {}, reads: noReads})
    startPath.push(...only!.path, ...eq(v(`${name}@0`), only!.value))
    startNames[name] = v(`${name}@0`)
  }
  const startReads: Reads = {focus: [], other: map => ({cell: `${map}@0`, assume: []})}
  for (const map of Object.keys(m.maps ?? {})) startPath.push(...eq(v(`${map}@0`), k(m.maps![map]!)))
  for (const a of preCases) for (const g of symC(goal.holds, {names: startNames, reads: startReads}, false)) {
    const constraints = [...nat(...m.params, ...Object.values(goalNames).flatMap(l => Object.keys(l))), ...a.path, ...startPath, ...g.path]
    obligations.push({phase: 'start', law: goal.name, constraints, verdict: solve(constraints)})
  }

  // The focus cells: every map read of the goal and of the scalar invariants, before and after the step.
  const focusReads = [...readsOf(goal.holds).map(r => ({...r, names: goalNames})), ...scalarLaws.flatMap(l => readsOf(l.holds).map(r => ({...r, names: {}})))]
  const focus: Focus[] = []
  for (const r of focusReads) {
    const key = keyLin(r.key, r.names)
    if (!focus.some(f => f.map === r.map && show(f.key) === show(key))) focus.push({map: r.map, key, cell: cellName(r.map, key, '')})
  }
  // The laws that hold at every key, at one key: the cells there are resolved by `cellAt`.
  const lawsAt = (key: Lin, cellAt: (map: string) => string): Constraint[][] => forallLaws.reduce<Constraint[][]>((acc, law) => {
    const cases = symC(law.holds, {names: {[law.forall!]: key}, reads: {focus: [], other: map => ({cell: cellAt(map), assume: []})}}, true)
    return acc.flatMap(p => cases.map(c => [...p, ...c.path]))
  }, [[]])
  const otherCell = (map: string, key: Lin) => cellName(map, key, '')
  const preReads: Reads = {focus, other: (map, key) => ({cell: otherCell(map, key), assume: lawsAt(key, mp => otherCell(mp, key))})}
  const preSym: Sym = {names: {...goalNames}, reads: preReads}

  // Assumptions before the step: the scalar invariants, the every-key laws at each focus key, and focus cells of one
  // map at equal keys being equal.
  let assumptions: Cases<null> = [{path: [], value: null}]
  for (const law of scalarLaws) assumptions = feasible(cross(assumptions, () => symC(law.holds, preSym, true)))
  for (const f of focus) {
    const cases = lawsAt(f.key, mp => focus.find(g => g.map === mp && show(g.key) === show(f.key))?.cell ?? otherCell(mp, f.key))
    assumptions = feasible(cross(assumptions, () => cases.map(path => ({path, value: null}))))
  }
  for (const [i, f] of focus.entries()) for (const g of focus.slice(i + 1).filter(g => g.map === f.map)) {
    assumptions = feasible(cross(assumptions, () => [
      {path: [...eq(f.key, g.key), ...eq(v(f.cell), v(g.cell))], value: null},
      ...apartFrom(f.key, [g.key]).map(path => ({path, value: null})),
    ]))
  }

  // The step: each new scalar, and each focus cell after the step's write to its map.
  debug('assume cases', assumeCases.length)
  debug('assumptions', assumptions.length)
  // Keys first: how each key the step reads or writes compares with each focus key of the same map, decided once.
  const stepReads = [
    ...Object.values(m.step.flags ?? {}).flatMap(readsOf),
    ...Object.values(m.step.state ?? {}).flatMap(e => readsOf({op: '=', a: e, b: e})),
    ...Object.entries(m.step.maps ?? {}).flatMap(([map, w]) => [...('each' in w ? [] : [{map, key: w.key}]), ...readsOf({op: '=', a: w.value, b: w.value})]),
  ]
  const pairs = new Map<string, {key: Lin, fkey: Lin}>()
  for (const r of stepReads) {
    const key = keyLin(r.key, {})
    for (const f of focus.filter(f => f.map === r.map)) pairs.set(`${show(key)}|${show(f.key)}`, {key, fkey: f.key})
  }
  // The request's assumptions and the invariants start every case, so contradictory choices are pruned early.
  let decisions: Cases<Record<string, 'eq' | 'apart'>> = feasible(cross(assumeCases, () => assumptions)).map(c => ({path: c.path, value: {}}))
  for (const [id, {key, fkey}] of pairs) {
    decisions = feasible(cross(decisions, acc => show(key) === show(fkey) ? [{path: [], value: {...acc, [id]: 'eq' as const}}] : [
      {path: eq(key, fkey), value: {...acc, [id]: 'eq' as const}},
      {path: lt(key, fkey), value: {...acc, [id]: 'apart' as const}},
      {path: lt(fkey, key), value: {...acc, [id]: 'apart' as const}},
    ]))
  }
  debug('key decisions', decisions.length)
  // Flags next: each named condition true or false, once, then the rest of the step under that choice.
  let flagCases: Cases<{decided: Record<string, 'eq' | 'apart'>, flags: Record<string, boolean>}> = decisions.map(d => ({path: d.path, value: {decided: d.value, flags: {}}}))
  for (const [name, c] of Object.entries(m.step.flags ?? {})) {
    flagCases = feasible(cross(flagCases, acc => [true, false].flatMap(truth => symC(c, {...preSym, decided: acc.decided, flags: acc.flags}, truth).map(r => ({path: r.path, value: {decided: acc.decided, flags: {...acc.flags, [name]: truth}}})))))
  }
  debug('flag cases', flagCases.length)
  const stepCases: Cases<Record<string, Lin>> = []
  for (const fc of flagCases) {
    const preSymF: Sym = {...preSym, flags: fc.value.flags, decided: fc.value.decided}
    let cases: Cases<Record<string, Lin>> = [{path: fc.path, value: {}}]
    for (const [name, e] of Object.entries(m.step.state ?? {})) cases = feasible(cross(cases, acc => symE(e, preSymF).map(r => ({path: r.path, value: {...acc, [name]: r.value}}))))
    for (const f of focus) {
      const write = m.step.maps?.[f.map]
      cases = feasible(cross(cases, acc => {
        if (write === undefined) return [{path: [], value: {...acc, [`${f.cell}'`]: v(f.cell)}}]
        if ('each' in write) throw new Error('the symbolic prover takes no write at every key (the kernel does)')
        return cross(symE(write.key, preSymF), key => {
          const decided = preSymF.decided?.[`${show(key)}|${show(f.key)}`]
          const written = () => symE(write.value, preSymF).map(val => ({path: [...val.path, ...(decided ? [] : eq(key, f.key))], value: {...acc, [`${f.cell}'`]: val.value}}))
          const kept = (paths: Constraint[][]) => paths.map(apart => ({path: apart, value: {...acc, [`${f.cell}'`]: v(f.cell)}}))
          return decided === 'eq' ? written() : decided === 'apart' ? kept([[]]) : [...written(), ...kept(apartFrom(key, [f.key]))]
        })
      }))
    }
    stepCases.push(...cases)
  }

  debug('step cases', stepCases.length)
  for (const st of stepCases) {
    const postNames: Record<string, Lin> = {...goalNames, ...Object.fromEntries(Object.keys(m.state).map(name => [name, st.value[name] ?? v(name)]))}
    const postFocus = focus.map(f => ({...f, cell: `${f.cell}'`}))
    const negated = symC(goal.holds, {names: postNames, reads: {focus: postFocus, other: noReads.other}}, false)
    for (const g of negated) {
      // The goal reads the focus cells after the step; replace each by its value.
      const path = g.path.map(c => ({...c, lin: postFocus.reduce((lin, f) => renameKey(lin, f.cell, st.value[f.cell]), c.lin)}))
      const all = [...st.path, ...path]
      const vars = [...new Set(all.flatMap(c => Object.keys(c.lin).filter(key => key !== '1')))]
      const constraints = [...nat(...new Set([...naturals, ...vars])), ...all]
      obligations.push({phase: 'step', law: goal.name, constraints, verdict: solve(constraints)})
    }
  }
  return {law: goal, proven: obligations.every(o => o.verdict.kind === 'refuted'), obligations}
}

const noReads: Reads = {focus: [], other: map => ({cell: `${map}[?]`, assume: []})}
function renameKey(lin: Lin, from: string, to: Lin | undefined): Lin {
  if (!(from in lin) || to === undefined) return lin
  const {[from]: c, ...rest} = lin
  return add(rest, scale(to, c!))
}

// --- real counterexamples ----------------------------------------------------------------------------------------------

// Every sequence of up to `depth` requests, with params and inputs within 0..bound, from the start: the first that breaks
// the law, checked with the interpreter. A variable `pre` or `assume` bounds by a constant of at most 15 (a choice, a
// yes/no, a small upTo) takes every value it may instead. A law that fails here is false; one that only fails `prove` may
// just need a stronger invariant.
export function search(m: Machine, law: Law, depth = 3, bound = 2): {params: Env, trace: Env[]} | undefined {
  const run = interpret(m)
  const holds = (params: Env, st: State) => {
    const keys = law.forall ? [...new Set([0, ...Object.values(st.maps).flatMap(cells => [...cells.keys()])])] : [0]
    return keys.every(key => evalC(law.holds, {...params, ...(law.forall ? {[law.forall]: key} : {})}, st, m))
  }
  const tops = new Map<string, number>()
  const conj = (c: C | undefined): C[] => (c === undefined ? [] : c.op === 'and' ? c.xs.flatMap(conj) : [c])
  for (const c of [...conj(m.pre), ...conj(m.assume)]) if ((c.op === '<' || c.op === '<=') && c.a.op === 'var' && c.b.op === 'const') {
    const top = c.op === '<' ? c.b.value - 1 : c.b.value
    if (top >= 0 && top <= 15) tops.set(c.a.name, Math.min(top, tops.get(c.a.name) ?? top))
  }
  const tuples = (names: string[]): Env[] => names.reduce<Env[]>((acc, name) => acc.flatMap(t => Array.from({length: (tops.get(name) ?? bound) + 1}, (_, i) => ({...t, [name]: i}))), [{}])
  const assumed = (env: Env, st: State) => m.assume === undefined || evalC(m.assume, env, st, m)
  const meetsPre = (params: Env) => m.pre === undefined || evalC(m.pre, params, {scalars: {}, maps: {}}, m)
  for (const params of tuples(m.params)) {
    const go = (st: State, trace: Env[]): Env[] | undefined => {
      if (!holds(params, st)) return trace
      if (trace.length === depth) return undefined
      for (const input of tuples(m.inputs)) {
        if (!assumed({...params, ...input}, st)) continue
        const found = go(run.step(params, st, input), [...trace, input])
        if (found) return found
      }
      return undefined
    }
    void go
  }
  // Shortest first: every depth for every params before the next depth.
  for (let limit = 0; limit <= depth; limit++) for (const params of tuples(m.params).filter(meetsPre)) {
    const go = (st: State, trace: Env[]): Env[] | undefined => {
      if (!holds(params, st)) return trace
      if (trace.length === limit) return undefined
      for (const input of tuples(m.inputs)) {
        if (!assumed({...params, ...input}, st)) continue
        const found = go(run.step(params, st, input), [...trace, input])
        if (found) return found
      }
      return undefined
    }
    const trace = go(run.init(params), [])
    if (trace) return {params, trace}
  }
  return undefined
}

// The cases of linear constraints in which a condition over plain variables has the given truth value.
export function conditionCases(c: C, truth: boolean): Constraint[][] {
  return symC(c, {names: {}, reads: noReads}, truth).map(cs => cs.path)
}
