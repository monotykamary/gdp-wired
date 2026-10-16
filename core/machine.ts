// Step machines: the one source for a stateful rule (a budget, caps, a ledger). From a Machine the library derives
//   - interpret / compileJs: the runtime, as an interpreter and as generated JavaScript
//   - prove: each law by induction (holds at the start, one step preserves it), with every case decided by solver.ts
//   - search: real counterexample traces from the start, by bounded enumeration of short request sequences
//   - strengthen (invariant.ts): candidate invariants dropped until the rest are inductive (Houdini)
// Arithmetic is linear: +, −, × by a constant, min, max, if. Maps are naturals indexed by naturals, every cell starting
// at the same value; a law about a map holds for every key x, and is proven at one arbitrary x (with the law assumed at
// every other key the step reads).
import {historyMachine, scope} from '../kernel/kernel.ts'
import {type Constraint, type Lin, type Verdict, add, eq, k, le, lt, nat, scale, show, solve, sub, v} from './solver.ts'

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

export type Machine = {
  name: string
  params: string[]
  inputs: string[]
  state: Record<string, E> // initial values, over params
  maps?: Record<string, number> // initial value of every cell
  step: {flags?: Record<string, C>, state?: Record<string, E>, maps?: Record<string, {key: E, value: E}>}
  pre?: C // about the params alone: a precondition, holding at the start and at every step
  assume?: C // about each request (inputs, and params), e.g. a flag is 0 or 1; holds at a step, not at the start
  history?: History
}
// The events kept so far, each a record of some of its inputs (read as r.<input>). A sum is a state variable worth the
// sum over the history of a term of the record and the params (a count, a total); a query is an input worth the sum over
// the history of a term of the record, the params and the request's other inputs (what code reads from a log at the
// request's own time). A relation, `when` (params and the request's other inputs) implies a <= b (homogeneous, over sums
// and queries), may be assumed at every step once it holds for each single record: both sides are sums over one list.
// With `prune`, the runtimes drop a record once its `order` (a recorded input) plus `after` (a term over the params) is at
// most the request's: the kernel proves such a record adds nothing to any query, and the runtimes refuse a request whose
// order goes back.
export type History = {keep: C, record: string[], sums: Record<string, E>, queries: Record<string, E>, relations?: {when: C, holds: C}[], prune?: {order: string, after: E}}
// A law: a condition on the state and params, and for a map law, `forall` names the key variable it holds at.
export type Law = {name: string, holds: C, forall?: string}

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

// --- the runtime ---------------------------------------------------------------------------------------------------

// Both runtimes compute over the naturals the proofs are about only while values stay JavaScript's exact integers: every
// param and input must be a natural below 2^53, and a sum or product past 2^53 - 1 throws rather than rounds. A machine
// runs only once the kernel's scope check accepts it, and the runtimes read only the params and inputs it declares, so a
// misspelled name, a missing input or a stray one fails loudly instead of running as undefined.
//
// A machine with a history runs as kernel.ts's plain machine (its sums as state) beside the records it keeps: each
// query is computed from the records at the request's own time. With `prune`, a request whose order goes back is
// refused and the records the kernel proved spent are dropped.

// history and last only with a history (last only when it is pruned).
export type State = {scalars: Record<string, number>, maps: Record<string, Map<number, number>>, history?: Env[], last?: number}
type Env = Record<string, number>
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
    case 'get': return st.maps[e.map]!.get(evalE(e.key, env, st, m)) ?? m.maps![e.map]!
  }
}
export function evalC(c: C, env: Env, st: State, m: Machine): boolean {
  switch (c.op) {
    case '<': return evalE(c.a, env, st, m) < evalE(c.b, env, st, m)
    case '<=': return evalE(c.a, env, st, m) <= evalE(c.b, env, st, m)
    case '=': return evalE(c.a, env, st, m) === evalE(c.b, env, st, m)
    case 'and': return c.xs.every(y => evalC(y, env, st, m))
    case 'or': return c.xs.some(y => evalC(y, env, st, m))
    case 'not': return !evalC(c.x, env, st, m)
    case 'flag': return env[`?${c.name}`] === 1
  }
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

// The interpreter: persistent (a step leaves the state it was given as it was), so searches can branch from any state.
export function interpret(m: Machine) {
  const {h, plain, carried} = runnable(m)
  const args = (params: Env, input?: Env): Env => {
    const env: Env = {}
    for (const p of m.params) env[p] = naturalIn(params[p], `param ${p}`)
    if (input) for (const i of carried) env[i] = naturalIn(input[i], `input ${i}`)
    return env
  }
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
    queries: (params: Env, st: State, input: Env): Env => {
      if (!h) return {}
      const env = args(params, input)
      ordered(env, st)
      return queriesOf(env, live(env, st))
    },
    step: (params: Env, st: State, input: Env): State => {
      const env = args(params, input)
      let records: Env[] = []
      if (h) { ordered(env, st); records = live(env, st); Object.assign(env, queriesOf(env, records)) }
      for (const [name, c] of Object.entries(plain.step.flags ?? {})) env[`?${name}`] = evalC(c, env, st, plain) ? 1 : 0
      const scalars = {...st.scalars}
      for (const [name, e] of Object.entries(plain.step.state ?? {})) scalars[name] = evalE(e, env, st, plain)
      const writes = Object.entries(plain.step.maps ?? {}).map(([name, {key, value}]) => [name, evalE(key, env, st, plain), evalE(value, env, st, plain)] as const)
      const maps = Object.fromEntries(Object.entries(st.maps).map(([name, cells]) => [name, new Map(cells)]))
      for (const [name, key, value] of writes) maps[name]!.set(key, value)
      if (!h) return {scalars, maps}
      const kept = evalC(h.keep, env, st, plain)
      return {scalars, maps, history: kept ? [...records, Object.fromEntries(h.record.map(f => [f, env[f]!]))] : records, ...(h.prune ? {last: env[h.prune.order]} : {})}
    },
  }
}

// The same machine as JavaScript source: what an app ships. A step reads the state it was given (every query, flag,
// scalar, key and value first), then writes the maps and the records in place, so it costs the same however large they
// grow; the state passed in is consumed. fork copies a state to branch from.
export function compileJs(m: Machine): string {
  const {h, plain, queries, carried} = runnable(m)
  const id = (name: string) => JSON.stringify(name)
  const flags = Object.keys(plain.step.flags ?? {})
  const ex = (e: E): string => {
    switch (e.op) {
      case 'var': return e.name.startsWith('r.') ? `r[${id(e.name.slice(2))}]` : plain.params.includes(e.name) || plain.inputs.includes(e.name) ? `env[${id(e.name)}]` : `s[${id(e.name)}]`
      case 'const': return String(e.value)
      case 'add': return `$x(${ex(e.a)} + ${ex(e.b)})`
      case 'sub': return `Math.max(0, ${ex(e.a)} - ${ex(e.b)})`
      case 'mul': return `$x(${e.k} * ${ex(e.a)})`
      case 'prod': return `$x(${ex(e.a)} * ${ex(e.b)})`
      case 'min': return `Math.min(${ex(e.a)}, ${ex(e.b)})`
      case 'max': return `Math.max(${ex(e.a)}, ${ex(e.b)})`
      case 'if': return `(${cx(e.c)} ? ${ex(e.then)} : ${ex(e.else)})`
      case 'get': return `(maps[${id(e.map)}].get(${ex(e.key)}) ?? ${plain.maps![e.map]})`
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
    }
  }
  const writes = Object.entries(plain.step.maps ?? {})
  const env = (input: boolean) => `{${[...m.params.map(p => `${id(p)}: $n(params[${id(p)}], ${id(`param ${p}`)})`), ...(input ? carried.map(i => `${id(i)}: $n(input[${id(i)}], ${id(`input ${i}`)})`) : [])].join(', ')}}`
  const lines = [`const env = ${env(true)}, s = state.scalars, maps = state.maps;`]
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
    `const scalars = {...s, ${Object.entries(plain.step.state ?? {}).map(([name, e]) => `${id(name)}: ${ex(e)}`).join(', ')}};`,
    ...writes.map(([, {key, value}], i) => `const key${i} = ${ex(key)}, value${i} = ${ex(value)};`))
  if (h) lines.push(`const keep = ${cx(h.keep)};`)
  lines.push(...writes.map(([name], i) => `maps[${id(name)}].set(key${i}, value${i});`))
  if (h) lines.push(`if (keep) records.push({${h.record.map(f => `${id(f)}: env[${id(f)}]`).join(', ')}});`,
    // Drop the spent prefix now and then, not every step: amortized, each record is moved a bounded number of times.
    'if (head > 1024 && 2 * head > records.length) { records.splice(0, head); head = 0; }',
    `return {scalars, maps, history: records, head${h.prune ? ', last: order' : ''}};`)
  else lines.push('return {scalars, maps};')
  return `// Generated from the machine ${m.name}. step consumes its state: keep the one it returns (fork to branch).
function $n(v, what) { if (typeof v !== 'number' || !Number.isSafeInteger(v) || v < 0) throw new RangeError(what + ' must be a natural below 2^53, not ' + v); return v; }
function $x(v) { if (v > 9007199254740991) throw new RangeError('a value passed 2^53 - 1, past which the proofs over the naturals no longer describe the run'); return v; }
export function init(params) {
  const env = ${env(false)}, s = {};
  return {scalars: {${Object.entries(plain.state).map(([name, e]) => `${id(name)}: ${ex(e)}`).join(', ')}}, maps: {${Object.keys(plain.maps ?? {}).map(name => `${id(name)}: new Map()`).join(', ')}}${h ? ', history: [], head: 0' : ''}};
}
export function fork(state) {
  return {scalars: {...state.scalars}, maps: Object.fromEntries(Object.entries(state.maps).map(([name, cells]) => [name, new Map(cells)]))${h ? ', history: state.history.slice(state.head), head: 0, last: state.last' : ''}};
}
export function step(params, state, input) {
  ${lines.join('\n  ')}
}
`
}

// Generated code as a function. Every caller passes source this library generated from its own terms, never from data,
// which is what makes compiling it safe; the lint's implied-eval rule is waived here and nowhere else.
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


const debug = (label: string, n: number) => { if (process.env.PROVE_DEBUG) require("node:fs").appendFileSync(process.env.PROVE_DEBUG, `[prove] ${label}: ${n} (${Math.round(performance.now())} ms)\n`) }
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
  const readsOfC = (y: C): {map: string, key: E}[] => y.op === 'flag' ? [] : y.op === 'not' ? readsOfC(y.x) : y.op === 'and' || y.op === 'or' ? y.xs.flatMap(readsOfC) : [...inE(y.a), ...inE(y.b)]
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
    ...Object.entries(m.step.maps ?? {}).flatMap(([map, w]) => [{map, key: w.key}, ...readsOf({op: '=', a: w.value, b: w.value})]),
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
// the law, checked with the interpreter. A law that fails here is false; one that only fails `prove` may just need a
// stronger invariant.
export function search(m: Machine, law: Law, depth = 3, bound = 2): {params: Env, trace: Env[]} | undefined {
  const run = interpret(m)
  const holds = (params: Env, st: State) => {
    const keys = law.forall ? [...new Set([0, ...Object.values(st.maps).flatMap(cells => [...cells.keys()])])] : [0]
    return keys.every(key => evalC(law.holds, {...params, ...(law.forall ? {[law.forall]: key} : {})}, st, m))
  }
  const tuples = (names: string[]): Env[] => names.reduce<Env[]>((acc, name) => acc.flatMap(t => Array.from({length: bound + 1}, (_, i) => ({...t, [name]: i}))), [{}])
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
