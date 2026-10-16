// Step machines: the one source for a stateful rule (a budget, caps, a ledger). From a Machine the library derives
//   - interpret / compileJs: the runtime, as an interpreter and as generated JavaScript
//   - prove: each law by induction (holds at the start, one step preserves it), with every case decided by solver.ts
//   - search: real counterexample traces from the start, by bounded enumeration of short request sequences
//   - strengthen (invariant.ts): candidate invariants dropped until the rest are inductive (Houdini)
// Arithmetic is linear: +, −, × by a constant, min, max, if. Maps are naturals indexed by naturals, every cell starting
// at the same value; a law about a map holds for every key x, and is proven at one arbitrary x (with the law assumed at
// every other key the step reads).
import {type Constraint, type Lin, type Verdict, add, eq, k, le, lt, nat, negate, scale, solve, sub, v} from './solver.ts'

export type E =
  | {op: 'var', name: string}
  | {op: 'const', value: number}
  | {op: 'add' | 'sub' | 'min' | 'max', a: E, b: E}
  | {op: 'mul', k: number, a: E}
  | {op: 'if', c: C, then: E, else: E}
  | {op: 'get', map: string, key: E}
export type C =
  | {op: '<' | '<=' | '=', a: E, b: E}
  | {op: 'and' | 'or', xs: C[]}
  | {op: 'not', x: C}

export type Machine = {
  name: string
  params: string[]
  inputs: string[]
  state: Record<string, E> // initial values, over params
  maps?: Record<string, number> // initial value of every cell
  step: {state?: Record<string, E>, maps?: Record<string, {key: E, value: E}>}
  assume?: C // about params and inputs, e.g. a flag is 0 or 1
}
// A law: a condition on the state and params, and for a map law, `forall` names the key variable it holds at.
export type Law = {name: string, holds: C, forall?: string}

// Builders.
export const x = (name: string): E => ({op: 'var', name})
export const n = (value: number): E => ({op: 'const', value})
export const plus = (a: E, b: E): E => ({op: 'add', a, b})
export const minus = (a: E, b: E): E => ({op: 'sub', a, b})
export const times = (factor: number, a: E): E => ({op: 'mul', k: factor, a})
export const min = (a: E, b: E): E => ({op: 'min', a, b})
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

export type State = {scalars: Record<string, number>, maps: Record<string, Map<number, number>>}
type Env = Record<string, number>

export function evalE(e: E, env: Env, st: State, m: Machine): number {
  switch (e.op) {
    case 'var': return env[e.name] ?? st.scalars[e.name]!
    case 'const': return e.value
    case 'add': return evalE(e.a, env, st, m) + evalE(e.b, env, st, m)
    case 'sub': return Math.max(0, evalE(e.a, env, st, m) - evalE(e.b, env, st, m))
    case 'mul': return e.k * evalE(e.a, env, st, m)
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
  }
}
export function interpret(m: Machine) {
  return {
    init: (params: Env): State => ({
      scalars: Object.fromEntries(Object.entries(m.state).map(([name, e]) => [name, evalE(e, params, {scalars: {}, maps: {}}, m)])),
      maps: Object.fromEntries(Object.keys(m.maps ?? {}).map(name => [name, new Map()])),
    }),
    step: (params: Env, st: State, input: Env): State => {
      const env = {...params, ...input}
      const scalars = {...st.scalars}
      for (const [name, e] of Object.entries(m.step.state ?? {})) scalars[name] = evalE(e, env, st, m)
      const maps = Object.fromEntries(Object.entries(st.maps).map(([name, cells]) => [name, new Map(cells)]))
      for (const [name, {key, value}] of Object.entries(m.step.maps ?? {})) maps[name]!.set(evalE(key, env, st, m), evalE(value, env, st, m))
      return {scalars, maps}
    },
  }
}

// The same machine as JavaScript source: what an app ships.
export function compileJs(m: Machine): string {
  const ex = (e: E): string => {
    switch (e.op) {
      case 'var': return m.params.includes(e.name) || m.inputs.includes(e.name) ? `env.${e.name}` : `s.${e.name}`
      case 'const': return String(e.value)
      case 'add': return `(${ex(e.a)} + ${ex(e.b)})`
      case 'sub': return `Math.max(0, ${ex(e.a)} - ${ex(e.b)})`
      case 'mul': return `(${e.k} * ${ex(e.a)})`
      case 'min': return `Math.min(${ex(e.a)}, ${ex(e.b)})`
      case 'max': return `Math.max(${ex(e.a)}, ${ex(e.b)})`
      case 'if': return `(${cx(e.c)} ? ${ex(e.then)} : ${ex(e.else)})`
      case 'get': return `(maps.${e.map}.get(${ex(e.key)}) ?? ${m.maps![e.map]})`
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
    }
  }
  const scalars = Object.entries(m.step.state ?? {}).map(([name, e]) => `${name}: ${ex(e)}`).join(', ')
  const writes = Object.entries(m.step.maps ?? {}).map(([name, {key, value}]) => `next.${name}.set(${ex(key)}, ${ex(value)});`).join('\n    ')
  return `// Generated from the machine ${m.name}.
export function init(env) {
  const s = {};
  return {scalars: {${Object.entries(m.state).map(([name, e]) => `${name}: ${ex(e)}`).join(', ')}}, maps: {${Object.keys(m.maps ?? {}).map(name => `${name}: new Map()`).join(', ')}}};
}
export function step(params, state, input) {
  const env = {...params, ...input}, s = state.scalars, maps = state.maps;
  const next = {${Object.keys(m.maps ?? {}).map(name => `${name}: new Map(maps.${name})`).join(', ')}};
  ${writes}
  return {scalars: {...s, ${scalars}}, maps: next};
}
`
}

// --- symbolic: from expressions to cases of linear constraints -------------------------------------------------------

type Cases<T> = {path: Constraint[], value: T}[]
// How map reads resolve: in `prove`, a read at a key other than the focus key x is a fresh variable, about which the
// map's laws are assumed.
type Reads = {focus?: {map: string, key: Lin, cell: string}, fresh: (map: string, key: Lin) => {cell: string, assume: Constraint[][]}}
type Sym = {names: Record<string, Lin>, reads: Reads}

const cross = <A, B>(as: Cases<A>, f: (a: A) => Cases<B>): Cases<B> => as.flatMap(a => f(a.value).map(b => ({path: [...a.path, ...b.path], value: b.value})))

function symE(e: E, s: Sym): Cases<Lin> {
  switch (e.op) {
    case 'var': return [{path: [], value: s.names[e.name] ?? v(e.name)}]
    case 'const': return [{path: [], value: k(e.value)}]
    case 'add': return cross(symE(e.a, s), a => symE(e.b, s).map(b => ({path: b.path, value: add(a, b.value)})))
    case 'mul': return symE(e.a, s).map(a => ({path: a.path, value: scale(a.value, e.k)}))
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
      return [
        ...cross(symC(e.c, s, true), () => symE(e.then, s)),
        ...cross(symC(e.c, s, false), () => symE(e.else, s)),
      ]
    case 'get':
      return symE(e.key, s).flatMap(key => {
        const focus = s.reads.focus
        const other = s.reads.fresh(e.map, key.value)
        const elsewhere = other.assume.length === 0 ? [[] as Constraint[]] : other.assume
        if (focus === undefined || focus.map !== e.map) return elsewhere.map(assume => ({path: [...key.path, ...assume], value: v(other.cell)}))
        return [
          {path: [...key.path, ...eq(key.value, focus.key)], value: v(focus.cell)},
          ...[lt(key.value, focus.key), lt(focus.key, key.value)].flatMap(apart => elsewhere.map(assume => ({path: [...key.path, ...apart, ...assume], value: v(other.cell)}))),
        ]
      })
  }
}
// The cases in which c has the given truth value.
function symC(c: C, s: Sym, truth: boolean): Cases<null> {
  switch (c.op) {
    case '<': case '<=': case '=': {
      return cross(symE(c.a, s), a => symE(c.b, s).flatMap(b => {
        const [p, q] = [a, b.value]
        const holds = c.op === '<' ? (truth ? [lt(p, q)] : [le(q, p)])
          : c.op === '<=' ? (truth ? [le(p, q)] : [lt(q, p)])
          : truth ? [eq(p, q)] : [lt(p, q), lt(q, p)]
        return holds.map(constraints => ({path: [...b.path, ...constraints], value: null}))
      }))
    }
    case 'not': return symC(c.x, s, !truth)
    case 'and': case 'or': {
      const conjunctive = (c.op === 'and') === truth
      if (conjunctive) return c.xs.reduce<Cases<null>>((acc, y) => cross(acc, () => symC(y, s, truth)), [{path: [], value: null}])
      return c.xs.flatMap(y => symC(y, s, truth))
    }
  }
}

// --- proofs ----------------------------------------------------------------------------------------------------------

export type Obligation = {phase: 'start' | 'step', law: string, constraints: Constraint[], verdict: Verdict}
export type Proof = {law: Law, proven: boolean, obligations: Obligation[]}

const pre = (name: string) => name
const post = (name: string) => `${name}'`

// Proves `goal` by induction, assuming `invariants` (which include goal) hold before the step. Laws about maps hold at
// the focus key and are assumed at every other key the step reads.
export function prove(m: Machine, goal: Law, invariants: Law[] = [goal]): Proof {
  const obligations: Obligation[] = []
  const naturals = [...m.params, ...m.inputs, ...Object.keys(m.state)]
  const assumeCases = m.assume ? symC(m.assume, {names: {}, reads: noReads}, true) : [{path: [], value: null}]
  // At the start: every scalar is its initial value and every map cell its initial value.
  const startNames: Record<string, Lin> = {}
  const startPath: Constraint[] = []
  for (const [name, e] of Object.entries(m.state)) {
    const [only] = symE(e, {names: {}, reads: noReads})
    if (only === undefined) continue
    startPath.push(...only.path, ...eq(v(`${name}@0`), only.value))
    startNames[name] = v(`${name}@0`)
  }
  const keyVar = goal.forall ?? 'x'
  const startReads: Reads = {fresh: map => ({cell: `${map}@0`, assume: []}), focus: undefined}
  for (const map of Object.keys(m.maps ?? {})) startPath.push(...eq(v(`${map}@0`), k(m.maps![map]!)))
  for (const a of assumeCases) for (const g of symC(goal.holds, {names: startNames, reads: startReads}, false)) {
    const constraints = [...nat(...m.params, `${keyVar}`), ...a.path, ...startPath, ...g.path]
    obligations.push({phase: 'start', law: goal.name, constraints, verdict: solve(constraints)})
  }
  // One step from any state where the invariants hold.
  const mapLaws = invariants.filter(law => law.forall !== undefined)
  const scalarLaws = invariants.filter(law => law.forall === undefined)
  const focusMap = goal.forall === undefined ? undefined : findMap(goal.holds)
  const freshCount = {i: 0}
  const lawAt = (map: string, cell: string, keyLin: Lin): Constraint[][] => {
    // The map's laws, at another key: its cell is `cell`.
    const out: Constraint[][] = [[]]
    for (const law of mapLaws.filter(l => findMap(l.holds) === map)) {
      const cases = symC(law.holds, {names: {[law.forall!]: keyLin}, reads: {fresh: () => ({cell, assume: []})}}, true)
      out.splice(0, out.length, ...out.flatMap(o => cases.map(c => [...o, ...c.path])))
    }
    return out
  }
  const reads = (atPost: boolean): Reads => ({
    focus: focusMap === undefined ? undefined : {map: focusMap, key: v(keyVar), cell: atPost ? post(`${focusMap}[${keyVar}]`) : pre(`${focusMap}[${keyVar}]`)},
    fresh: (map, keyLin) => {
      const cell = `${map}[#${freshCount.i++}]`
      return {cell, assume: atPost ? [] : lawAt(map, cell, keyLin)}
    },
  })
  const preSym: Sym = {names: {}, reads: reads(false)}
  // Assumptions: scalar invariants, and the map laws at the focus key.
  let assumptions: Cases<null> = [{path: [], value: null}]
  for (const law of [...scalarLaws, ...mapLaws.filter(l => findMap(l.holds) === focusMap)]) {
    const names = law.forall === undefined ? {} : {[law.forall]: v(keyVar)}
    assumptions = cross(assumptions, () => symC(law.holds, {names, reads: preSym.reads}, true))
  }
  // The step: each new scalar, and the focus cell after the step's write.
  let stepCases: Cases<Record<string, Lin>> = [{path: [], value: {}}]
  for (const [name, e] of Object.entries(m.step.state ?? {})) {
    stepCases = cross(stepCases, acc => symE(e, preSym).map(r => ({path: r.path, value: {...acc, [name]: r.value}})))
  }
  if (focusMap !== undefined) {
    const write = m.step.maps?.[focusMap]
    stepCases = cross(stepCases, acc => {
      if (write === undefined) return [{path: [], value: {...acc, [post(`${focusMap}[${keyVar}]`)]: v(pre(`${focusMap}[${keyVar}]`))}}]
      return cross(symE(write.key, preSym), key => [
        ...symE(write.value, preSym).map(val => ({path: [...val.path, ...eq(key, v(keyVar))], value: {...acc, [post(`${focusMap}[${keyVar}]`)]: val.value}})),
        ...[lt(key, v(keyVar)), lt(v(keyVar), key)].map(apart => ({path: apart, value: {...acc, [post(`${focusMap}[${keyVar}]`)]: v(pre(`${focusMap}[${keyVar}]`))}})),
      ])
    })
  }
  for (const a of assumeCases) for (const inv of assumptions) for (const st of stepCases) {
    const postNames: Record<string, Lin> = {...Object.fromEntries(Object.keys(m.state).map(name => [name, st.value[name] ?? v(name)]))}
    const postReads: Reads = focusMap === undefined ? noReads : {focus: {map: focusMap, key: v(keyVar), cell: `__post`}, fresh: noReads.fresh}
    const negated = symC(goal.holds, {names: {...postNames, ...(goal.forall ? {[goal.forall]: v(keyVar)} : {})}, reads: postReads}, false)
    for (const g of negated) {
      const path = g.path.map(c => ({...c, lin: renameKey(c.lin, '__post', st.value[post(`${focusMap}[${keyVar}]`)])}))
      const cells = [...new Set([...a.path, ...inv.path, ...st.path, ...path].flatMap(c => Object.keys(c.lin).filter(key => key.includes('['))))]
      const constraints = [...nat(...naturals, keyVar, ...cells), ...a.path, ...inv.path, ...st.path, ...path]
      obligations.push({phase: 'step', law: goal.name, constraints, verdict: solve(constraints)})
    }
  }
  return {law: goal, proven: obligations.every(o => o.verdict.kind === 'refuted'), obligations}
}

const noReads: Reads = {fresh: map => ({cell: `${map}[?]`, assume: []})}
function renameKey(lin: Lin, from: string, to: Lin | undefined): Lin {
  if (!(from in lin) || to === undefined) return lin
  const {[from]: c, ...rest} = lin
  return add(rest, scale(to, c!))
}
function findMap(c: C): string | undefined {
  const inE = (e: E): string | undefined => e.op === 'get' ? e.map : 'a' in e ? (inE(e.a) ?? ('b' in e ? inE(e.b) : undefined)) : e.op === 'if' ? (inC(e.c) ?? inE(e.then) ?? inE(e.else)) : undefined
  const inC = (y: C): string | undefined => y.op === 'not' ? inC(y.x) : y.op === 'and' || y.op === 'or' ? y.xs.map(inC).find(Boolean) : inE(y.a) ?? inE(y.b)
  return inC(c)
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
  const assumed = (env: Env) => m.assume === undefined || evalC(m.assume, env, {scalars: {}, maps: {}}, m)
  for (const params of tuples(m.params)) {
    const go = (st: State, trace: Env[]): Env[] | undefined => {
      if (!holds(params, st)) return trace
      if (trace.length === depth) return undefined
      for (const input of tuples(m.inputs)) {
        if (!assumed({...params, ...input})) continue
        const found = go(run.step(params, st, input), [...trace, input])
        if (found) return found
      }
      return undefined
    }
    void go
  }
  // Shortest first: every depth for every params before the next depth.
  for (let limit = 0; limit <= depth; limit++) for (const params of tuples(m.params)) {
    const go = (st: State, trace: Env[]): Env[] | undefined => {
      if (!holds(params, st)) return trace
      if (trace.length === limit) return undefined
      for (const input of tuples(m.inputs)) {
        if (!assumed({...params, ...input})) continue
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
