// Runs that never end, found: the search behind `proveNeverEnds`. Untrusted, like prove.ts: what it finds is a closed
// recurrent set with its successor given (kernel.ts's Recur), checked by kernel.ts's checkRecur and, exported, by
// NonTerm.lean's never_ends_of.
//
// - Runs. Random runs of the loop: params small or near the constants its conditions compare with, each turn's inputs
//   small or a value the state holds. Each run keeps its turns' inputs, so any state it reached has a stem.
// - Lassos. A run back at a state it was in (the params and the state; the inputs are read afresh each turn): the set is
//   the cycle's states, each turn's inputs given at its state by an if over the states (`lassoRecur`).
// - Policies. From a state a run reached, a run whose inputs are terms over the state and params: in each mode (the
//   values of the state variables the loop compares with constants, its locations), the first allowed of a few
//   assignments, each input a term from a pool (0, 1, ±1, the constants it is compared with, each state and param value,
//   those ± 1); an assignment is added, drawn from the pools, where the run would stop. The policy is the set's witness.
//   A policy run that comes back is a lasso; one that goes on is the set's sample.
// - The set. Per mode, atoms over the integer values (a pair x, x$n or x$neg is the integer x − x$n; a natural is
//   itself): bounds of one value, of the sum and the difference of two, equalities, each true on the policy run. Those
//   constant along it go in first; then each counterexample the prover's model gives (a state of the set whose
//   witnessed turn fails or leaves the set) is excluded by one more atom false there, the steadiest and simplest first
//   (its slack along the run never shrinking), until the closure goal is proven: kernel/prove.ts's grow, which tries
//   kernel/cdcl.ts's CDCL on a linear goal first. Linear loops' geometric runs (a value doubling, two growing apart) are
//   among these sets: their bounds and differences grow along the run.
// - Accelerated cycles, between the runs and the policies (core/accel.ts): a set from a cycle of the loop's relation,
//   the cycle's n-fold run read in closed form (an atom's differences along it), and a stem from a reached state or a
//   run with its loops accelerated, checked as the rest are. A large closure goal (a program of many locations, whose
//   body reads every rule) is closed by the set's parts (`cases`): each part's goal at its location, the location
//   substituted and the constants folded, which leaves only that location's rules (kernel.ts's checkRecurCases).
import {type C, type E, n as K, same as eq, seeded, walkOnce, x as V} from './machine.ts'
import {type Loop, type Recur, type RecurCases, type Tree, caseGoals, checkRecur, checkRecurCases, coverGoal, loopMachine, recurGoal, substC, trueC} from '../kernel/kernel.ts'
import {clock, counted, grow, realModels} from '../kernel/prove.ts'
import {work} from './solver.ts'
import {accelerated, relationBuilt, stemsTo} from './accel.ts'
import {findBoundedRun} from './bmc.ts'

// `lassos`: only lassos of the random runs (no policy, no set fitted), the cheap case. `counted`: the budget read off the
// prover's counted clock (kernel/prove.ts's `counted`, that many units of work a millisecond; each turn simulated is one,
// as is each turn's condition weighed), not wall time, so the same loop and seed give the same verdict and certificate
// on any machine (core/conformance.ts's cases are made so).
// `accel`: the share of the time (after the random runs) for the accelerated cycles' sets (core/accel.ts; 0 none).
// `extend`: an accelerated set that a stem reaches (the likeliest candidate there is: its cycle keeps it, by the closed
// forms, and a run gets there) may take until this many ms from the start, past `ms`, for its closure.
// `cases`: an accelerated set with a large closure goal, at locations, may be closed by its cases (kernel.ts's
// checkRecurCases, NonTerm.lean's never_ends_of_cases): the verdict's `cases`, in place of `recur`.
export type NeverEndsOptions = {ms?: number, seed?: number, maxTurns?: number, lassos?: boolean, counted?: number, accel?: number, extend?: number, cases?: boolean}
// `lasso`: where the set is a lasso's, its turns' inputs (a stem from the start, then a cycle back to the state it began
// at), so a caller can replay it on its own semantics.
export type NeverEndsVerdict = {proven: boolean, checked: boolean, recur?: Recur, cases?: RecurCases, by?: 'lasso' | 'policy lasso' | 'recurrent set' | 'accelerated', why?: string,
  lasso?: {params: Record<string, number>, stem: Record<string, number>[], cycle: Record<string, number>[]},
  stats: {runs: number, turns: number, policies: number, rounds: number, ms: number, lassoTried: number, goalSize: number, accel: number, accelClosed: number}}

type Env = Record<string, number>
const T: C = trueC, F: C = {op: '<', a: K(0), b: K(0)}
export const isT = (c: C) => c.op === '<=' && c.a.op === 'const' && c.b.op === 'const' && c.a.value <= c.b.value
export const isF = (c: C) => (c.op === '<' && c.a.op === 'const' && c.b.op === 'const' && c.a.value >= c.b.value) || (c.op === '<=' && c.a.op === 'const' && c.b.op === 'const' && c.a.value > c.b.value)
const and = (xs: C[]): C => { const ys = xs.flatMap(x => (x.op === 'and' ? x.xs : [x])).filter(x => !isT(x)); return ys.some(isF) ? F : ys.length === 0 ? T : ys.length === 1 ? ys[0]! : {op: 'and', xs: ys} }
const or = (xs: C[]): C => { const ys = xs.flatMap(x => (x.op === 'or' ? x.xs : [x])).filter(x => !isF(x)); return ys.some(isT) ? T : ys.length === 0 ? F : ys.length === 1 ? ys[0]! : {op: 'or', xs: ys} }
const plus = (a: E, b: E): E => (a.op === 'const' && a.value === 0 ? b : b.op === 'const' && b.value === 0 ? a : a.op === 'const' && b.op === 'const' ? K(a.value + b.value) : {op: 'add', a, b})
const minus = (a: E, b: E): E => (b.op === 'const' && b.value === 0 ? a : a.op === 'const' && b.op === 'const' ? K(Math.max(0, a.value - b.value)) : {op: 'sub', a, b})
const times = (k: number, a: E): E => (k === 0 ? K(0) : k === 1 ? a : a.op === 'const' ? K(k * a.value) : {op: 'mul', k, a})
const ite = (c: C, a: E, b: E): E => (isT(c) ? a : isF(c) ? b : a === b || JSON.stringify(a) === JSON.stringify(b) ? a : {op: 'if', c, then: a, else: b})

// Constants folded: a term or condition with the same value everywhere, smaller (a policy's conditions read the mode as
// its constants, which decides most of a translated loop's cases; core/bmc.ts, a run's start and its fixed requests).
// Each shared part is folded once.
const simpMemo = new WeakMap<E | C, E | C>()
const memo = <T extends E | C>(x: T, f: (x: T) => T): T => { const hit = simpMemo.get(x); if (hit) return hit as T; const out = f(x); simpMemo.set(x, out); return out }
export const simpE = (e: E): E => memo(e, simpE0)
export const simpC = (c: C): C => memo(c, simpC0)
function simpE0(e: E): E {
  switch (e.op) {
    case 'var': case 'const': return e
    case 'add': return plus(simpE(e.a), simpE(e.b))
    case 'sub': return minus(simpE(e.a), simpE(e.b))
    case 'mul': return times(e.k, simpE(e.a))
    case 'prod': { const a = simpE(e.a), b = simpE(e.b); return a.op === 'const' ? times(a.value, b) : b.op === 'const' ? times(b.value, a) : {op: 'prod', a, b} }
    case 'min': case 'max': { const a = simpE(e.a), b = simpE(e.b); return a.op === 'const' && b.op === 'const' ? K(Math[e.op](a.value, b.value)) : {op: e.op, a, b} }
    case 'if': return ite(simpC(e.c), simpE(e.then), simpE(e.else))
    case 'get': return {op: 'get', map: e.map, key: simpE(e.key)}
  }
}
function simpC0(c: C): C {
  switch (c.op) {
    case '<=': case '<': case '=': {
      const a = simpE(c.a), b = simpE(c.b)
      if (a.op === 'const' && b.op === 'const') return (c.op === '<=' ? a.value <= b.value : c.op === '<' ? a.value < b.value : a.value === b.value) ? T : F
      return {op: c.op, a, b}
    }
    case 'and': return and(c.xs.map(simpC))
    case 'or': return or(c.xs.map(simpC))
    case 'not': { const x = simpC(c.x); return isT(x) ? F : isF(x) ? T : {op: 'not', x} }
    case 'flag': case 'all': return c
  }
}

// A goal's size as the kernel reads it: its terms written out (shared parts counted at each use). A closure goal past
// GOAL_MAX is not tried: the witness's ifs read inside the body's multiply, and the kernel would not finish within the
// budget (one task's goal was 163 million nodes).
const sizeMemo = new WeakMap<object, number>()
export function goalSize(x: unknown): number {
  if (typeof x !== 'object' || x === null) return 1
  const m = sizeMemo.get(x)
  if (m !== undefined) return m
  let n = 1
  for (const v of Object.values(x)) n += goalSize(v)
  sizeMemo.set(x, n)
  return n
}
const GOAL_MAX = 300_000
// An accelerated set's goal: the witness reads the location (and, where the cycle comes back to one, an atom that tells
// the parts there apart), so its ifs multiply the body's less; and the kernel reads a term shared in the goal once per
// case, so its size here is its distinct terms (TermComp's s1: 23 million nodes written out, 707,064 distinct, proven in
// 11 s; tqli: 720,729 written out, proven in 22 s).
export const dagSize = (x: unknown): number => { let n = 0; walkOnce(x, () => { n++ }); return n }
const ACCEL_DAG_MAX = 1_500_000
// (a goal past this many distinct terms is closed by cases, where `cases` asks for it: pgarch's sets, 537,164, each
// location's case under 300)
const CASES_FROM = 20_000

// --- running the loop ---------------------------------------------------------------------------------------------------

class Overflow extends Error {}
const BIG = 2 ** 48
const big = (x: number) => { if (x > BIG) throw new Overflow(); return x }
function cE(e: E): (env: Env) => number {
  switch (e.op) {
    case 'var': { const n = e.name; return env => env[n] ?? 0 }
    case 'const': { const v = e.value; return () => v }
    case 'add': { const a = cE(e.a), b = cE(e.b); return env => big(a(env) + b(env)) }
    case 'sub': { const a = cE(e.a), b = cE(e.b); return env => Math.max(0, a(env) - b(env)) }
    case 'mul': { const a = cE(e.a), k = e.k; return env => big(k * a(env)) }
    case 'prod': { const a = cE(e.a), b = cE(e.b); return env => big(a(env) * b(env)) }
    case 'min': { const a = cE(e.a), b = cE(e.b); return env => Math.min(a(env), b(env)) }
    case 'max': { const a = cE(e.a), b = cE(e.b); return env => Math.max(a(env), b(env)) }
    case 'if': { const c = cC(e.c), a = cE(e.then), b = cE(e.else); return env => (c(env) ? a(env) : b(env)) }
    case 'get': return () => 0
  }
}
function cC(c: C): (env: Env) => boolean {
  switch (c.op) {
    case '<=': { const a = cE(c.a), b = cE(c.b); return env => a(env) <= b(env) }
    case '<': { const a = cE(c.a), b = cE(c.b); return env => a(env) < b(env) }
    case '=': { const a = cE(c.a), b = cE(c.b); return env => a(env) === b(env) }
    case 'and': { const xs = c.xs.map(cC); return env => xs.every(x => x(env)) }
    case 'or': { const xs = c.xs.map(cC); return env => xs.some(x => x(env)) }
    case 'not': { const x = cC(c.x); return env => !x(env) }
    case 'flag': case 'all': throw new Error('a loop reads no flag')
  }
}

// An integer value of the loop: a pair (x, x$n or x$neg) or a natural (n empty).
type Obs = {name: string, p: string, n?: string}
function observables(names: string[]): Obs[] {
  const out: Obs[] = [], twin = new Set<string>()
  for (const x of names) for (const s of ['$n', '$neg']) if (names.includes(x + s)) twin.add(x + s)
  for (const x of names) if (!twin.has(x)) { const n = names.includes(`${x}$n`) ? `${x}$n` : names.includes(`${x}$neg`) ? `${x}$neg` : undefined; out.push({name: x, p: x, ...(n ? {n} : {})}) }
  return out
}
const valueOf = (o: Obs, env: Env) => (env[o.p] ?? 0) - (o.n ? env[o.n] ?? 0 : 0)
// An integer term over the observables as a pair of naturals (p, n), its value p − n.
type ITerm = {p: E, n: E}
const iObs = (o: Obs): ITerm => ({p: V(o.p), n: o.n ? V(o.n) : K(0)})
const iConst = (c: number): ITerm => (c >= 0 ? {p: K(c), n: K(0)} : {p: K(0), n: K(-c)})
const iAdd = (x: ITerm, c: number): ITerm => (c >= 0 ? {p: plus(x.p, K(c)), n: x.n} : {p: x.p, n: plus(x.n, K(-c))})
// The value written into a pair (normal: at most one part nonzero) or a natural (its value, 0 below).
const iInto = (x: ITerm, o: Obs): Record<string, E> => (o.n ? {[o.p]: minus(x.p, x.n), [o.n]: minus(x.n, x.p)} : {[o.p]: minus(x.p, x.n)})

// The constants a condition compares a name with (`t = 2`, `x + 1 <= 100`): where the loop's cases are.
function constantsOf(c: C | E, out = new Set<number>()): Set<number> {
  JSON.stringify(c, (k, v) => { if (k === 'value' && typeof v === 'number') out.add(v); return v })
  return out
}

// --- atoms: linear facts over the integer values ------------------------------------------------------------------------

// Σ c·x ≥ d (or = d) over observables, as a natural condition: positive parts against negative ones.
type Atom = {coefs: [number, number][], d: number, eq: boolean, score: number, arity: number}
function atomC(a: Atom, obs: Obs[]): C {
  let pos: E = K(0), neg: E = K(0)
  for (const [i, c] of a.coefs) {
    const o = obs[i]!, k = Math.abs(c)
    if (c > 0) { pos = plus(pos, times(k, V(o.p))); if (o.n) neg = plus(neg, times(k, V(o.n))) } else { neg = plus(neg, times(k, V(o.p))); if (o.n) pos = plus(pos, times(k, V(o.n))) }
  }
  const lhs = plus(neg, K(Math.max(a.d, 0))), rhs = plus(pos, K(Math.max(-a.d, 0)))
  return a.eq ? eq(lhs, rhs) : {op: '<=', a: lhs, b: rhs}
}
const atomValue = (a: Atom, vals: number[]) => a.coefs.reduce((s, [i, c]) => s + c * vals[i]!, 0)
const atomHolds = (a: Atom, vals: number[]) => (a.eq ? atomValue(a, vals) === a.d : atomValue(a, vals) >= a.d)

// The pool for one mode: the facts true at every state of the run in that mode, scored (0: an equality; 1: a bound
// whose slack never shrinks along the run; 2: the rest), one value before two.
function pool(runVals: number[][], nObs: number): Atom[] {
  const out: Atom[] = []
  const add = (coefs: [number, number][]) => {
    const vs = runVals.map(vals => coefs.reduce((s, [i, c]) => s + c * vals[i]!, 0))
    const lo = Math.min(...vs), hi = Math.max(...vs), arity = coefs.length
    if (lo === hi) { out.push({coefs, d: lo, eq: true, score: 0, arity}); return }
    const steady = (sign: number) => vs.every((v, j) => j === 0 || sign * (v - vs[j - 1]!) >= 0) ? 1 : 2
    out.push({coefs, d: lo, eq: false, score: steady(1), arity})
    out.push({coefs: coefs.map(([i, c]) => [i, -c]), d: -hi, eq: false, score: steady(-1), arity})
  }
  for (let i = 0; i < nObs; i++) add([[i, 1]])
  for (let i = 0; i < nObs; i++) for (let j = i + 1; j < nObs; j++) { add([[i, 1], [j, -1]]); add([[i, 1], [j, 1]]) }
  return out.sort((a, b) => a.score - b.score || a.arity - b.arity)
}

// --- the search ---------------------------------------------------------------------------------------------------------

export function findNeverEnds(l: Loop, opts: NeverEndsOptions = {}): NeverEndsVerdict {
  return opts.counted ? counted(opts.counted, () => search(l, opts)) : search(l, opts)
}
function search(l: Loop, opts: NeverEndsOptions): NeverEndsVerdict {
  const wall0 = performance.now(), now = clock, t0 = now(), until = t0 + (opts.ms ?? 10_000), maxTurns = opts.maxTurns ?? 400
  const rand = seeded(opts.seed ?? 7)
  const stats = {runs: 0, turns: 0, policies: 0, rounds: 0, ms: 0, lassoTried: 0, goalSize: 0, accel: 0, accelClosed: 0}
  const done = (v: Omit<NeverEndsVerdict, 'stats'>): NeverEndsVerdict => ({...v, stats: {...stats, ms: Math.round(performance.now() - wall0)}})
  const stateNames = Object.keys(l.state), kept = [...l.params, ...stateNames]
  const allObs = observables(kept), inObs = observables(l.inputs)
  // The modes: state variables compared with a constant by `=` in the loop's conditions (a translated task's pc).
  const modeVars = stateNames.filter(n => [l.while, l.assume ?? T].some(c => JSON.stringify(c).includes(`{"op":"=","a":{"op":"var","name":${JSON.stringify(n)}},"b":{"op":"const"`)))
  const modeOf = (env: Env) => modeVars.map(n => env[n] ?? 0).join(',')
  const modeCond = (key: string): C => and(key === '' ? [] : key.split(',').map((x, i) => eq(V(modeVars[i]!), K(Number(x)))))
  const consts = [...constantsOf(l.while), ...constantsOf(l.assume ?? T)].filter(x => x <= 1_000_000)
  const near = [...new Set(consts.flatMap(c => [c, c + 1, c - 1]))]
  const literal = (x: string) => x.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
  const inConsts = new Map(l.inputs.map(i => [i, [...new Set([0, 1, ...[l.assume ?? T, l.while].flatMap(c => [...JSON.stringify(c).matchAll(new RegExp(literal(`{"op":"=","a":{"op":"var","name":${JSON.stringify(i)}},"b":{"op":"const","value":`) + '(\\d+)', 'g'))].map(m => Number(m[1])))])]]))
  let wh: (env: Env) => boolean, as: (env: Env) => boolean, init: [string, (env: Env) => number][], body: [string, (env: Env) => number][], pre: (env: Env) => boolean
  try {
    wh = cC(l.while); as = cC(l.assume ?? T); pre = cC(l.pre ?? T)
    init = Object.entries(l.state).map(([n, e]) => [n, cE(e)]); body = Object.entries(l.body).map(([n, e]) => [n, cE(e)])
  } catch (e) { return done({proven: false, checked: false, why: (e as Error).message}) }
  const start = (ps: Env): Env => { const env: Env = {...ps}; for (const [n, f] of init) env[n] = f(ps); return env }
  const turn = (st: Env, input: Env): Env | undefined => {
    work.n++
    const at: Env = {...st, ...input}
    if (!wh(at) || !as(at)) return undefined
    const out: Env = {...at}
    for (const [n, f] of body) out[n] = f(at)
    return out
  }
  const keyOf = (env: Env) => kept.map(n => env[n] ?? 0).join(',')
  // A value into an observable: a pair takes any integer, a natural the integer's value below 0 cut to 0 (as the
  // witness's terms write it); a random draw for a natural takes its size.
  const setInt = (o: Obs, x: number, env: Env) => { if (o.n) { env[o.p] = Math.max(x, 0); env[o.n] = Math.max(-x, 0) } else env[o.p] = Math.max(x, 0) }
  const setDraw = (o: Obs, x: number, env: Env) => setInt(o, o.n ? x : Math.abs(x), env)
  const drawInt = (bound: number) => (rand(3) === 0 && near.length ? near[rand(near.length)]! * (rand(4) === 0 ? -1 : 1) : rand(2 * bound + 1) - bound)
  const drawParams = (bound: number): Env | undefined => {
    for (let tries = 0; tries < 20; tries++) {
      const ps: Env = {}
      for (const o of observables(l.params)) setDraw(o, drawInt(bound), ps)
      if (pre(ps)) return ps
    }
    return undefined
  }
  const drawInput = (st: Env, bound: number): Env => {
    const input: Env = {}
    for (const o of inObs) {
      const cs = inConsts.get(o.p) ?? [0]
      const x = !o.n && rand(2) === 0 ? cs[rand(cs.length)]! : rand(4) === 0 && allObs.length ? valueOf(allObs[rand(allObs.length)]!, st) * (rand(2) ? 1 : -1) : drawInt(bound)
      setDraw(o, x, input)
    }
    return input
  }
  // A state a run reached: its params, the run's turns' inputs (shared by every visit of the run) and how many of them
  // lead here.
  type Visit = {params: Env, trail: Env[], at: number, st: Env, run?: {n: number}}
  const stemOf = (v: Visit) => v.trail.slice(0, v.at)
  const certify = (r: Omit<Recur, 'tree'>, by: NeverEndsVerdict['by'], ms = 8000): NeverEndsVerdict | undefined => {
    const goal = recurGoal(l, r)
    stats.goalSize = Math.max(stats.goalSize, goalSize(goal.hyps))
    if (goalSize(goal.hyps) > GOAL_MAX) return undefined
    const out = grow(goal, new Map(), {nodes: 0, until: Math.min(until, now() + ms)})
    if (!('tree' in out)) return undefined
    const recur: Recur = {...r, tree: out.tree}
    let ok = false
    try { ok = checkRecur(l, recur) } catch { ok = false }
    return ok ? done({proven: true, checked: true, recur, by}) : undefined
  }
  const asStem = (inputs: Env[]): Record<string, number>[] => inputs.map(x => Object.fromEntries(l.inputs.map(n => [n, x[n] ?? 0])))
  const params = (ps: Env): Record<string, number> => Object.fromEntries(l.params.map(n => [n, ps[n] ?? 0]))
  // A lasso: the set is the cycle's states (the params and the state), each turn's inputs given at its state.
  const lassoRecur = (v: Visit, cycle: {st: Env, input: Env}[], by: NeverEndsVerdict['by']): NeverEndsVerdict | undefined => {
    if (cycle.length > 64 || cycle.length * kept.length > 600) return undefined
    stats.lassoTried++
    const at = (st: Env) => and(kept.map(n => eq(V(n), K(st[n] ?? 0))))
    const set = or(cycle.map(c => at(c.st)))
    const wit: Record<string, E> = {}
    for (const n of l.inputs) wit[n] = cycle.slice(0, -1).reduceRight<E>((acc, c) => ite(at(c.st), K(c.input[n] ?? 0), acc), K(cycle.at(-1)!.input[n] ?? 0))
    const out = certify({start: params(v.params), stem: asStem(stemOf(v)), set, wit}, by)
    return out && {...out, lasso: {params: params(v.params), stem: asStem(stemOf(v)), cycle: asStem(cycle.map(c => c.input))}}
  }

  // 1. Random runs: the states they reach, each with its stem; a lasso on the way is tried at once.
  const visits: Visit[] = [], bounds = [1, 2, 4, 8, 16, 64]
  try {
    // (a fifth of the time, at most 1.5 s, a run too, unless only lassos are asked for; at most 4,000 states kept, then
    // only a run's last)
    const runsUntil = opts.lassos ? until : Math.min(t0 + (until - t0) * 0.2, t0 + 1500)
    while (now() < runsUntil) {
      const bound = bounds[stats.runs++ % bounds.length]!, ps = drawParams(bound)
      if (!ps) continue
      let st = start(ps)
      const stem: Env[] = [], seen = new Map<string, number>(), trail: Env[] = [], run = {n: 0}
      if (visits.length < 4000) visits.push({params: ps, trail: stem, at: 0, st, run})
      for (let n = 0; n < 3000 && now() < runsUntil; n++) {
        const key = keyOf(st), back = seen.get(key)
        if (back !== undefined) {
          const cycle = trail.slice(back).map((s, j) => ({st: s, input: stem[back + j]!}))
          const v = lassoRecur({params: ps, trail: stem, at: back, st: trail[back]!}, cycle, 'lasso')
          if (v) return v
          break
        }
        seen.set(key, n); trail.push(st)
        let next: Env | undefined, input: Env | undefined
        for (let tries = 0; tries < 40 && !next; tries++) { input = drawInput(st, bound); next = turn(st, input) }
        if (!next) break
        stem.push(input!); stats.turns++; run.n++
        st = next
        if ((n % 50 === 49 || n < 8) && visits.length < 4000) visits.push({params: ps, trail: stem, at: stem.length, st, run})
      }
      if (visits.length < 20000 || run.n >= 100) visits.push({params: ps, trail: stem, at: stem.length, st, run})
    }
  } catch (e) { if (!(e instanceof Overflow)) return done({proven: false, checked: false, why: (e as Error).message.slice(0, 200)}) }

  if (opts.lassos) return done({proven: false, checked: false, why: `no lasso in ${stats.runs} runs`})
  // 1b. Accelerated cycles (core/accel.ts): a set from a cycle of the relation, a stem into it, its closure proven.
  if ((opts.accel ?? 0.4) > 0) {
    const accelUntil = Math.min(until, now() + (until - now()) * (opts.accel ?? 0.4)), m = loopMachine(l), longUntil = Math.max(until, t0 + (opts.extend ?? 0))
    try {
      // (the random runs, the longest 20, for the cycles they take)
      const ends = new Map<object, Visit>()
      for (const v of visits) if (v.run && (ends.get(v.run)?.at ?? -1) < v.at) ends.set(v.run, v)
      const runs = [...ends.values()].sort((a, b) => b.at - a.at).slice(0, 20).map(v => ({params: v.params, inputs: stemOf(v)}))
      // A set's closure (`budget`: when it stops), then, where no stem is known, the accelerated runs' search deeper and a
      // bounded run (core/bmc.ts: the kernel's k-step goal's model, the set's complement as the law it breaks), then the
      // kernel's check of each stem; `late` where the closure ran out of time.
      const attempt = (a: ReturnType<typeof accelerated> extends Generator<infer T> ? T : never, goal: ReturnType<typeof recurGoal>, stems: {params: Env, stem: Env[]}[], cut: (t: {params: Env, stem: Env[]}) => {params: Env, stem: Env[]} | undefined, budget: number): NeverEndsVerdict | 'late' | undefined => {
        // (a model of the CDCL search whose products don't multiply out goes on to the plain search, which multiplies rows)
        const was = realModels.on
        realModels.on = true
        // (a large goal by its cases, where the set's parts are at locations: each part's goal its location substituted
        // and its constants folded, which leaves the rules at that location, and the cover)
        const byCases = opts.cases && a.cases && dagSize(goal.hyps) > CASES_FROM ? a.cases : undefined
        let closed: {tree: Tree} | {cover: Tree, cases: RecurCases['cases']} | undefined, late = false
        try {
          for (const g of byCases ? [coverGoal({set: a.set, cases: byCases}), ...caseGoals(l, a, byCases)] : [goal]) {
            const out = grow(g, new Map(), {nodes: 0, until: budget})
            if (!('tree' in out)) { late = out.stuck === 'unknown' && out.why !== undefined; closed = undefined; break }
            if (!byCases) closed = {tree: out.tree}
            else if (!closed) closed = {cover: out.tree, cases: []}
            else if ('cases' in closed) closed.cases.push({...byCases[closed.cases.length]!, tree: out.tree})
          }
        } finally { realModels.on = was }
        if (!closed) return late ? 'late' : undefined
        stats.accelClosed++
        // (the accelerated runs' search again, deeper: fun9's stem of 30 turns)
        if (!stems.length && now() < until) for (const t of stemsTo(l, a.targets, {start, turn}, {now, until: Math.min(until, now() + 1000), deepen: true})) { const c = cut(t); if (c) { stems.push(c); break } }
        if (!stems.length && now() < until) {
          const left = Math.min(until - now(), 2000)
          const run = findBoundedRun(m, [{name: 'outside the set', holds: {op: 'not', x: a.set}}], {ms: left, depth: 24, ...(opts.counted ? {} : {wall: performance.now() + left})})
          const c = run && cut({params: run.params as Env, stem: run.trace.map(r => Object.fromEntries(l.inputs.map(n => [n, Number(r[n] ?? 0)])))})
          if (c) stems.push(c)
        }
        for (const t of stems) {
          const base = {start: params(t.params), stem: asStem(t.stem), set: a.set, wit: a.wit}
          if ('cases' in closed) {
            const cases: RecurCases = {...base, ...closed}
            let ok = false
            try { ok = checkRecurCases(l, cases) } catch { ok = false }
            if (ok) return done({proven: true, checked: true, cases, by: 'accelerated'})
            continue
          }
          const recur: Recur = {...base, tree: closed.tree}
          let ok = false
          try { ok = checkRecur(l, recur) } catch { ok = false }
          if (ok) return done({proven: true, checked: true, recur, by: 'accelerated'})
        }
        return undefined
      }
      // (sets with a small goal that the accelerated runs' search, run to its end, doesn't reach: after the rest, their
      // closures and bounded runs, in the time the search has left)
      const later: {a: Parameters<typeof attempt>[0], goal: ReturnType<typeof recurGoal>, cut: Parameters<typeof attempt>[3]}[] = []
      let deepened = 0
      const again: {a: Parameters<typeof attempt>[0], goal: ReturnType<typeof recurGoal>, stems: Parameters<typeof attempt>[2], cut: Parameters<typeof attempt>[3]}[] = []
      // (the search for the next candidate has its own time: a closure tried on a set a stem reaches doesn't count
      // against it, up to `extend`; so a set whose closure runs out of time leaves the time to look for a smaller one)
      // (a large loop's relation takes seconds to build, once: the search for candidates starts when it is built, up to
      // 10 s later; pgarch's 203 locations, 4 s to build its loop and 13 s its relation on a laptop)
      const built = now()
      relationBuilt(l)
      let genUntil = accelUntil + Math.min(10_000, now() - built)
      for (const a of accelerated(l, {now, get until() { return genUntil }, runs, io: {start, turn}})) {
        stats.accel++
        const goal = recurGoal(l, a)
        stats.goalSize = Math.max(stats.goalSize, goalSize(goal.hyps))
        // (past the cap a goal is closed only by its cases, each at one location)
        if (dagSize(goal.hyps) > ACCEL_DAG_MAX && !(opts.cases && a.cases)) continue
        const inSet = cC(a.set)
        // A stem into the set, cut where it first enters it (every turn allowed): from a state a random run reached (the
        // shortest), else an accelerated run (cheap: tried before the closure, which is not tried for a set no stem
        // reaches), else, once the set is closed, a bounded run.
        const cut = (t: {params: Env, stem: Env[]}): {params: Env, stem: Env[]} | undefined => {
          let st = start(t.params)
          for (let j = 0; j <= t.stem.length; j++) {
            if (inSet(st)) return {params: t.params, stem: t.stem.slice(0, j)}
            if (j === t.stem.length) return undefined
            const nx = turn(st, t.stem[j]!)
            if (!nx) return undefined
            st = nx
          }
          return undefined
        }
        const stems: {params: Env, stem: Env[]}[] = [], report = {exhausted: false}
        let best: Visit | undefined
        for (const v of visits) if ((!best || v.at < best.at) && inSet(v.st)) best = v
        if (best) {
          stems.push(cut({params: best.params, stem: stemOf(best)}) ?? {params: best.params, stem: stemOf(best)})
          // (a run's stem past 64 turns, which Lean replays turn by turn over the whole loop: a shorter one of the
          // accelerated runs' search first, where it finds one within 500 ms)
          if (stems[0]!.stem.length > 64) for (const t of stemsTo(l, a.targets, {start, turn}, {now, until: Math.min(longUntil, now() + 500)})) { const c = cut(t); if (c && c.stem.length < stems[0]!.stem.length) { stems.unshift(c); break } }
        } else {
          // (a set's stem has time of its own, past the stage's if need be, within the search's)
          let n = 0
          for (const t of stemsTo(l, a.targets, {start, turn}, {now, until: Math.min(longUntil, now() + 1000), report})) {
            const c = cut(t)
            if (c) { stems.push(c); break }
            if (++n >= 4) break
          }
          // (a set that search, run to its end, doesn't reach: again deeper, at most 500 ms, for the first four)
          if (!stems.length && report.exhausted && deepened++ < 4) for (const t of stemsTo(l, a.targets, {start, turn}, {now, until: Math.min(longUntil, now() + 500), deepen: true})) { const c = cut(t); if (c) { stems.push(c); break } }
        }
        // (a set the accelerated runs' search, run to its end, doesn't reach is left: the time goes to sets a run
        // reaches; a small one is tried after them)
        if (!stems.length && report.exhausted) { if (dagSize(goal.hyps) <= 50_000 && later.length < 8) later.push({a, goal, cut}); continue }
        // (a set with a stem is likely: its closure may take most of what is left, past the stage's share; one without,
        // the stage's share and at most 4 s)
        const tried = now()
        const v = attempt(a, goal, stems, cut, stems.length ? Math.min(until, now() + Math.max(4000, (until - now()) * 0.6)) : Math.min(accelUntil, now() + 4000))
        if (v && v !== 'late') return v
        if (stems.length) genUntil = Math.max(genUntil, Math.min(longUntil - 1000, genUntil + now() - tried))
        if (v === 'late' && stems.length && longUntil > until) again.push({a, goal, stems, cut})
      }
      // (the small sets no stem reaches: a closure and a bounded run each, in what is left of the search's time)
      for (const {a, goal, cut} of later) {
        if (now() >= until) break
        const v = attempt(a, goal, [], cut, Math.min(until, now() + 2000))
        if (v && v !== 'late') return v
      }
      // (a set with a stem whose closure ran out of time: again, with the time `extend` gives, the smaller goal first,
      // each its share of what is left by its goal's size, the closure's work growing with it)
      const sized = again.map(x => ({...x, size: dagSize(x.goal.hyps)})).sort((x, y) => x.size - y.size).slice(0, 6)
      for (const [k, {a, goal, stems, cut, size}] of sized.entries()) {
        if (now() >= longUntil - 1000) break
        const share = size / sized.slice(k).reduce((s, x) => s + x.size, 0)
        const v = attempt(a, goal, stems, cut, Math.min(longUntil, now() + Math.max(2000, (longUntil - now()) * 0.9 * share)))
        if (v && v !== 'late') return v
      }
    } catch (e) { if (!(e instanceof Overflow)) throw e }
  }
  // 2. Policies from the states reached.
  const pools = inObs.map(o => {
    const terms: ITerm[] = [iConst(0), iConst(1)]
    if (o.n) terms.push(iConst(-1))
    for (const c of inConsts.get(o.p) ?? []) if (c > 1) terms.push(iConst(c))
    for (const x of allObs) for (const c of [0, 1, -1]) terms.push(iAdd(iObs(x), c))
    return terms
  })
  const compiled = new Map<ITerm, [(env: Env) => number, (env: Env) => number]>()
  const evalT = (t: ITerm, env: Env) => { let f = compiled.get(t); if (!f) { f = [cE(t.p), cE(t.n)]; compiled.set(t, f) } return f[0](env) - f[1](env) }
  const fuzzy = (c: C): ((env: Env) => number) => {
    if (c.op === 'and') { const xs = c.xs.map(fuzzy); return env => xs.reduce((s, x) => s + x(env), 0) / xs.length }
    if (c.op === 'or') { const xs = c.xs.map(fuzzy); return env => Math.max(...xs.map(x => x(env))) }
    const b = cC(c); return env => (b(env) ? 1 : 0)
  }
  const turnDegree = fuzzy({op: 'and', xs: [l.while, l.assume ?? T]})
  const degree = (st: Env, input: Env) => { work.n++; try { return turnDegree({...st, ...input}) } catch { return 0 } }
  type Assign = number[] // a pool index per input observable
  const inputOf = (a: Assign, st: Env): Env => { const out: Env = {}; inObs.forEach((o, i) => setInt(o, evalT(pools[i]![a[i]!]!, st), out)); return out }
  const allowedC = (a: Assign, mode: string): C => {
    const sub: Record<string, E> = {}
    inObs.forEach((o, i) => Object.assign(sub, iInto(pools[i]![a[i]!]!, o)))
    if (mode !== '') mode.split(',').forEach((x, i) => { sub[modeVars[i]!] = K(Number(x)) })
    return simpC(substC({op: 'and', xs: [l.while, l.assume ?? T]}, {vars: sub, maps: {}, flags: {}}))
  }
  // The seeds: states of the longest runs, the shallowest first (a short stem), then the rest by depth.
  const longest = Math.max(0, ...visits.map(v => v.run?.n ?? 0))
  const order = visits.map((v, i) => ({v, i, d: v.at, long: (v.run?.n ?? 0) >= Math.min(200, longest) ? 0 : 1}))
    .sort((a, b) => a.long - b.long || a.d - b.d || a.i - b.i)
  // (and, in turn, the deepest: a run that went on is past the choices its start needed)
  const deep = [...order].sort((a, b) => b.d - a.d || a.i - b.i), seeds: Visit[] = []
  for (let j = 0; j < order.length; j++) seeds.push(order[j]!.v, deep[j]!.v)
  for (let s = 0; s < seeds.length * 3 && now() < until; s++) {
    const v = seeds[s % seeds.length]!
    stats.policies++
    const policy = new Map<string, Assign[]>()
    let st = v.st
    const states: Env[] = [], inputs: Env[] = [], seen = new Map<string, number>()
    let stop: 'repeat' | 'long' | 'stuck' = 'stuck', back = -1
    try {
      for (let n = 0; n < maxTurns && now() < until; n++) {
        const key = keyOf(st)
        if (seen.has(key)) { stop = 'repeat'; back = seen.get(key)!; break }
        seen.set(key, n); states.push(st)
        const mode = modeOf(st), chain = policy.get(mode) ?? []
        let next: Env | undefined, input: Env | undefined
        for (const a of chain) { input = inputOf(a, st); next = turn(st, input); if (next) break }
        if (!next && chain.length < 4) {
          // A local search on how much of the turn's condition an assignment meets (a conjunction the share of its
          // parts, a disjunction its best part), one input at a time, from a few random starts.
          for (let restart = 0; restart < 6 && !next && now() < until; restart++) {
            const zero = restart === 0 && rand(3) === 0, a = pools.map(p => (zero ? 0 : rand(p.length)))
            let best = degree(st, inputOf(a, st))
            for (let sweep = 0; sweep < 4 && best < 1 && now() < until; sweep++) {
              let moved = false
              for (const i of pools.map((_, j) => j).sort(() => rand(2) - 0.5)) {
                // (a wide pool is tried at 24 of its terms, drawn afresh each sweep)
                const tries = pools[i]!.length <= 24 ? pools[i]!.map((_, j) => j) : Array.from({length: 24}, () => rand(pools[i]!.length))
                for (const j of tries) {
                  if (best >= 1) break
                  const was = a[i]!
                  a[i] = j
                  const d = degree(st, inputOf(a, st))
                  if (d > best) { best = d; moved = true } else a[i] = was
                }
              }
              if (!moved) break
            }
            input = inputOf(a, st); next = turn(st, input)
            if (next) { chain.push(a); policy.set(mode, chain) }
          }
        }
        if (!next) { states.pop(); break }
        inputs.push(input!); stats.turns++
        st = next
        if (n === maxTurns - 1) stop = 'long'
      }
    } catch (e) { if (e instanceof Overflow) stop = states.length >= 40 ? 'long' : 'stuck'; else continue }
    if (stop === 'repeat') {
      const cycle = states.slice(back).map((x, j) => ({st: x, input: inputs[back + j]!}))
      const out = lassoRecur({params: v.params, trail: [...stemOf(v), ...inputs.slice(0, back)], at: v.at + back, st: states[back]!}, cycle, 'policy lasso')
      if (out) return out
    }
    if (stop === 'stuck' && states.length < 40) continue
    // The witness: each input by mode, then the first allowed of the mode's assignments.
    const modes = [...policy.keys()]
    const wit: Record<string, E> = {}
    const allowed = new Map(modes.map(m => [m, policy.get(m)!.map(a => allowedC(a, m))]))
    inObs.forEach((o, i) => {
      for (const part of o.n ? [o.p, o.n] : [o.p]) {
        const byMode = (m: string): E => {
          const chain = policy.get(m)!, cs = allowed.get(m)!
          const val = (a: Assign) => iInto(pools[i]![a[i]!]!, o)[part]!
          return chain.slice(0, -1).reduceRight<E>((acc, a, j) => ite(cs[j]!, val(a), acc), val(chain.at(-1)!))
        }
        wit[part] = modes.slice(0, -1).reduceRight<E>((acc, m) => ite(modeCond(m), byMode(m), acc), modes.length ? byMode(modes.at(-1)!) : K(0))
      }
    })
    // The set: from a burn-in on, the run's states by mode; the constant facts first, then one atom per counterexample.
    const burn = Math.min(Math.floor(states.length / 4), 8), sample = states.slice(burn)
    const byMode = new Map<string, number[][]>()
    for (const x of sample) { const m = modeOf(x); if (!policy.has(m)) continue; byMode.set(m, [...(byMode.get(m) ?? []), allObs.map(o => valueOf(o, x))]) }
    if ([...byMode.keys()].length === 0) continue
    const atoms = new Map<string, Atom[]>(), pools2 = new Map<string, Atom[]>()
    // (an equality of two values goes in only where neither is constant: the constants' equalities imply it)
    for (const [m, vals] of byMode) {
      const p = pool(vals, allObs.length), fixed = new Set(p.filter(a => a.score === 0 && a.arity === 1).map(a => a.coefs[0]![0]))
      pools2.set(m, p); atoms.set(m, p.filter(a => a.score === 0 && (a.arity === 1 || a.coefs.every(([i]) => !fixed.has(i)))))
    }
    const setOf = (): C => {
      const ms = [...byMode.keys()]
      if (modeVars.length === 0) return and(atoms.get('')!.map(a => atomC(a, allObs)))
      return and([or(ms.map(modeCond)), ...ms.map(m => or([{op: 'not', x: modeCond(m)}, and(atoms.get(m)!.map(a => atomC(a, allObs)))]))])
    }
    const first = burn
    const stemTo = {start: params(v.params), stem: asStem([...stemOf(v), ...inputs.slice(0, first)])}
    for (let round = 0; round < 40 && now() < until; round++) {
      stats.rounds++
      const set = setOf()
      const goal = recurGoal(l, {set, wit})
      stats.goalSize = Math.max(stats.goalSize, goalSize(goal.hyps))
      if (goalSize(goal.hyps) > GOAL_MAX) break
      const out = grow(goal, new Map(), {nodes: 0, until: Math.min(until, now() + 6000)})
      if ('tree' in out) {
        // The stem: to the first state of the run (from the start, through the seed's stem and the policy's turns) in
        // the set.
        const inSet = cC(set), all = [...stemOf(v), ...inputs]
        let at = start(v.params), cut = stemTo.stem.length
        for (let j = 0; j <= all.length; j++) {
          if (inSet(at)) { cut = j; break }
          if (j === all.length) break
          const nx = turn(at, all[j]!)
          if (!nx) break
          at = nx
        }
        const recur: Recur = {...stemTo, stem: asStem(all.slice(0, cut)), set, wit, tree: out.tree}
        let ok = false
        try { ok = checkRecur(l, recur) } catch { ok = false }
        if (ok) return done({proven: true, checked: true, recur, by: 'recurrent set'})
        break
      }
      if (out.stuck !== 'sat' || !out.witness) break
      // The counterexample: a state of the set; an atom of its mode false there, true along the run.
      const w = out.witness, rho: Env = Object.fromEntries([...kept, ...l.inputs].map(n => [n, Math.round(w[n] ?? 0)]))
      const m = modeVars.length ? modeOf(rho) : ''
      const cand = pools2.get(m), vals = allObs.map(o => valueOf(o, rho)), have = atoms.get(m)
      const pick = cand?.find(a => !have!.includes(a) && !atomHolds(a, vals))
      if (!pick) break
      have!.push(pick)
    }
  }
  return done({proven: false, checked: false, why: `no run found that never ends (${stats.runs} runs, ${stats.policies} policies, ${stats.rounds} rounds)`})
}
