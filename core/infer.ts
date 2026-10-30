// Invariants nobody wrote: a law that holds but isn't inductive, proven with laws the search finds. Nothing here is
// trusted; what it finds is proven by the kernel with the rule's own laws, as laws of the same rule.
//   - runs: random runs from the start (params and requests by their kinds, the assumption met) give reachable states,
//     3,000 kept as samples
//   - candidates: linear forms Σ c·v ≤ d over the state and the params (an integer as its value, its two naturals
//     together), up to three terms with small coefficients and the rule's own constants, each d the largest value the
//     runs reached (and the rule's constants just above it); the same forms where a yes/no, a choice or a small natural
//     holds one value (locked is 0 → …), and a choice's value no run reached as unreachable; and laws about every key
//     of the maps: forms over the cells at one key (and a scalar), at every key or every key but a scalar's (k = owner
//     or …), and where a cell holds one value
//   - Houdini on the runs' neighbors: a reached state moved a little that every candidate alive and every law allows,
//     stepped; a candidate its step breaks is in no inductive set of them, so it is dropped
//   - the join, over the rule's own vocabulary: per control state the samples' affine hull (its equalities, exact) and
//     each direction's largest value. Two spaces: the states (a row each), and for a rule with maps the cells at a key
//     (a row per key a state holds and a fresh one, its forms laws at every key). The control state: the choice (loc)
//     and a few yes/nos, then, refined on demand (as CEGAR refines its predicates), the levels the rule's comparisons
//     with a constant cut a value or a cell into (Ts[k] ≤ 1 or past it, inflight 0 or more, a yes/no param). The values:
//     the state, the params, the cells at the key, and the terms the laws read that aren't linear (max(attempts, 1)).
//     The directions: each value up and down, pairs where there are few, the rule's own comparisons (its flags', a clock
//     moved by a request read as the clock after), and the laws' preimages: a law's comparison read after the step
//     through each branch of its terms, the request's values eliminated against the step's own comparisons, and a form's
//     own when its goal has a counterexample. Houdini on the cone of the caller's laws and step laws: each goal proven
//     with as little of that set assumed as will do (none, then the forms a counterexample breaks, as IC3's relative
//     induction, then all), each asked first of the CDCL search for a model alone (a refutation's core: the forms it
//     read), a counterexample the whole set allows joined in (the hull grows to hold it, a bound rises to the next of
//     the rule's constants, then goes), one to a caller's law ruled out by a level of the control that leaves it out, a
//     candidate, or a cube blocked as IC3 blocks one (its control state, the rule's own comparisons true there and the
//     bounds that keep the samples out, the literals its refutation's core read, its predecessors blocked first), the
//     cube first where no sample is at its control state; every goal of the cone proven, the cone is the answer
//   - the kernel (where the join proves nothing, as it was): the laws with the candidates chosen so far, proven one law
//     at a time; when a goal is stuck at a step, its witness is a counterexample to induction, so the candidate that
//     rules it out (and the most of those seen) is added; a chosen candidate that nothing supports, or that makes a proof slow, is dropped; the set proven as a whole
//     is the answer, after each chosen candidate the proof doesn't need is taken out again
import {quietly} from './cyclic.ts'
import {type C, type E, type Fn, type Law, type Machine, type Rand, type Request, type State, all, any, atMost, carriedView, loadJs, divisorsIn, evalC, evalE, get, interpret, machineTerms, fnValue, modName, n, not, plus, same, seeded, times, walk, withArithmetic, x} from './machine.ts'
import {type StepLaw, type Verdict, bool, proveRule, proveSteps, verdictOf} from './dsl.ts'
import {allowed, keysOf, linKey, watch} from './watch.ts'
import {clock, counted, decideLaw, decideNote, machineKey, memoHits, withStrict, fullRate, grow, keyValue, lawInstances, proveLaw, proveLaws, proveSetFast, proveStepLaws, stepLawInstances, usedHyps, withDeadline, withModels, withTrees, withWall} from '../kernel/prove.ts'
import {type Goal, type Instances, assumed, obligations, plainOf, stepLawObligations, substC} from '../kernel/kernel.ts'
import {env, gcd, work} from './solver.ts'
import {bgcd} from './q.ts'
import {showC, showE} from './exists.ts'
import {REFUTED, type Refuted, growCdcl} from '../kernel/cdcl.ts'

type AnyRule = Parameters<typeof proveRule>[0]
type Env = Record<string, number>

// The search's budgets are counted in what it did, not timed, so that what it finds is the same on any machine (kernel/
// prove.ts's `counted` does the same for the datatype search): the runs by the requests they try (`runs`), the rest by
// the rows it reads, the forms it evaluates, the laws it watches and the kernel's work (the solver's rows), each at its
// rate a millisecond (`inferRates`). `ms` is that budget in counted milliseconds, and the search's wall time too, a stop:
// reached, it ends the search where it is (`stats.stopped`; what was found then depends on the machine). Precedence:
// `timed` times every budget, as before (`ms` the search's, `runsMs` the runs', 500 ms), for a benchmark under a
// wall-clock limit (compare/chc/solve.ts); else `runsMs`, given, times the runs alone; else everything is counted.
export type InferOptions = {
  ms?: number // the whole search's budget, counted, and its wall time, a stop (20 s)
  runs?: number // the random runs: at least this many requests tried, and on until the samples are full (16,000; trials at most that many, or 3,000)
  runsMs?: number // the random runs by wall time instead (500 ms where `timed`)
  timed?: boolean // every budget by wall time: `ms` the search's, `runsMs` the runs'
  seen?: State[] // reachable states the caller already has (of a rule with no params), beside the runs
  constants?: number[] // more constants for the coefficients and bounds
  maxCandidates?: number // past this many, the search keeps the simplest (60,000)
  first?: Verdict // the laws' verdict alone, when the caller has it already
  progress?: (phase: string, info: Record<string, number | string>) => void // told as each phase ends
  existentials?: boolean // congruences as "there exists" (∃k. v = c·k + r), where the runs keep v's remainder (true)
  minimize?: boolean // once proven, each chosen law the proof doesn't need taken out again (true); false answers at once
  remainders?: boolean // remainders (v mod k = r, a guard where only some runs keep one) where the runs keep one (true); with false, congruences instead (`existentials`)
  join?: number // the join's share of what is left of the search after the candidates (0.6)
}
// What was found: each law as a Law (pass it with the rule's laws), how it reads, and for a rule, the builder call
// that states it (`r.law(...)`), to paste.
export type Found = {law: Law, text: string, source?: string}
export type Inferred = Verdict & {found: Found[], stats: {samples: number, candidates: number, alive: number, proofs: number, ms: number, stopped: boolean}}

// An atom: a value the forms read, the naturals it is made of with their signs (an integer is pos − neg); a cell atom
// is a map's cell at the law's key (its parts are maps).
// A term atom (`term`) is a term the laws read that isn't linear, over the state and params: a value of its own.
// A view's atom (`view`, `place`) is a map's cell at one of a view's places (Known[x], Known[y], Link[N·x + y]).
type Atom = {name: string, parts: [string, 1 | -1][], param: boolean, int: boolean, cell: boolean, term?: E, place?: number, view?: number}
// (`hi`: the value up to `hi` from `value`, Infinity for no end: a level of a value the rule compares with constants)
type Guard = {atom: number, value: number, hi?: number} | {keyNot: number}
// `when`: a linear condition the form holds under (Σ c·v ≤ d over scalars), beside its guard; the search makes such forms
// from a counterexample to induction no candidate rules out.
// `mod`: the form is a remainder, (Σ c·v) mod k = r (d unused). `cong`: a congruence, ∃k. Σ c·v = mod·k + rest
// (core/exists.ts: proven through a witness, a ghost the kernel's counterexamples choose), k a natural or, over an
// integer, an integer; the same claim, made only where remainders are off (InferOptions.remainders).
// `also`: more values the form holds under, beside its guard (a control state: loc and the yes/nos at once); `never`:
// values never all held at once (a control state no run reaches). The join makes both.
// `nevers`: control states none of which is ever held (the join's control states no run reached, one law for all).
// `cube`: literals never all true at once (a value at one value, or Σ c·v ≤ d): a cube the join blocked.
type At = {atom: number, value: number, hi?: number}
// a value outside a guard's (or a control value's) values
const off = (g: At, v: number) => v < g.value || v > (g.hi ?? g.value)
type Lit = {at: At} | {lin: {coef: [number, number][], d: number}}
type Form = {coef: [number, number][], d: number, cells: boolean, view?: number, guard?: Guard, also?: At[], when?: {coef: [number, number][], d: number}, unreachable?: At, never?: At[], nevers?: At[][], cube?: Lit[], mod?: {k: number, r: number}, cong?: {mod: number, rest: number}, size: number}

const KEY = 'key$found', KEY2 = 'key2$found', AT = '@', K = '#', SOME = 'k$found'
// The counted clock's rates, units a millisecond: about the slowest tenth of what Modal's 1-vCPU containers do in each
// phase (`runs/modal/infer/after2`, GDP_INFER_TRACE=1: requests tried 85 a ms, rows 13,093, forms evaluated 11,240, the
// kernel's work 37; laws watched 198 by a fit), so a counted budget runs out no later than a timed one would there.
// The runs' requests: 16,000, 400 trials of a rule whose every request is allowed. Every search of the suite's and the
// frontier corpus's then keeps 3,000 samples, at least as many as 500 ms of wall time gave on 2 vCPU (`runs/modal/infer/
// before`'s cal2 jobs: 29 to 11,625 trials, 745 to 3,000 samples). Of 100 to 3,000 trials (`runs/modal/infer/grid`),
// 100 lost a corpus item (metered blocks) and 200 to 3,000 none: 400 is a step above the least that lost none.
export const inferRates = {tries: 100, rows: 10_000, evals: 10_000, watched: 100, work: 40}
export const inferRuns = 16_000
// GDP_INFER_TRACE=1: each phase's wall time beside what it counted, to stderr (the calibration's numbers).
const inferTrace = !!env.GDP_INFER_TRACE
// The join (below, after the candidates): GDP_JOIN=0 turns it off, for comparing. Its share of what is left of the
// search's budget; each kernel search's budget (counted, or wall time where timed), a request's 150 ms; the steps a walk
// from a joined state takes; pairs of values as directions up to 10 values; a bound raised twice at most, then dropped;
// equalities of at most 4 values, coefficients up to 1,000; at most 24 candidates beside the hull, 40 tried; yes/nos in
// the control state up to 7, and 128 of its values; a goal tried with 6 parts of the set before all of it, 2 forms added
// at a time.
const joinOn = env.GDP_JOIN !== '0'
const joinShare = 0.6, joinQueryMs = 8000, joinGrowWall = 2000, joinRequestMs = 150, joinWalk = 8, joinPairs = 10, joinRaises = 2, joinSparse = 4, joinCoef = 1000
const joinExtras = 24, joinTries = 40, joinBits = 7, joinKeys = 128, joinAttempts = 6, joinAdd = 2
// GDP_JOIN_CORE=0: the join's goals by the prover's trees alone, as before (else a model, or a refutation's core, of the
// CDCL search first, at a quarter of the goal's budget).
// GDP_JOIN_NEVERS=0: each control state no run reached a form of its own, as before (else one form for all of them,
// until it is first broken).
const joinNevers = env.GDP_JOIN_NEVERS !== '0'
const joinNeversBreaks = 1
const joinCore = env.GDP_JOIN_CORE !== '0'
// Cubes blocked for a counterexample to a caller's law (GDP_JOIN_CUBES=0: none), before any candidate is tried where
// no sample holds its control state, else where none rules it out: at most 48 in all, each tried 8 times, its
// predecessors blocked first 8 deep, each query's budget 2 s (counted, or wall time where timed).
const joinCubes = env.GDP_JOIN_CUBES !== '0'
const joinCubeMax = 48, joinCubeTries = 8, joinCubeDepth = 8, joinCubeMs = 2000
// GDP_JOIN_ATOMS=0: a cube's literals at a point its control values and the samples' bounds alone (else the rule's own
// comparisons true there too).
const joinAtoms = env.GDP_JOIN_ATOMS !== '0'
// GDP_JOIN_PRIME=0: each control state no state reached a form of its own, every value read.
const joinPrime = env.GDP_JOIN_PRIME !== '0'
// GDP_JOIN_DOWN=0: a blocked cube kept as its refutation's core cuts it (no literal dropped); joinDownQueries, the
// queries a cube's generalization may ask.
const joinDown = env.GDP_JOIN_DOWN !== '0', joinDownQueries = 24
// GDP_INFER_HALVES=0: a cell form chosen without its equality's other half (below).
// GDP_JOIN_LEVELS=0: the join's control never refined by the levels of the rule's comparisons (the join, `refine`);
// GDP_JOIN_CLOCKS=0: a request's value a step adds to a state variable kept apart from it in the rule's comparisons.
const inferHalves = env.GDP_INFER_HALVES !== '0'
const isRule = (t: AnyRule | Machine): t is AnyRule => typeof (t as AnyRule).kindsOfState === 'function'

// The constants a machine's expressions hold, and the factors it multiplies by.
function constantsOf(m: Machine, laws: Law[]): number[] {
  const out = new Set<number>()
  const e = (t: E): void => {
    switch (t.op) {
      case 'const': out.add(t.value); break
      case 'var': break
      case 'mul': out.add(t.k); e(t.a); break
      case 'add': case 'sub': case 'min': case 'max': case 'prod': e(t.a); e(t.b); break
      case 'if': c(t.c); e(t.then); e(t.else); break
      case 'get': e(t.key); break
    }
  }
  const c = (t: C): void => {
    switch (t.op) {
      case '<': case '<=': case '=': e(t.a); e(t.b); break
      case 'and': case 'or': t.xs.forEach(c); break
      case 'not': c(t.x); break
      case 'flag': break
      case 'all': c(t.c); break
    }
  }
  Object.values(m.state).forEach(e)
  Object.values(m.step.state ?? {}).forEach(e)
  Object.values(m.step.flags ?? {}).forEach(c)
  for (const w of Object.values(m.step.maps ?? {})) { if ('key' in w) e(w.key); e(w.value) }
  if (m.assume) c(m.assume)
  if (m.pre) c(m.pre)
  laws.forEach(l => c(l.holds))
  return [...out].filter(k => Number.isSafeInteger(k) && Math.abs(k) <= 1e6)
}

// Two keys a rule composes into one, N·a + b (+ c) of two of its inputs, a map read or written there (Casbin's link
// table, Link[a·64 + b]): the frame (what its assumption says of a and b alone, over x and y), N, c. The first.
type Pairing = {n: number, c: number, frame: C}
// A view: the cells at a few keys (`vars`, shown as `names`) at the places the rule or a caller's law reads them
// (`places`, key terms over the vars, each with the vars it `covers`), a row per assignment of keys a state holds that
// the frame allows (`rowsOf`); its forms, laws at every tuple of the keys, read places covering at least `need` of them.
// The pair space is one: two keys, and the key the rule composes of them where it composes one.
type View = {vars: string[], names: string[], places: E[], covers: number[][], frame: C, need: number, rowsOf: (params: Env, st: State, full?: boolean) => Env[], atoms: number[], rows: Env[], printable: boolean}
// A key's linear form over the names `ok` admits, into `out` (`1` the constant); false where it is none.
const conj = (c: C): C[] => (c.op === 'and' ? c.xs.flatMap(conj) : [c])
function pairingOf(m: Machine): Pairing | undefined {
  const inputs = new Set(m.inputs), input = (v: string) => inputs.has(v)
  let found: Pairing | undefined
  const each = new Set(Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [w.each] : [])))
  const consider = (key: E) => {
    if (found) return
    const l = new Map<string, number>()
    if (!linKey(key, input, 1, l)) return
    const vs = [...l].filter(([v, c]) => v !== '1' && c)
    if (vs.length !== 2) return
    const [[a, ca], [b, cb]] = vs[0]![1] >= vs[1]![1] ? [vs[0]!, vs[1]!] : [vs[1]!, vs[0]!]
    if (cb !== 1 || ca < 2) return
    const names = (c: C) => [...JSON.stringify(c).matchAll(/"name":"([^"]+)"/g)].map(q => q[1]!)
    const own = m.assume ? conj(m.assume).filter(c => names(c).length && names(c).every(v => v === a || v === b)) : []
    found = {n: ca, c: l.get('1') ?? 0, frame: substC({op: 'and', xs: own}, {vars: {[a]: x(KEY), [b]: x(KEY2)}, maps: {}, flags: {}})}
  }
  const visit = (t: unknown): void => {
    if (!t || typeof t !== 'object') return
    if (Array.isArray(t)) { t.forEach(visit); return }
    const o = t as {op?: string, key?: E, a?: E, b?: E}
    if (o.op === 'get' && o.key && m.maps && (o as {map?: string}).map! in m.maps) consider(o.key)
    if (o.op === '=' && o.a?.op === 'var' && each.has(o.a.name) && o.b) consider(o.b)
    for (const v of Object.values(o)) if (typeof v === 'object') visit(v)
  }
  visit([m.step, m.assume])
  return found
}

// The key's sort, read off the rule and the caller's laws: a key read at a map's plain key is of that map's key sort;
// at a key the rule composes (N·a + b + c, pairingOf's), a is of the rows' sort and b of the columns'; a write at every
// key's key is of its map's, and two keys compared (k = src) are of one sort. Union-find over those places; a law's own
// keys are named apart (`L:law:key`). What a view of a law needs of it: its keys' sorts, the composed keys its reads
// name, its guards on its keys alone, the maps read at a plain key of a sort, and the keys a state holds of a sort.
function keySorts(m: Machine, laws: Law[], pairing?: Pairing) {
  const parent = new Map<string, string>()
  const find = (a: string): string => { const p2 = parent.get(a); if (p2 === undefined || p2 === a) return a; const r = find(p2); parent.set(a, r); return r }
  const union = (a: string, b: string) => { const ra = find(a), rb = find(b); if (ra !== rb) parent.set(ra, rb) }
  const composed = new Set<string>(), plainRead = new Set<string>()
  const split = (key: E, name: (v: string) => string | undefined): [string, string] | undefined => {
    if (!pairing?.n) return undefined
    const lin = new Map<string, number>()
    if (!linKey(key, () => true, 1, lin)) return undefined
    const vs = [...lin].filter(([v, c]) => v !== '1' && c)
    if (vs.length !== 2 || (lin.get('1') ?? 0) !== pairing.c) return undefined
    const hi = vs.find(([, c]) => c === pairing.n), lo = vs.find(([, c]) => c === 1)
    const a = hi && name(hi[0]), b = lo && name(lo[0])
    return a && b ? [a, b] : undefined
  }
  // (a key of three or more parts, N²·a + N·b + c: its parts, each a place of its own, `${k}:${i}`)
  const arity = new Map<string, number>()
  const parts = (key: E, name: (v: string) => string | undefined): string[] | undefined => {
    if (!pairing?.n) return undefined
    const lin = new Map<string, number>()
    if (!linKey(key, () => true, 1, lin) || (lin.get('1') ?? 0) !== pairing.c) return undefined
    const vs = [...lin].filter(([v, c]) => v !== '1' && c).sort((a, b) => b[1] - a[1]), ns = vs.map(([v]) => name(v))
    return vs.length >= 3 && vs.every(([, c], i) => c === pairing.n ** (vs.length - 1 - i)) && ns.every(Boolean) ? ns as string[] : undefined
  }
  const kids = (t: E | C, f: (y: E | C) => void) => { for (const v of Object.values(t)) if (v && typeof v === 'object') (Array.isArray(v) ? v : [v]).forEach(y => { if (y && typeof y === 'object' && 'op' in y) f(y as E | C) }) }
  const walk = (t: E | C, name: (v: string) => string | undefined): void => {
    if (t.op === 'get') {
      // (a carried map's key has its cells' sort, as a map's: the quorum a request brings, read where the stored one is)
      const carried = (m.inputMaps ?? []).includes(t.map)
      // (a function of a key: its argument's sort, `F:f`)
      if (m.fns?.[t.map] && t.key.op === 'var' && name(t.key.name)) { union(name(t.key.name)!, `F:${t.map}`); return }
      if (!carried && !(t.map in (m.maps ?? {}))) { walk(t.key, name); return }
      if (carried) { if (t.key.op === 'var' && name(t.key.name)) union(name(t.key.name)!, `M:${t.map}`); else walk(t.key, name); return }
      const sp = split(t.key, name), ps = parts(t.key, name)
      if (sp) { composed.add(t.map); union(sp[0], 'hi'); union(sp[1], 'lo'); return }
      if (ps) { arity.set(t.map, ps.length); ps.forEach((q, i) => union(q, `${t.map}:${i}`)); return }
      if (t.key.op === 'var' && name(t.key.name)) { plainRead.add(t.map); union(name(t.key.name)!, `M:${t.map}`); return }
      walk(t.key, name); return
    }
    if (t.op === 'all') { const own = new Set([t.key, ...(t.keys ?? [])]); walk(t.c, v => (own.has(v) ? `Q:${JSON.stringify(t).length}:${v}` : name(v))); return }
    if (t.op === '=' && t.a.op === 'var' && t.b.op === 'var') { const a = name(t.a.name), b = name(t.b.name); if (a && b) union(a, b); return }
    // (a write at every key of k parts at one: z = N²·n + N·k + v)
    if (t.op === '=' && t.a.op === 'var' && name(t.a.name)?.startsWith('M:')) { const mp = name(t.a.name)!.slice(2), ps = parts(t.b, name); if (ps) { arity.set(mp, ps.length); ps.forEach((q, i) => union(q, `${mp}:${i}`)) } }
    kids(t, y => walk(y, name))
  }
  const inputs = new Set(m.inputs), rule = (v: string) => (inputs.has(v) ? v : undefined)
  for (const [mp, w] of Object.entries(m.step.maps ?? {})) {
    if ('each' in w) walk(w.value, v => (v === w.each ? `M:${mp}` : rule(v)))
    else { walk({op: 'get', map: mp, key: w.key}, rule); walk(w.value, rule) }
  }
  for (const e of Object.values(m.step.state ?? {})) walk(e, rule)
  for (const c of Object.values(m.step.flags ?? {})) walk(c, rule)
  if (m.assume) walk(m.assume, rule)
  const lawName = (l: Law) => { const own = new Set([l.forall, ...(l.keys ?? [])]); return (v: string) => (own.has(v) ? `L:${l.name}:${v}` : undefined) }
  for (const l of laws) walk(l.holds, lawName(l))
  // (a map read at a composed key is no plain read where a write at every key reads it at its own key)
  for (const mp of composed) plainRead.delete(mp)
  // (a map of keys of k parts read at a write at every key's own key is no plain read)
  for (const mp of arity.keys()) plainRead.delete(mp)
  return {
    find,
    sortOf: (l: Law, v: string) => find(`L:${l.name}:${v}`),
    shape: (l: Law, bound: string[]) => {
      const own = new Set(bound), composites: [string, string][] = [], guards: C[] = []
      const see = (t: E | C): void => {
        if (t.op === 'get') { const sp = split(t.key, v => (own.has(v) ? v : undefined)); if (sp && !composites.some(([a, b]) => a === sp[0] && b === sp[1])) composites.push(sp) }
        kids(t, see)
      }
      see(l.holds)
      // (the antecedent's conditions on the keys, with the state and params beside: k < 64, a ≠ b, k < size, j < next)
      const onKeys = (c: C) => { const s2 = JSON.stringify(c), ns = [...s2.matchAll(/"name":"([^"]+)"/g)].map(q => q[1]!); return !s2.includes('"op":"get"') && ns.some(v => own.has(v)) && ns.every(v => own.has(v) || v in m.state || m.params.includes(v)) }
      if (l.holds.op === 'or') for (const y of l.holds.xs) if (y.op === 'not') guards.push(...conj(y.x).filter(onKeys))
      return {composites, guards}
    },
    // (a guard that reads the state or params beside the keys: a domain that moves)
    moving: (g: C, bound: string[]) => [...JSON.stringify(g).matchAll(/"name":"([^"]+)"/g)].some(q => !bound.includes(q[1]!)),
    composedMaps: [...composed], plainRead: [...plainRead], arity,
    // (a key of k parts at these key terms)
    composeAll: (ts: E[]): E => { const k = ts.reduce((acc: E, t) => plus(times(pairing!.n, acc), t)); return pairing!.c ? plus(k, n(pairing!.c)) : k },
    compose: (a: E, b: E): E => { const k = plus(times(pairing!.n, a), b); return pairing!.c ? plus(k, n(pairing!.c)) : k },
    plainMaps: (sort: string) => [...plainRead].filter(mp => find(`M:${mp}`) === sort),
    valuesAt: (st: State, sort: string): number[] => {
      const ks = new Set<number>()
      for (const [mp, cells] of Object.entries(st.maps)) for (const k of cells.keys()) {
        if (plainRead.has(mp) && find(`M:${mp}`) === sort) ks.add(k)
        if (composed.has(mp) && pairing?.n && k >= pairing.c) { if (find('hi') === sort) ks.add(Math.floor((k - pairing.c) / pairing.n)); if (find('lo') === sort) ks.add((k - pairing.c) % pairing.n) }
        const ar = arity.get(mp)
        if (ar && pairing?.n && k >= pairing.c) for (let i = ar - 1, r = k - pairing.c; i >= 0; i--, r = Math.floor(r / pairing.n)) if (find(`${mp}:${i}`) === sort) ks.add(i ? r % pairing.n : r)
      }
      const xs = [...ks].sort((a, b) => a - b)
      return [...xs, xs.length ? xs.at(-1)! + 1 : 0]
    },
  }
}

// The products of two of `names` a machine's terms (its step, flags, assumption) and these conditions multiply, a
// product of sums read as its monomials ((top + 2)·window: top·window), each pair of factors once, in order.
function monomialsOf(m: Machine, cs: C[], names: Set<string>): [string, string][] {
  const out = new Map<string, [string, string]>()
  const vars = (e: E, acc: Set<string>): Set<string> => {
    if (e.op === 'var') acc.add(e.name)
    else if (e.op === 'add' || e.op === 'sub' || e.op === 'min' || e.op === 'max') { vars(e.a, acc); vars(e.b, acc) } else if (e.op === 'mul') vars(e.a, acc)
    return acc
  }
  const visit = (t: unknown): void => {
    if (!t || typeof t !== 'object') return
    if (Array.isArray(t)) { t.forEach(visit); return }
    const o = t as {op?: string, a?: E, b?: E}
    if (o.op === 'prod' && o.a && o.b) for (const u of vars(o.a, new Set())) for (const w of vars(o.b, new Set())) if (names.has(u) && names.has(w)) { const p = [u, w].sort() as [string, string]; out.set(p.join('*'), p) }
    for (const val of Object.values(o)) if (typeof val === 'object') visit(val)
  }
  visit([m.state, m.step, m.assume, cs])
  return [...out.values()].slice(0, 8)
}

// The directions of the states a step breaks a law from (its preimage, made linear): each comparison a law makes, read
// after the step through each branch of the step's terms (an if's two sides, max's and min's each, a ∸ b as a − b, a
// map's written value or its old one), and a step law's as it reads; the request's values in it eliminated against the
// step's own comparisons (its flags, its assumption, its terms' conditions, the step laws' `when`), Fourier–Motzkin, one
// value at a time, twice at most; what reads the state and params alone (a cell at any key as the cell) is a direction.
// So "executes at t0 + now ≥ ReadyAt[id]" with "executes needs Ts[id] ≤ t0 + now" gives ReadyAt[k] − Ts[k], and "the
// timer drops a client with Reset ≤ now" with "a tick comes at now ≥ lastTick + windowMs" gives Reset[k] − lastTick −
// windowMs: what a bound must hold of for the step to keep the law, beside the rule's own comparisons.
function preimages(m: Machine, laws: Law[], stepLaws: StepLaw[], atoms: Atom[], coords: number[]): Rel[] {
  type Lin = Map<string, number>
  const cap = 256, inputs = new Set(m.inputs), maps = new Set(Object.keys(m.maps ?? {}))
  const termOf = new Map(atoms.flatMap(a => (a.term ? [[JSON.stringify(a.term), a.parts[0]![0]] as const] : [])))
  const plus = (a: Lin, b: Lin, k = 1): Lin => { const o = new Map(a); for (const [v, c] of b) o.set(v, (o.get(v) ?? 0) + k * c); return o }
  // (branches deduplicated, at most `cap` a term)
  const uniq = (ls: Lin[]): Lin[] => [...new Map(ls.map(l => [JSON.stringify([...l].filter(([, c]) => c).sort((p, q) => (p[0] < q[0] ? -1 : 1))), l])).values()].slice(0, cap)
  const cross = (xs: Lin[], ys: Lin[], k: number): Lin[] => uniq(xs.flatMap(a => ys.map(b => plus(a, b, k))))
  // (`post`: names read after the step, through its terms; a step law's primed names are so too)
  const linE = (e: E, post: boolean): Lin[] => {
    const t = termOf.size && e.op !== 'var' && e.op !== 'const' ? termOf.get(JSON.stringify(e)) : undefined
    if (t && !post) return [new Map([[t, 1]])]
    switch (e.op) {
      case 'const': return [new Map([['1', e.value]])]
      case 'var': {
        const primed = e.name.endsWith("'") ? e.name.slice(0, -1) : undefined
        if (primed !== undefined && primed in m.state) return linE(m.step.state?.[primed] ?? x(primed), false)
        if (post && e.name in m.state) return linE(m.step.state?.[e.name] ?? e, false)
        return [new Map([[e.name, 1]])]
      }
      case 'add': return cross(linE(e.a, post), linE(e.b, post), 1)
      case 'sub': return uniq([...cross(linE(e.a, post), linE(e.b, post), -1), new Map()])
      case 'mul': return linE(e.a, post).map(l => new Map([...l].map(([v, c]) => [v, c * e.k])))
      case 'min': case 'max': return uniq([...linE(e.a, post), ...linE(e.b, post)])
      case 'if': return uniq([...linE(e.then, post), ...linE(e.else, post)])
      case 'prod': return []
      case 'get': {
        const name = e.map.endsWith("'") && maps.has(e.map.slice(0, -1)) ? e.map.slice(0, -1) : e.map
        if (!maps.has(name)) return []
        const w = (post || name !== e.map) ? m.step.maps?.[name] : undefined
        // (the cell as it was first: a step writes few)
        if (w) return uniq([new Map([[name, 1]]), ...linE(w.value, false)])
        return [new Map([[name, 1]])]
      }
    }
  }
  const flags: Record<string, C> = {}
  // (a quantified flag as the goals read it, its 0/1 variable ?f: a flag after it may read it, 2PC's go1 reads noGo)
  for (const [f, c] of Object.entries(m.step.flags ?? {})) flags[f] = c.op === 'all' ? {op: '=', a: x(`?${f}`), b: n(1)} : substC(c, {vars: {}, maps: {}, flags})
  const inline = (c: C) => substC(c, {vars: {}, maps: {}, flags})
  const atomsOfC = (c: C, post: boolean, out: Lin[]): void => {
    if (c.op === 'and' || c.op === 'or') { c.xs.forEach(y => atomsOfC(y, post, out)); return }
    if (c.op === 'not') { atomsOfC(c.x, post, out); return }
    if (c.op !== '<' && c.op !== '<=' && c.op !== '=') return
    for (const a of linE(c.a, post)) for (const b of linE(c.b, post)) if (out.length < 1000) out.push(plus(a, b, -1))
  }
  const condsOfE = (e: E, out: Lin[]): void => {
    if (e.op === 'if') { atomsOfC(inline(e.c), false, out); condsOfE(e.then, out); condsOfE(e.else, out) }
    else if (e.op === 'add' || e.op === 'sub' || e.op === 'min' || e.op === 'max' || e.op === 'prod') { condsOfE(e.a, out); condsOfE(e.b, out) }
    else if (e.op === 'mul') condsOfE(e.a, out)
  }
  // (each law its own: its comparisons, their eliminations and its share of the directions, taken in turn)
  const sources: Lin[][] = [], guards: Lin[] = []
  for (const l of laws) { const b: Lin[] = []; atomsOfC(inline(l.holds), true, b); sources.push(b) }
  for (const sl of stepLaws) {
    const b: Lin[] = []
    atomsOfC(inline(sl.then), false, b); sources.push(b)
    for (const w of sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when]) atomsOfC(inline(w), false, guards)
  }
  Object.values(flags).forEach(c => atomsOfC(c, false, guards))
  if (m.assume) atomsOfC(inline(m.assume), false, guards)
  Object.values(m.step.state ?? {}).forEach(e => condsOfE(e, guards))
  const reads = (l: Lin) => [...l].filter(([v, c]) => c && inputs.has(v)).map(([v]) => v)
  const dir = (l: Lin): Rel | undefined => {
    const coef: [number, number][] = []
    for (const i of coords) {
      const a = atoms[i]!, [pos, neg] = a.parts, cp = l.get(pos![0]) ?? 0
      if (neg && (l.get(neg[0]) ?? 0) !== -cp) return undefined
      if (cp) coef.push([i, cp])
    }
    const rest = [...l].filter(([v, c]) => c && v !== '1' && !coef.some(([i]) => atoms[i]!.parts.some(([q]) => q === v)))
    if (rest.length || coef.length < 2) return undefined
    const g = coef.reduce((acc, [, cc]) => gcd(acc, cc), 0), t = coef.map(([i, cc]) => [i, cc / g] as [number, number])
    return {coef: t[0]![1] > 0 ? t : t.map(([i, cc]) => [i, -cc] as [number, number]), d: 0}
  }
  const per = sources.map(bad => {
    const found = new Map<string, Rel>()
    let front = bad
    for (let round = 0; round < 3 && front.length; round++) {
      const next: Lin[] = []
      for (const f of front) {
        const vs = reads(f)
        if (!vs.length) { const r = dir(f); if (r) found.set(JSON.stringify(r.coef), r); continue }
        if (round === 2) continue
        const v = vs[0]!
        for (const g of guards) {
          const gv = g.get(v) ?? 0, fv = f.get(v)!
          if (!gv || next.length > 2000) continue
          next.push(plus(new Map([...f].map(([k2, c]) => [k2, c * gv])), g, -fv))
        }
      }
      front = next
    }
    return [...found.values()]
  })
  const out = new Map<string, Rel>()
  for (let i = 0; per.some(l => i < l.length); i++) for (const l of per) if (i < l.length) out.set(JSON.stringify(l[i]!.coef), l[i]!)
  return [...out.values()]
}

// The linear comparisons a machine's conditions make over the state alone (its assumption, its step's conditions and the
// laws), over the atoms given (an integer atom's two parts with opposite coefficients), each as Σ t·v ≤ d beside its
// negation (an equality's two sides and theirs): the directions a bound of the join may take beside the atoms' own,
// and the literals of a cube at a point.
type Rel = {coef: [number, number][], d: number}
function comparisons(m: Machine, laws: Law[], atoms: Atom[], coords: number[], more: C[] = []): Rel[] {
  const termOf = new Map(atoms.flatMap(a => (a.term ? [[JSON.stringify(a.term), a.parts[0]![0]] as const] : []))), cellParts = new Set(atoms.flatMap(a => (a.cell ? a.parts.map(([q]) => q) : [])))
  const lin = (e: E, k: number, out: Map<string, number>): boolean => {
    const t = termOf.size && e.op !== 'var' && e.op !== 'const' ? termOf.get(JSON.stringify(e)) : undefined
    if (t) { out.set(t, (out.get(t) ?? 0) + k); return true }
    // (a map's cell at any key as the cell: a comparison over cells is one at a key)
    if (e.op === 'get' && cellParts.has(e.map)) { out.set(e.map, (out.get(e.map) ?? 0) + k); return true }
    if (e.op === 'const') { out.set('1', (out.get('1') ?? 0) + k * e.value); return true }
    if (e.op === 'var') { out.set(e.name, (out.get(e.name) ?? 0) + k); return true }
    if (e.op === 'add') return lin(e.a, k, out) && lin(e.b, k, out)
    return e.op === 'mul' && lin(e.a, k * e.k, out)
  }
  // A request's value that some step puts in a state variable as it is (a clause's head argument, say) stands for that
  // variable: a comparison over the request then reads as one over the state it makes.
  const inputTo = new Map<string, string>()
  const leaves = (e: E, to: string): void => { if (e.op === 'var') { if (m.inputs.includes(e.name) && !inputTo.has(e.name)) inputTo.set(e.name, to) } else if (e.op === 'if') { leaves(e.then, to); leaves(e.else, to) } }
  for (const [v, e] of Object.entries(m.step.state ?? {})) leaves(e.op === 'sub' ? e.a : e, v)
  // A request's value a step adds to a state variable (bn + db, the clock moved): beside that variable, with its
  // coefficient, the two read as the variable after the step, a value of the state.
  const incr = new Map<string, Set<string>>()
  const adds = (e: E, v: string): void => {
    if (e.op === 'if') { adds(e.then, v); adds(e.else, v); return }
    if (e.op !== 'add') return
    for (const [p, q] of [[e.a, e.b], [e.b, e.a]] as const) if (p.op === 'var' && p.name === v && q.op === 'var' && m.inputs.includes(q.name)) { if (!incr.has(q.name)) incr.set(q.name, new Set()); incr.get(q.name)!.add(v) }
  }
  if (env.GDP_JOIN_CLOCKS !== '0') for (const [v, e] of Object.entries(m.step.state ?? {})) adds(e, v)
  const found = new Map<string, Rel>()
  const visitE = (e: E): void => {
    if (e.op === 'if') { visitC(e.c); visitE(e.then); visitE(e.else) } else if (e.op === 'add' || e.op === 'sub' || e.op === 'min' || e.op === 'max' || e.op === 'prod') { visitE(e.a); visitE(e.b) } else if (e.op === 'mul') visitE(e.a)
  }
  const visitC = (c: C): void => {
    if (c.op === 'and' || c.op === 'or') { c.xs.forEach(visitC); return }
    if (c.op === 'not') { visitC(c.x); return }
    if (c.op !== '<' && c.op !== '<=' && c.op !== '=') return
    visitE(c.a); visitE(c.b)
    const l0 = new Map<string, number>()
    if (!lin(c.a, 1, l0) || !lin(c.b, -1, l0)) return
    for (const [u, vs] of incr) { const k = l0.get(u); if (k && [...vs].some(v => l0.get(v) === k)) l0.delete(u) }
    const l = new Map<string, number>()
    for (const [v, k] of l0) { const w = inputTo.get(v) ?? v; l.set(w, (l.get(w) ?? 0) + k) }
    const coef: [number, number][] = []
    for (const i of coords) {
      const a = atoms[i]!, [pos, neg] = a.parts, cp = l.get(pos![0]) ?? 0
      if (neg && (l.get(neg[0]) ?? 0) !== -cp) return
      if (cp) coef.push([i, cp])
      l.delete(pos![0]); if (neg) l.delete(neg[0])
    }
    const k0 = l.get('1') ?? 0
    l.delete('1')
    if ([...l.values()].some(v => v !== 0) || !coef.length) return
    const g = coef.reduce((acc, [, cc]) => gcd(acc, cc), 0), t = coef.map(([i, cc]) => [i, cc / g] as [number, number])
    const d = Math.floor((c.op === '<' ? -k0 - 1 : -k0) / g), u = t.map(([i, cc]) => [i, -cc] as [number, number])
    for (const r of [{coef: t, d}, {coef: u, d: -d - 1}, ...(c.op === '=' ? [{coef: u, d: -d}, {coef: t, d: d - 1}] : [])]) if (Number.isSafeInteger(r.d)) found.set(JSON.stringify(r), r)
  }
  if (m.assume) visitC(m.assume)
  Object.values(m.step.flags ?? {}).forEach(visitC)
  Object.values(m.step.state ?? {}).forEach(visitE)
  laws.forEach(l => visitC(l.holds))
  more.forEach(visitC)
  return [...found.values()]
}

export function inferLaws(target: AnyRule | Machine, laws: Law[], stepLaws: StepLaw[] = [], opts: InferOptions = {}): Inferred {
  return quietly(() => withDeadline(clock() + (opts.ms ?? 20000), () => inferLawsSearch(target, laws, stepLaws, opts)))
}
function inferLawsSearch(target: AnyRule | Machine, laws: Law[], stepLaws: StepLaw[] = [], opts: InferOptions = {}): Inferred {
  // (GDP_INFER_TRACE=2: each phase's progress too, to stderr)
  if (env.GDP_INFER_TRACE === '2' && !opts.progress) opts = {...opts, progress: (phase, info) => (globalThis as unknown as {process: {stderr: {write: (s: string) => void}}}).process.stderr.write(`[infer ${phase}] ${JSON.stringify(info)}\n`)}
  const t0 = performance.now(), ms = opts.ms ?? 20000, wallUntil = t0 + ms, rule = isRule(target) ? target.withSumsOf(laws, stepLaws) : undefined
  // The clock the budgets read (counted milliseconds since the start, or wall time where `timed`), and the stop.
  const timed = !!opts.timed, w0 = work.n, used = {tries: 0, rows: 0, evals: 0, watched: 0}
  const now = (): number => (timed ? performance.now() - t0
    : used.tries / inferRates.tries + used.rows / inferRates.rows + used.evals / inferRates.evals + used.watched / inferRates.watched + (work.n - w0) / inferRates.work)
  let stopped = false
  const stop = () => stopped || (stopped = performance.now() > wallUntil)
  const until = ms
  let tp = performance.now(), cp = 0, wp = w0
  const trace = (what: string, o: Record<string, number | string | boolean> = {}) => {
    if (!inferTrace) return
    const t = performance.now(), c = now()
    ;(globalThis as unknown as {process: {stderr: {write: (s: string) => void}}}).process.stderr.write(`[infer] ${what} ${JSON.stringify({ms: Math.round(t - tp), counted: Math.round(c - cp), work: work.n - wp, ...used, ...o})}\n`)
    tp = t; cp = c; wp = work.n
  }
  if (rule) { const ks = divisorsIn([...laws, ...stepLaws] as never); if (ks.size) rule.dividesBy(...ks) }
  const m = rule ? rule.machine : target as Machine
  let proofs = 0
  // The rule (or machine) the kernel proves the candidates with: once a remainder is among them, one that declares
  // div$k and mod$k for its divisors (rule.withDivisors leaves the caller's rule as it was until a found law needs them).
  // Only the laws proven read: a search none of whose chosen candidates is a remainder proves with the rule as it is.
  const byDivisors = new Map<string, {r?: AnyRule, m: Machine}>()
  const forLaws = (ls: Law[]): {r?: AnyRule, m: Machine} => {
    const ks = [...divisorsIn(ls.map(l => l.holds))].filter(k2 => !m.fns?.[modName(k2)]).sort((a, b) => a - b), key = ks.join(',')
    let out = byDivisors.get(key)
    if (!out) { const r2 = ks.length ? rule?.withDivisors(...ks) : rule; out = {r: r2, m: r2 ? r2.machine : withArithmetic(m, [], ks)}; byDivisors.set(key, out) }
    return out
  }
  // (`fast`: the set's proof asked again after a drop, kernel/prove.ts's proveSetFast: what was settled kept where it stands)
  const prove = (ls: Law[], fast = false): Verdict => {
    proofs++
    const {r: searchRule, m: mm} = forLaws(ls)
    if (searchRule) return stepLaws.length ? proveSteps(searchRule, ls, stepLaws, {search: false}) : proveRule(searchRule, ls, {search: false, fast})
    const out = stepLaws.length ? proveStepLaws(mm, ls, stepLaws) : (fast ? proveSetFast : proveLaws)(mm, ls)
    return verdictOf(out)
  }
  const stats = (samples: number, candidates: number, alive: number) => ({samples, candidates, alive, proofs, ms: Math.round(performance.now() - t0), stopped: stop()})
  const first = opts.first ?? prove(laws)
  if ((first.proven && first.checked) || first.run) return {...first, found: [], stats: stats(0, 0, 0)}

  // --- runs ------------------------------------------------------------------------------------------------------------
  const run = interpret(m), rand = seeded(17), kinds = rule ? rule.kindsOfState() : []
  const given = rule ? [...rule.kindLaws().filter(k => !laws.some(l => l.name === k.name)), ...laws] : laws
  const randomParams = (bound: number, r: Rand = rand): Env => (rule ? rule.randomParams(r, bound) : Object.fromEntries(m.params.map(p => [p, r(bound + 1)])))
  const randomInput = (params: Env, bound: number, r: Rand = rand): Request => (rule ? rule.randomInput(r, bound, params)
    : {...Object.fromEntries(m.inputs.map(i => [i, r(bound + 1)])), ...Object.fromEntries((m.inputMaps ?? []).map(i => [i, new Map<number, number>()]))})
  type Sample = {params: Env, st: State}
  const samples: Sample[] = [], cap = 3000
  const keep = (s: Sample) => { if (samples.length < cap) samples.push(s); else if (rand(4) === 0) samples[rand(cap)] = s }
  for (const st of opts.seen ?? []) if (!m.params.length) keep({params: {}, st})
  trace('start')
  const mapsText = (st: State) => JSON.stringify(Object.values(st.maps).map(c => [...c]))
  // Counted: `runs` requests tried at least, and on until the samples are full (a trial keeps its start at least, so as
  // many trials as they hold fill them), the trials at most `runs` or that many. Timed: `runsMs` of wall time.
  const runsTimed = timed || opts.runsMs !== undefined, runsUntil = Math.min(wallUntil, performance.now() + (opts.runsMs ?? 500)), least = opts.runs ?? Math.min(inferRuns, Math.max(2000, 4 * ms))
  const moreRuns = (trial: number) => (runsTimed ? performance.now() < runsUntil : trial < Math.max(cap, least) && (used.tries < least || samples.length < cap) && !stop())
  let trials = 0
  // (an assumption with "there exists", a value the request brings, may admit no request at a small bound, a multiple
  // of 5 but 0, say: a trial whose steps moved nothing doubles the bound at once)
  const skolems = m.inputs.some(i => i.startsWith('some$a'))
  for (let trial = 0, bound = 2, stuck = false; moreRuns(trial); trial++, bound = trial % 20 === 0 || stuck ? (bound >= 1024 ? 2 : bound * 2) : bound) {
    stuck = false; trials++
    const params = randomParams(bound)
    if (m.pre && !evalC(m.pre, params, {scalars: {}, maps: {}}, m)) continue
    let st: State
    try { st = run.init(params) } catch { continue }
    keep({params, st})
    let took = 0
    for (let d = 0, tries = 0; d < 40 && tries < 200; tries++) {
      used.tries++
      const input = randomInput(params, bound)
      let next: State
      try { if (!allowed(m, run, params, st, input)) continue; next = run.step(params, st, input) } catch { break }
      d++
      if (JSON.stringify(next.scalars) !== JSON.stringify(st.scalars) || mapsText(next) !== mapsText(st)) { keep({params, st: next}); took++ }
      st = next
    }
    stuck = skolems && took === 0
  }

  opts.progress?.('runs', {samples: samples.length, trials})
  trace('runs', {samples: samples.length, trials})

  // --- atoms and rows --------------------------------------------------------------------------------------------------
  const scalars = Object.keys(m.state), stateSet = new Set(scalars), mapNames = Object.keys(m.maps ?? {}), mapSet = new Set(mapNames)
  const atoms: Atom[] = []
  const add = (name: string, has: (p: string) => boolean, param: boolean, cell: boolean) => {
    if (name.endsWith('$neg') && has(name.slice(0, -4))) return
    const neg = `${name}$neg`, int = has(neg)
    atoms.push({name: cell ? `${name}[k]` : name, parts: int ? [[name, 1], [neg, -1]] : [[name, 1]], param, int, cell})
  }
  for (const name of scalars) add(name, p => stateSet.has(p), false, false)
  for (const name of m.params) add(name, p => m.params.includes(p), true, false)
  for (const name of mapNames) add(name, p => mapSet.has(p), false, true)
  // The terms the laws and the step laws read that aren't linear (max(attempts, 1), a ∸ b, a product, a function's
  // value, a choice of two), over the state and params alone: each a value of its own, read at every row, so that a form
  // bounds it as it bounds a variable (the law's own comparison, tightened where the samples say). The largest such
  // terms, not their parts.
  {
    const named = (n: string) => stateSet.has(n) || m.params.includes(n)
    const okE = (e: E): boolean => e.op === 'const' || (e.op === 'var' ? named(e.name) : e.op === 'mul' ? okE(e.a) : e.op === 'if' ? okC(e.c) && okE(e.then) && okE(e.else)
      : e.op === 'get' ? !!m.fns?.[e.map] && okE(e.key) : okE(e.a) && okE(e.b))
    const okC = (c: C): boolean => (c.op === 'and' || c.op === 'or' ? c.xs.every(okC) : c.op === 'not' ? okC(c.x) : c.op === '<' || c.op === '<=' || c.op === '=' ? okE(c.a) && okE(c.b) : false)
    const seenT = new Set<string>()
    const visitE = (e: E): void => {
      if (e.op === 'var' || e.op === 'const') return
      if (e.op !== 'add' && e.op !== 'mul' && okE(e)) { const k = JSON.stringify(e); if (!seenT.has(k)) { seenT.add(k); atoms.push({name: showE(e), parts: [[`$t${seenT.size - 1}`, 1]], param: false, int: false, cell: false, term: e}) } return }
      if (e.op === 'mul') visitE(e.a); else if (e.op === 'if') { visitC(e.c); visitE(e.then); visitE(e.else) } else if (e.op === 'get') visitE(e.key); else { visitE(e.a); visitE(e.b) }
    }
    const visitC = (c: C): void => { if (c.op === 'and' || c.op === 'or') c.xs.forEach(visitC); else if (c.op === 'not') visitC(c.x); else if (c.op === '<' || c.op === '<=' || c.op === '=') { visitE(c.a); visitE(c.b) } }
    const lawConds = [...laws.map(l => l.holds), ...stepLaws.flatMap(sl => [sl.then, ...(sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when])])]
    for (const c of lawConds) if (!c.op.startsWith('all')) visitC(c)
    // and a product of two naturals the rule, its laws or its step laws multiply (u·w of the state and the params, a
    // monomial as the kernel's arithmetic reads it: (top + 2)·window's top·window), its value its factors' product; a
    // bound over it is linear for the kernel, which multiplies the factors' rows where a goal needs the product's facts
    for (const [u, w] of monomialsOf(m, lawConds, new Set([...scalars, ...m.params].filter(p => !stateSet.has(`${p}$neg`) && !m.params.includes(`${p}$neg`))))) {
      const e: E = {op: 'prod', a: x(u), b: x(w)}, k = JSON.stringify(e)
      if (!seenT.has(k)) { seenT.add(k); atoms.push({name: `${u}·${w}`, parts: [[`$t${seenT.size - 1}`, 1]], param: false, int: false, cell: false, term: e}) }
    }
  }
  const termAtoms = atoms.filter(a => a.term)
  // a row's term atoms' values, at its state (a term whose value the interpreter can't take: 0)
  const withTerms = (env: Env, st: State): Env => {
    if (!termAtoms.length) return env
    for (const a of termAtoms) { try { env[a.parts[0]![0]] = evalE(a.term!, env, st, m) } catch { env[a.parts[0]![0]] = 0 } }
    return env
  }
  const A = atoms.length, cellAtoms = atoms.flatMap((a, i) => (a.cell ? [i] : []))
  const valueOf = (a: Atom, env: Env) => { let s = 0; for (const [p, sign] of a.parts) s += sign * (env[a.cell ? AT + p : p] ?? 0); return s }
  // The pairs' rows (the join's, where the rule composes two keys into one), once the pair atoms are made.
  const views: View[] = []
  const cellOf = (st: State, map: string, key: number) => st.maps[map]?.get(key) ?? st.defaults?.[map] ?? m.maps![map]!
  // The scalar rows (one per state reached), and the cell rows (one per state and key a map holds, and one fresh key).
  const keysIn = (st: State) => { const ks = new Set<number>(); for (const c of Object.values(st.maps)) for (const k of c.keys()) ks.add(k); return [...ks] }
  // A state read from a kernel model names some cells (`named`, map|key); the others it leaves free (any value), so a form
  // is judged there only at rows whose cells it reads the model names (`unnamed`: a row's cells it doesn't), and no
  // fresh key. Elsewhere every cell is the state's.
  const named = new WeakMap<State, Set<string>>(), unnamed = new WeakMap<Env, Set<string>>()
  const mark = (row: Env, st: State, cells: [string, string, number][]) => { const nm = named.get(st); if (nm) { const u = new Set(cells.filter(([, mp, k]) => !nm.has(`${mp}|${k}`)).map(([q]) => q)); if (u.size) unnamed.set(row, u) } return row }
  const cellRows = (params: Env, st: State): Env[] => {
    if (!mapNames.length) return []
    const ks = keysIn(st), fresh = ks.length ? Math.max(...ks) + 1 : 0
    return [...ks, ...(named.has(st) ? [] : [fresh])].map(k => mark(withTerms({...params, ...st.scalars, [K]: k, ...Object.fromEntries(mapNames.map(mp => [AT + mp, cellOf(st, mp, k)]))}, st), st, mapNames.map(mp => [AT + mp, mp, k])))
  }
  const rowsS = samples.map(s => withTerms({...s.params, ...s.st.scalars}, s.st))
  const rowsK: Env[] = []
  for (const s of samples) { if (rowsK.length > 6000) break; rowsK.push(...cellRows(s.params, s.st)) }
  const valsS = atoms.map(a => Float64Array.from(rowsS, r => valueOf(a, r))), valsK = atoms.map(a => Float64Array.from(rowsK, r => valueOf(a, r)))
  const kindOf = new Map(kinds.map(([name, k]) => [name, k]))
  // Modes: a yes/no, a choice, or a state natural (or cell) no run took past a few values.
  type Mode = {atom: number, values: number[], choice?: readonly string[], bool?: boolean}
  const modes: Mode[] = []
  atoms.forEach((a, i) => {
    if (a.param || a.int || a.term) return
    const k = a.cell ? undefined : kindOf.get(a.name), seenValues = [...new Set(a.cell ? valsK[i]! : valsS[i]!)].sort((p, q) => p - q)
    const decoded = k?.vars(a.name).length === 1 ? k.decode(a.name, {[a.name]: 0}) : undefined
    const values = (k as unknown as {values?: readonly string[]} | undefined)?.values
    if (typeof decoded === 'boolean') modes.push({atom: i, values: [0, 1], bool: true})
    else if (typeof decoded === 'string' && values) modes.push({atom: i, values: values.map((_, j) => j), choice: values})
    else if (!k && seenValues.length && seenValues.length <= 4 && seenValues.every(v => v <= 8)) modes.push({atom: i, values: seenValues})
  })
  const modeOf = (i: number) => modes.find(mo => mo.atom === i)

  // --- candidates ----------------------------------------------------------------------------------------------------
  const consts = [...new Set([...constantsOf(m, laws), ...(opts.constants ?? [])].map(Math.abs))].filter(k => k > 0).sort((p, q) => p - q)
  const mags = [...new Set([1, 2, 3, ...consts.filter(k => k > 3 && k <= 1000).slice(0, 4)])]
  const bounds = [...new Set([...consts, ...consts.flatMap(a => consts.map(b => a * b)), ...consts.flatMap(a => consts.map(b => a + b))].flatMap(k => [k, -k])), 0].sort((p, q) => p - q)
  const maxCandidates = opts.maxCandidates ?? 60000
  // The shapes: every coefficient vector over up to three atoms, coprime; a scalar form reads a state variable, a
  // cell form a cell (and at most one scalar).
  const shapes: {coef: [number, number][], cells: boolean}[] = []
  const pick = (terms: number, ms: number[], pool: number[], ok: (acc: [number, number][]) => boolean, cells: boolean) => {
    const cs = ms.flatMap(k => [k, -k])
    const go = (from: number, acc: [number, number][]) => {
      if (shapes.length > maxCandidates) return
      if (acc.length === terms) { if (ok(acc) && acc.reduce((g, [, c]) => gcd(g, c), 0) === 1) shapes.push({coef: [...acc], cells}); return }
      for (let i = from; i < pool.length; i++) for (const c of cs) go(i + 1, [...acc, [pool[i]!, c]])
    }
    go(0, [])
  }
  const choose = (k: number, of: number) => { let r = 1; for (let i = 0; i < k; i++) r = r * (of - i) / (i + 1); return r }
  // A choice's index orders its values arbitrarily: it is a guard, or alone (a bound on it reads as the values it
  // allows), never a term among others.
  const plain = atoms.flatMap((a, i) => (a.cell ? [] : [i])), terms = plain.filter(i => !modeOf(i)?.choice), P = terms.length
  const scalarOk = (acc: [number, number][]) => acc.some(([i]) => !atoms[i]!.param)
  pick(1, [1], plain, scalarOk, false)
  pick(2, choose(2, P) * 4 * mags.length ** 2 <= maxCandidates / 4 ? mags : [1], terms, scalarOk, false)
  if (choose(3, P) * 8 * mags.length ** 3 <= maxCandidates / 2) pick(3, mags, terms, scalarOk, false)
  else if (choose(3, P) * 8 <= maxCandidates / 2) pick(3, [1], terms, scalarOk, false)
  // (a map at a composed key and a map at a plain one read at one key are of two sorts: Leader[k] against
  // VoteRequestMsg[k], a pair relation's raw key, is no law of the rule's)
  const pairMaps = new Set(pairingOf(m)?.n ? keySorts(m, laws, pairingOf(m)).composedMaps : []), pairOf = (i: number) => pairMaps.has(atoms[i]!.parts[0]![0])
  const sortedCells = (acc: [number, number][]) => { const cs = acc.filter(([i]) => atoms[i]!.cell); return cs.every(([i]) => pairOf(i)) || cs.every(([i]) => !pairOf(i)) }
  if (cellAtoms.length) {
    const all = atoms.flatMap((_, i) => (modeOf(i)?.choice ? [] : [i])), cellOk = (acc: [number, number][]) => acc.some(([i]) => atoms[i]!.cell) && acc.filter(([i]) => !atoms[i]!.cell).length <= 1 && sortedCells(acc)
    pick(1, [1], cellAtoms, () => true, true)
    pick(2, [1], all, cellOk, true)
    if (choose(3, A) * 8 <= maxCandidates / 4) pick(3, [1], all, acc => cellOk(acc) && acc.filter(([i]) => atoms[i]!.cell).length >= 2, true)
  }
  const sizeOf = (coef: [number, number][]) => coef.length * 100 + coef.reduce((s, [, c]) => s + Math.abs(c), 0)
  const forms: Form[] = []
  const NS = rowsS.length, NK = rowsK.length
  const at = (coef: [number, number][], vals: Float64Array[], j: number) => { let s = 0; for (const [i, c] of coef) s += c * vals[i]![j]!; return s }
  const keyNots = plain.filter(i => !atoms[i]!.param && !atoms[i]!.int && !atoms[i]!.term)
  // The guards: the choices first, then yes/nos, then small naturals, at most eight; each shape's largest value per
  // guard in one pass over (at most 1,500 of) the rows. Building candidates takes at most a quarter of the time.
  const guards = [...modes].sort((p, q) => Number(!!q.choice) - Number(!!p.choice) || Number(!!q.bool) - Number(!!p.bool)).slice(0, 8)
  const strideS = Math.max(1, Math.ceil(NS / 1500)), strideK = Math.max(1, Math.ceil(NK / 1500))
  const buildUntil = Math.min(until, now() + (until - now()) / 4)
  for (const [n_, {coef, cells}] of shapes.entries()) {
    if (forms.length > maxCandidates || (n_ % 256 === 0 && (now() > buildUntil || stop()))) break
    const vals = cells ? valsK : valsS, N = cells ? NK : NS, rows = cells ? rowsK : rowsS
    used.rows += N + (coef.length > 2 ? 0 : Math.ceil(N / (cells ? strideK : strideS)))
    let d = -Infinity
    for (let j = 0; j < N; j++) d = Math.max(d, at(coef, vals, j))
    if (!Number.isFinite(d)) continue
    forms.push({coef, d, cells, size: sizeOf(coef) + (cells ? 10 : 0)})
    // The rule's constants just above the largest value reached, a bound a run may not have hit.
    for (const b of bounds.filter(b => b > d).slice(0, 2)) forms.push({coef, d: b, cells, size: sizeOf(coef) + 1 + (cells ? 10 : 0)})
    if (coef.length > 2) continue
    const here = guards.filter(mode => !coef.some(([i]) => i === mode.atom) && (cells ? !atoms[mode.atom]!.cell || sortedCells([...coef, [mode.atom, 1]]) : !atoms[mode.atom]!.cell))
    const most = here.map(() => new Map<number, number>()), away = cells ? keyNots.map(() => -Infinity) : []
    for (let j = 0; j < N; j += cells ? strideK : strideS) {
      const value = at(coef, vals, j)
      here.forEach((mode, g) => { const v = vals[mode.atom]![j]!, b = most[g]!; b.set(v, Math.max(b.get(v) ?? -Infinity, value)) })
      // At every key but a scalar's: the largest value away from that key.
      if (cells) keyNots.forEach((s, g) => { if (rows[j]![K] !== valsK[s]![j]) away[g] = Math.max(away[g]!, value) })
    }
    here.forEach((mode, g) => { for (const [value, dv] of most[g]!) if (mode.values.includes(value) && dv < d) forms.push({coef, d: dv, cells, guard: {atom: mode.atom, value}, size: sizeOf(coef) + 50}) })
    keyNots.forEach((s, g) => { if (cells && Number.isFinite(away[g]!) && away[g]! < d) forms.push({coef, d: away[g]!, cells, guard: {keyNot: s}, size: sizeOf(coef) + 60}) })
  }
  for (const mode of modes) if (!atoms[mode.atom]!.cell) for (const value of mode.values) if (NS && !valsS[mode.atom]!.includes(value)) forms.push({coef: [], d: 0, cells: false, unreachable: {atom: mode.atom, value}, size: 1})
  // Remainders: a value, or the sum or difference of two, at one remainder by k in every run (or in every run where a
  // guard holds), k each divisor the rule and its laws read (modBy, divBy) and 2: x mod 2 = 0 for a counter that steps
  // by 2, the parity of a sum that two counters keep. No form above states one (no linear bound does).
  // The moduli: the divisors the rule and its laws read, then 2, 3, 4 and the rule's own constants up to 64 (six in all).
  const divisors = [...new Set([...[...divisorsIn([...machineTerms(m), ...laws.map(l => l.holds)])].filter(k => k >= 2 && k <= 1_000_000).sort((p, q) => p - q), 2, 3, 4, ...consts.filter(k => k > 4 && k <= 64)])].slice(0, 6)
  const modAtoms = terms.filter(i => !atoms[i]!.param && !modeOf(i)?.bool && !atoms[i]!.term), modShapes: [number, number][][] = modAtoms.map(i => [[i, 1]])
  if (modAtoms.length * (modAtoms.length - 1) <= 2000) for (const [a, i] of modAtoms.entries()) for (const j of modAtoms.slice(a + 1)) modShapes.push([[i, 1], [j, 1]], [[i, 1], [j, -1]])
  const residue = (v: number, k: number) => ((v % k) + k) % k
  // A shape whose runs reached two values or fewer is a bound's (above), not a remainder's.
  const varied = (coef: [number, number][]) => { const vs = new Set<number>(); for (let j = 0; j < NS && vs.size < 3; j += strideS) { used.rows++; vs.add(at(coef, valsS, j)) } return vs.size >= 3 }
  for (const coef of NS && opts.remainders !== false ? modShapes.filter(varied) : []) for (const k of divisors) {
    if (forms.length > maxCandidates || now() > buildUntil || stop()) break
    const all = new Set<number>(), byGuard = guards.map(() => new Map<number, Set<number>>())
    used.rows += Math.ceil(NS / strideS)
    for (let j = 0; j < NS; j += strideS) {
      const r = residue(at(coef, valsS, j), k)
      all.add(r)
      guards.forEach((mode, g) => { const v = valsS[mode.atom]![j]!, b = byGuard[g]!; if (!b.has(v)) b.set(v, new Set()); b.get(v)!.add(r) })
    }
    const size = sizeOf(coef) + 30 + k
    if (all.size === 1) { forms.push({coef, d: 0, cells: false, mod: {k, r: [...all][0]!}, size}); continue }
    guards.forEach((mode, g) => { if (coef.some(([i]) => i === mode.atom)) return; for (const [value, rs] of byGuard[g]!) if (rs.size === 1 && mode.values.includes(value)) forms.push({coef, d: 0, cells: false, guard: {atom: mode.atom, value}, mod: {k, r: [...rs][0]!}, size: size + 50}) })
  }
  // Congruences, where remainders are off: a state value (or the sum or difference of two) whose every sample leaves
  // one remainder by a constant of the rule's (2 first), with at least three values reached: ∃k. v = c·k + r. The
  // remainder above says the same without a quantifier, so the kernel proves it as it stands (no witness to choose),
  // under a guard where only some runs keep it, and Lean states it with %: that is the form tried by default.
  if (opts.remainders === false && opts.existentials !== false && NS) {
    const mods = [...new Set([2, 3, 4, ...consts.filter(k => k > 4 && k <= 64)])].slice(0, 6)
    const congOf = (coef: [number, number][]) => {
      const vs = new Set<number>()
      used.rows += NS
      for (let j = 0; j < NS; j++) vs.add(at(coef, valsS, j))
      if (vs.size < 3) return
      const nat = coef.every(([i, c]) => !atoms[i]!.int && c > 0), list = [...vs]
      for (const c of mods) {
        const r = ((list[0]! % c) + c) % c
        if (list.every(x => ((x % c) + c) % c === r) && (!nat || list.every(x => x >= r))) forms.push({coef, d: 0, cells: false, cong: {mod: c, rest: r}, size: sizeOf(coef) + 40 + c})
      }
    }
    const st = plain.filter(i => !atoms[i]!.param && !modeOf(i))
    for (const i of st) congOf([[i, 1]])
    if (st.length <= 24) for (const [a, i] of st.entries()) for (const j of st.slice(a + 1)) { congOf([[i, 1], [j, 1]]); congOf([[i, 1], [j, -1]]) }
  }
  opts.progress?.('candidates', {atoms: A, shapes: shapes.length, forms: forms.length})
  trace('candidates', {forms: forms.length})

  // --- how a form reads, and as a law ------------------------------------------------------------------------------------
  const nameOf = (i: number) => atoms[i]!.name
  const shownValue = (i: number, value: number) => { const mo = modeOf(i); return mo?.choice ? (mo.choice[value] ?? String(value)) : mo?.bool ? (value === 1 ? 'yes' : 'no') : String(value) }
  const sides = (f: Form) => {
    const term = ([i, c]: [number, number]) => `${Math.abs(c) === 1 ? '' : `${Math.abs(c)}·`}${nameOf(i)}`
    const left = f.coef.filter(([, c]) => c > 0), right = f.coef.filter(([, c]) => c < 0)
    return {left, right, l: [...left.map(term), ...(f.d < 0 ? [String(-f.d)] : [])].join(' + ') || '0', r: [...right.map(term), ...(f.d > 0 ? [String(f.d)] : [])].join(' + ') || '0'}
  }
  // A bound on a choice alone reads as the values it allows.
  const allowedValues = (f: Form) => {
    const only = f.coef.length === 1 ? modeOf(f.coef[0]![0]) : undefined
    if (!only?.choice) return undefined
    const c = f.coef[0]![1]
    return only.values.filter(v => c * v <= f.d)
  }
  // (a form about every key says so first)
  const viewText = (v: View, t: string) => v.vars.reduce((acc, k2, i) => acc.replaceAll(k2, v.names[i]!), t)
  const textOf = (f: Form): string => {
    if (f.cells) return `every k: ${textIn(f)}`
    if (f.view === undefined) return textIn(f)
    const v = views[f.view]!
    return `every ${v.names.join(', ')}${v.frame.op === 'and' && !v.frame.xs.length ? '' : ` with ${viewText(v, showC(v.frame))}`}: ${textIn(f)}`
  }
  const textIn = (f: Form): string => {
    const atText = (g: At) => (g.hi === undefined ? `${nameOf(g.atom)} is ${shownValue(g.atom, g.value)}` : g.hi === Infinity ? `${g.value} <= ${nameOf(g.atom)}` : `${nameOf(g.atom)} in ${g.value}..${g.hi}`)
    if (f.never) return `never ${f.never.map(atText).join(' and ')}`
    if (f.nevers) return `never ${f.nevers.map(c => c.map(atText).join(' and ')).join('; nor ')}`
    if (f.cube) return `never ${f.cube.map(l => ('at' in l ? atText(l.at) : (({l: a, r: b}) => `${a} <= ${b}`)(sides({coef: l.lin.coef, d: l.lin.d, cells: false, size: 0})))).join(' and ')}`
    if (f.also) return `${f.also.map(atText).join(' and ')} → ${textIn({...f, also: undefined})}`
    if (f.unreachable) return f.unreachable.hi === undefined ? `${nameOf(f.unreachable.atom)} is never ${shownValue(f.unreachable.atom, f.unreachable.value)}` : `never ${atText(f.unreachable)}`
    if (f.cong) return `∃k. ${f.coef.map(([i, c], j) => `${j ? (c > 0 ? ' + ' : ' − ') : c < 0 ? '−' : ''}${nameOf(i)}`).join('')} = ${f.cong.mod}·k${f.cong.rest ? ` + ${f.cong.rest}` : ''}`
    const {l, r} = sides(f), within = allowedValues(f)
    const body = f.mod ? `${f.coef.map(([i, c], j) => `${c < 0 ? (j ? ' − ' : '−') : j ? ' + ' : ''}${nameOf(i)}`).join('')} mod ${f.mod.k} = ${f.mod.r}` : within ? `${nameOf(f.coef[0]![0])} is ${within.map(v => shownValue(f.coef[0]![0], v)).join(' or ')}` : `${l} <= ${r}`
    const under = f.when ? (({l: wl, r: wr}) => `${wl} <= ${wr} → `)(sides({coef: f.when.coef, d: f.when.d, cells: false, size: 0})) : ''
    const guarded = !f.guard ? under + body : 'keyNot' in f.guard ? `k = ${nameOf(f.guard.keyNot)} or ${body}` : `${atText(f.guard)} → ${under}${body}`
    return guarded
  }
  const sum = (es: E[]): E => es.reduce((p, q) => plus(p, q), n(0))
  // Each congruence its own witness's name (each may be a ghost of the machine).
  const someNames = new Map<Form, string>(), someName = (f: Form) => { let k = someNames.get(f); if (!k) someNames.set(f, (k = `${SOME}${someNames.size}`)); return k }
  const part = (a: Atom, p: string): E => (a.term ?? (a.place !== undefined ? get(p.slice(2, p.lastIndexOf(AT)), views[a.view!]!.places[a.place]!) : a.cell ? get(p, x(KEY)) : x(p)))
  const partsOf = (f: Form, sign: 1 | -1): E[] => f.coef.flatMap(([i, c]) => atoms[i]!.parts.filter(([, s]) => s * c * sign > 0).map(([p]) => { const e = part(atoms[i]!, p); return Math.abs(c) === 1 ? e : times(Math.abs(c), e) }))
  // Σ c·v ≤ d over naturals: the positive parts on the left, the negative ones and d on the right (an integer's
  // negative part goes to the other side of its sign).
  const condOf = (f: Form): C => {
    // Not at a value, one-sided where it can be (less splitting for the kernel): a natural not 0 is at least 1, and a
    // yes/no or a choice not at its last value is below it (its kind's law bounds it).
    const notAt = (i: number, value: number, hi?: number): C => {
      const e = part(atoms[i]!, atoms[i]!.parts[0]![0]), mo = modeOf(i), lastValue = mo?.bool ? 1 : mo?.choice ? mo.choice.length - 1 : undefined
      // (a level: below its first value, or past its last)
      if (hi !== undefined) return any(...(value > 0 ? [atMost(e, n(value - 1))] : []), ...(hi < Infinity ? [atMost(n(hi + 1), e)] : []))
      return value === 0 ? atMost(n(1), e) : value === lastValue ? atMost(e, n(value - 1)) : not(same(e, n(value)))
    }
    if (f.never) return any(...f.never.map(g => notAt(g.atom, g.value, g.hi)))
    if (f.nevers) return all(...f.nevers.map(c => any(...c.map(g => notAt(g.atom, g.value, g.hi)))))
    if (f.cube) return not(all(...f.cube.map(l => ('at' in l ? same(part(atoms[l.at.atom]!, atoms[l.at.atom]!.parts[0]![0]), n(l.at.value)) : condOf({coef: l.lin.coef, d: l.lin.d, cells: false, size: 0})))))
    if (f.also) return any(...f.also.map(g => notAt(g.atom, g.value, g.hi)), condOf({...f, also: undefined}))
    if (f.unreachable) return notAt(f.unreachable.atom, f.unreachable.value, f.unreachable.hi)
    if (f.mod) {
      // Σ c·v = P − N over naturals (P the positive parts, N the negative ones), whose remainder by k is that of the
      // natural P + (k − 1)·N.
      const {k: dk, r} = f.mod, neg = partsOf(f, -1), e = get(modName(dk), sum([...partsOf(f, 1), ...neg.map(t => times(dk - 1, t))]))
      const body = same(e, n(r))
      return !f.guard ? body : 'keyNot' in f.guard ? any(same(x(KEY), x(atoms[f.guard.keyNot]!.parts[0]![0])), body) : any(notAt(f.guard.atom, f.guard.value, f.guard.hi), body)
    }
    // Σ = c·k + r, k = SOME (an integer's two parts where Σ reads an integer or a difference): the negative parts and
    // c·k's negative part on the other side.
    if (f.cong) {
      const k = someName(f), intK = f.coef.some(([i, c]) => atoms[i]!.int || c < 0), ck = times(f.cong.mod, x(k)), ckNeg = times(f.cong.mod, x(`${k}$neg`))
      return same(sum([...partsOf(f, 1), ...(intK ? [ckNeg] : [])]), sum([...partsOf(f, -1), ck, ...(f.cong.rest ? [n(f.cong.rest)] : [])]))
    }
    const lhs = sum([...partsOf(f, 1), ...(f.d < 0 ? [n(-f.d)] : [])]), rhs = sum([...partsOf(f, -1), ...(f.d > 0 ? [n(f.d)] : [])])
    // Under a condition Σ ≤ d: its negation, −Σ ≤ −d − 1, or the body.
    const body = f.when ? any(condOf({coef: f.when.coef.map(([i, c]) => [i, -c]), d: -f.when.d - 1, cells: false, size: 0}), atMost(lhs, rhs)) : atMost(lhs, rhs)
    return !f.guard ? body : 'keyNot' in f.guard ? any(same(x(KEY), x(atoms[f.guard.keyNot]!.parts[0]![0])), body) : any(notAt(f.guard.atom, f.guard.value, f.guard.hi), body)
  }
  // A view's frame as builder code (its keys by their names; comparisons of a name with a name or a constant), and the
  // state and params it reads.
  const frameSource = (v: View): {binder: string, src: string, reads: string[]} | undefined => {
    const ren = new Map(v.vars.map((k2, i) => [k2, v.names[i]!])), reads: string[] = []
    const name = (t: E) => (t.op !== 'var' ? undefined : ren.get(t.name) ?? (reads.push(t.name), t.name))
    const c = (t: C): string | undefined => {
      if (t.op === 'not') { const y = c(t.x); return y && `${y}.not()` }
      if (t.op === 'and') { const xs = t.xs.map(c); return xs.length && xs.every(Boolean) ? xs.slice(1).reduce((a, b) => `${a}.and(${b})`, xs[0]!) : undefined }
      if (t.op !== '<' && t.op !== '<=' && t.op !== '=') return undefined
      const a = name(t.a), b = t.b.op === 'const' ? String(t.b.value) : name(t.b)
      return a && b ? `${a}.${t.op === '<' ? 'lt' : t.op === '<=' ? 'atMost' : 'eq'}(${b})` : undefined
    }
    const src = c(v.frame)
    return src ? {binder: v.names.length === 1 ? v.names[0]! : `(${v.names.join(', ')})`, src, reads} : undefined
  }
  // The builder call, for a rule whose atoms are its own variables (naturals, or integers alone).
  const sourceOf = (f: Form, text: string): string | undefined => {
    if (!rule || f.when || f.mod || f.also || f.never || f.nevers || f.cube || [...f.coef.map(([i]) => i), ...(f.guard && 'atom' in f.guard ? [f.guard.atom] : [])].some(i => atoms[i]!.term)) return undefined
    const used = [...new Set([...f.coef.map(([i]) => i), ...(f.guard ? ['keyNot' in f.guard ? f.guard.keyNot : f.guard.atom] : []), ...(f.unreachable ? [f.unreachable.atom] : [])])]
    const ints = f.coef.filter(([i]) => atoms[i]!.int).length
    if (ints && ints !== f.coef.length) return undefined
    // (a view's cell: its map at x or at y, a view of one or two plain keys whose frame compares names and constants)
    const fr = f.view !== undefined ? frameSource(views[f.view]!) : undefined
    if (f.view !== undefined && (!views[f.view]!.printable || !fr)) return undefined
    const mapOf = (i: number) => { const a = atoms[i]!, p = a.parts[0]![0]; return a.place !== undefined ? p.slice(2, p.lastIndexOf(AT)) : p }
    const ref = (i: number) => (atoms[i]!.place !== undefined ? `${mapOf(i)}.at(${atoms[i]!.place === 0 ? 'x' : 'y'})` : atoms[i]!.cell ? `${atoms[i]!.parts[0]![0]}.at(k)` : nameOf(i))
    // (a cell of a map of yes/nos, at k or at x or y, reads as its 0/1 term too)
    const boolCell = (i: number) => (atoms[i]!.cell || atoms[i]!.place !== undefined) && rule.kindsOfCells().some(([mp, kd]) => mp === mapOf(i) && kd === bool)
    const val = (i: number) => { const mo = modeOf(i); return mo?.choice && !atoms[i]!.cell ? `${ref(i)}.index` : (mo?.bool && !atoms[i]!.cell) || boolCell(i) ? `${ref(i)}.n` : ref(i) }
    // (a yes/no, a cell of yes/nos too, as itself or its negation; a level of any value by its number)
    const cond = (i: number, value: number, hi?: number) => {
      const mo = modeOf(i), v = val(i)
      if (hi !== undefined) return hi === Infinity ? `${v}.atLeast(${value})` : `${v}.atLeast(${value}).and(${v}.atMost(${hi}))`
      return mo?.choice && !atoms[i]!.cell ? `${ref(i)}.is('${mo.choice[value]}')` : (mo?.bool && !atoms[i]!.cell) || boolCell(i) ? (value === 1 ? ref(i) : `${ref(i)}.not()`) : `${v}.eq(${value})`
    }
    const args = `({${[...new Set([...used.map(i => (atoms[i]!.cell || atoms[i]!.place !== undefined ? mapOf(i) : nameOf(i))), ...(fr?.reads ?? [])])].join(', ')}})`
    const wrap = (body: string) => (f.cells ? `forall(k => ${body})` : fr ? `forall(${fr.binder} => ${fr.src}.implies(${body}))` : body)
    if (f.unreachable) return `r.law('${text}', ${args} => ${cond(f.unreachable.atom, f.unreachable.value, f.unreachable.hi)}.not())`
    if (f.cong) {
      if (f.coef.length !== 1 || f.coef[0]![1] !== 1) return undefined
      const intK = atoms[f.coef[0]![0]]!.int
      return `r.law('${text}', ${args} => exists(${intK ? 'int, ' : ''}k => ${val(f.coef[0]![0])}.eq(k.times(${f.cong.mod})${f.cong.rest ? `.plus(${f.cong.rest})` : ''})))`
    }
    const term = (ts: [number, number][], k: number) => {
      const parts = ts.map(([i, c]) => (Math.abs(c) === 1 ? val(i) : `${val(i)}.times(${Math.abs(c)})`))
      if (!parts.length) return String(k)
      return parts.slice(1).reduce((acc, p) => `${acc}.plus(${p})`, parts[0]!) + (k > 0 ? `.plus(${k})` : '')
    }
    const {left, right} = sides(f)
    const body = left.length ? `${term(left, Math.max(0, -f.d))}.atMost(${term(right, Math.max(0, f.d))})` : `${term(right, Math.max(0, f.d))}.atLeast(${Math.max(0, -f.d)})`
    const guarded = !f.guard ? body : 'keyNot' in f.guard ? `k.eq(${nameOf(f.guard.keyNot)}).or(${body})` : `${cond(f.guard.atom, f.guard.value, f.guard.hi)}.implies(${body})`
    return `r.law('${text}', ${args} => ${wrap(guarded)})`
  }

  // --- evaluating a form ---------------------------------------------------------------------------------------------
  // (each row's atom values read once, however many forms are evaluated there: rows are never changed once made)
  const valuesAt = new WeakMap<Env, Float64Array>()
  const valuesOf = (env: Env): Float64Array => {
    let vs = valuesAt.get(env)
    if (!vs) { const n2 = atoms.length; vs = new Float64Array(n2); for (let i = 0; i < n2; i++) vs[i] = valueOf(atoms[i]!, env); valuesAt.set(env, vs) }
    return vs
  }
  const holdsRow = (f: Form, env: Env): boolean => {
    used.evals++
    const vs = valuesOf(env)
    if (f.never) return f.never.some(g => off(g, vs[g.atom]!))
    if (f.nevers) return f.nevers.every(c => c.some(g => off(g, vs[g.atom]!)))
    if (f.cube) return !f.cube.every(l => ('at' in l ? vs[l.at.atom] === l.at.value : l.lin.coef.reduce((acc, [i, c]) => acc + c * vs[i]!, 0) <= l.lin.d))
    if (f.also?.some(g => off(g, vs[g.atom]!))) return true
    if (f.unreachable) return off(f.unreachable, vs[f.unreachable.atom]!)
    if (f.cong) {
      let v = 0
      for (const [i, c] of f.coef) v += c * vs[i]!
      const nat = f.coef.every(([i, c]) => !atoms[i]!.int && c > 0)
      return ((v - f.cong.rest) % f.cong.mod + f.cong.mod) % f.cong.mod === 0 && (!nat || v >= f.cong.rest)
    }
    if (f.guard) {
      if ('keyNot' in f.guard) { if (env[K] === vs[f.guard.keyNot]) return true }
      else if (off(f.guard, vs[f.guard.atom]!)) return true
    }
    if (f.when) { let w = 0; for (const [i, c] of f.when.coef) w += c * vs[i]!; if (w > f.when.d) return true }
    let s = 0
    for (const [i, c] of f.coef) s += c * vs[i]!
    return f.mod ? residue(s, f.mod.k) === f.mod.r : s <= f.d
  }
  // At a state: a cell form at every key the maps hold and a fresh one.
  type Point = {scalar: Env, cells: Env[], views: Env[][]}
  const pointOf = (params: Env, st: State): Point => ({scalar: withTerms({...params, ...st.scalars}, st), cells: cellRows(params, st), views: views.map(v => v.rowsOf(params, st))})
  // (the atoms a form reads)
  const atomsIn = (f: Form): number[] => [...f.coef.map(([i]) => i), ...(f.guard && 'atom' in f.guard ? [f.guard.atom] : []), ...(f.also ?? []).map(a => a.atom), ...(f.never ?? []).map(a => a.atom), ...(f.unreachable ? [f.unreachable.atom] : []), ...(f.nevers ?? []).flat().map(a => a.atom), ...(f.cube ?? []).flatMap(l => ('at' in l ? [l.at.atom] : l.lin.coef.map(([i]) => i)))]
  const judged = (f: Form, r: Env) => { const u = unnamed.get(r); return !u || !atomsIn(f).some(i => atoms[i]!.parts.some(([q]) => u.has(atoms[i]!.cell ? AT + q : q))) }
  const holdsAt = (f: Form, p: Point) => (f.view !== undefined ? (p.views[f.view] ?? []).every(r => !judged(f, r) || holdsRow(f, r)) : f.cells ? p.cells.every(r => !judged(f, r) || holdsRow(f, r)) : holdsRow(f, p.scalar))
  // A kernel witness as a point: its scalars, and a cell row per key it reads a map at.
  const witnessPoint = (w: Record<string, number>): Point => {
    const scalar: Env = Object.fromEntries([...scalars, ...m.params].map(v => [v, w[v] ?? 0]))
    withTerms(scalar, {scalars: scalar, maps: {}})
    const byKey = new Map<number, Env>(), named: Record<string, number> = {...Object.fromEntries([...scalars, ...m.params, ...m.inputs].map(v => [v, 0])), ...w}
    for (const [name, value] of Object.entries(w)) {
      const br = name.indexOf('[')
      if (br < 0 || !name.endsWith(']') || !mapSet.has(name.slice(0, br))) continue
      const key = keyValue(name, named)
      if (key === undefined) continue
      const row = byKey.get(key) ?? {...scalar, [K]: key}
      row[AT + name.slice(0, br)] = value
      byKey.set(key, row)
    }
    return {scalar, cells: [...byKey.values()], views: []}
  }
  // A kernel witness's map cells, each at the key it names (the others at the map's constant).
  const mapsOf = (w: Record<string, number>): State['maps'] => {
    const out: State['maps'] = Object.fromEntries(mapNames.map(mp => [mp, new Map<number, number>()]))
    // (a name the model leaves out is 0, as the state's and the request's are read)
    const named: Record<string, number> = {...Object.fromEntries([...scalars, ...m.params, ...m.inputs].map(v => [v, 0])), ...w}
    for (const [name, value] of Object.entries(w)) {
      const br = name.indexOf('[')
      if (br < 0 || !name.endsWith(']') || !mapSet.has(name.slice(0, br))) continue
      const key = keyValue(name, named)
      if (key !== undefined) out[name.slice(0, br)]!.set(key, value)
    }
    return out
  }

  // A kernel witness's function values (a function the kernel knows by its facts alone: the model's own), the steps and
  // the views reading them where it names them and the interpreter's elsewhere, within f.
  const withFnsOf = <T>(w: Record<string, number>, f: () => T): T => {
    const fns = m.fns, saved: [string, Fn][] = [], named: Record<string, number> = {...Object.fromEntries([...scalars, ...m.params, ...m.inputs].map(v => [v, 0])), ...w}
    for (const [name, fn] of Object.entries(fns ?? {})) {
      if (fn.call || fn.recur) continue
      const table: Record<number, number> = {}
      for (const [c, v] of Object.entries(w)) if (c.startsWith(`${name}[`) && c.endsWith(']')) { const key = keyValue(c, named); if (key !== undefined) table[key] = v }
      if (Object.keys(table).length) { saved.push([name, fn]); fns![name] = {...fn, js: `(k) => (${JSON.stringify(table)})[k] ?? (${fn.js})(k)`} }
    }
    try { return f() } finally { for (const [name, fn] of saved) fns![name] = fn }
  }
  // A kernel witness's request: its inputs, and each map it carries at the cells the model names (a quorum).
  const requestOf = (w: Record<string, number>): Request => {
    const out: Request = Object.fromEntries(m.inputs.map(i => [i, w[i] ?? 0])), named: Record<string, number> = {...Object.fromEntries([...scalars, ...m.params, ...m.inputs].map(v => [v, 0])), ...w}
    for (const q of m.inputMaps ?? []) {
      const cells = new Map<number, number>()
      for (const [name, value] of Object.entries(w)) if (name.startsWith(`${q}[`) && name.endsWith(']')) { const key = keyValue(name, named); if (key !== undefined) cells.set(key, value) }
      out[q] = cells
    }
    return out
  }

  // --- Houdini on the runs' neighbors ----------------------------------------------------------------------------------
  let alive = forms.slice().sort((p, q) => p.size - q.size).slice(0, maxCandidates)
  const ctis: Point[] = []
  // (a law about keys is evaluated at every tuple of the state's keys, as watch does: counted as that many evaluations)
  const lawful = (params: Env, st: State) => {
    used.watched += given.length
    const k = keysOf(4, st).length
    for (const l of given) if (l.forall) used.evals += k ** (1 + (l.keys?.length ?? 0))
    try { return given.every(l => watch(m, run, l, params, 4).start(st)) } catch { return false }
  }
  const houdiniUntil = Math.min(until, now() + Math.max(500, (until - now()) / 4))
  for (let quiet = 0; samples.length && now() < houdiniUntil && !stop() && quiet < 3;) {
    const killed = new Set<Form>()
    for (let tries = 0; tries < 400 && now() < houdiniUntil && !stop(); tries++) {
      const base = samples[rand(samples.length)]!, scal = {...base.st.scalars}, maps = {...base.st.maps}
      for (let k = 0, moves = 1 + rand(2); k < moves; k++) {
        if (mapNames.length && rand(2) === 0) {
          const mp = mapNames[rand(mapNames.length)]!, ks = keysIn(base.st), key = ks.length && rand(3) ? ks[rand(ks.length)]! : rand(5)
          const cells = new Map(maps[mp] ?? []); cells.set(key, Math.max(0, cellOf(base.st, mp, key) + (rand(7) - 3))); maps[mp] = cells
        } else if (scalars.length) { const v = scalars[rand(scalars.length)]!; scal[v] = Math.max(0, scal[v]! + (rand(7) - 3)) }
      }
      const st: State = {...base.st, scalars: scal, maps}, pre = pointOf(base.params, st)
      if (!alive.every(f => killed.has(f) || holdsAt(f, pre)) || !lawful(base.params, st)) continue
      const input = randomInput(base.params, 4)
      let next: State
      try { if (!allowed(m, run, base.params, st, input)) continue; next = run.step(base.params, st, input) } catch { continue }
      const post = pointOf(base.params, next)
      let broke = false
      for (const f of alive) if (!killed.has(f) && !holdsAt(f, post)) { killed.add(f); broke = true }
      if (!broke && !lawful(base.params, next)) ctis.push(pre)
    }
    quiet = killed.size ? 0 : quiet + 1
    alive = alive.filter(f => !killed.has(f))
  }

  opts.progress?.('houdini', {alive: alive.length, ctis: ctis.length})
  trace('houdini', {alive: alive.length})

  // --- the kernel ----------------------------------------------------------------------------------------------------
  const lawOf = new Map<Form, Law>()
  const someOf = (f: Form): string[] => (!f.cong ? [] : f.coef.some(([i, c]) => atoms[i]!.int || c < 0) ? [someName(f), `${someName(f)}$neg`] : [someName(f)])
  const lawFor = (f: Form) => {
    let l = lawOf.get(f)
    // (about two keys: where the frame holds of them)
    const v = f.view !== undefined ? views[f.view]! : undefined
    if (!l) lawOf.set(f, (l = {name: textOf(f), holds: v ? any(not(v.frame), condOf(f)) : condOf(f), ...(f.cells ? {forall: KEY} : v ? {forall: v.vars[0]!, keys: v.vars.slice(1)} : {}), ...(f.cong ? {some: someOf(f)} : {})}))
    return l
  }
  const names = new Set(given.map(l => l.name))
  alive = alive.filter(f => !names.has(textOf(f)))
  let pool = alive.slice(), chosen: Form[] = []
  // (the enumeration's set, proven where the join found nothing: the answer, the search below not run)
  let enumProof: Verdict | undefined
  // (the ∃ law the engine's set proved with, its ghost's: reported in `found` with the cubes, so the verdict's laws prove
  // again as they are, and export to Lean)
  let enumSome: Law[] = []
  const goalName = (g: string) => g.replace(/ @[^@]*$/, '')
  let last: Verdict = first
  const slow = Math.max(3000, ms / 10)
  // A point a form is false at; a cell form is judged only at rows that read every map it reads.
  const reads = (f: Form, r: Env) => f.coef.every(([i]) => !atoms[i]!.cell || atoms[i]!.parts.every(([q]) => AT + q in r))
  const falseAt = (f: Form, p: Point) => (f.cells ? p.cells.some(r => reads(f, r) && !holdsRow(f, r)) : !holdsRow(f, p.scalar))
  // (a remainder or a congruence only where no bound of the candidates rules the point out, before the counterexample's own forms:
  // false at half the states a run doesn't reach, it would otherwise be chosen first everywhere)
  const best = (p: Point, congs = false) => {
    let pickF: Form | undefined, score = -Infinity
    for (const f of pool) {
      if (chosen.includes(f) || !!(f.cong || f.mod) !== congs || !falseAt(f, p)) continue
      const s = ctis.reduce((k, c) => k + (falseAt(f, c) ? 1 : 0), 0) * 1000 - f.size
      if (s > score) (pickF = f, score = s)
    }
    return pickF
  }
  // A counterexample to induction no candidate rules out: forms false at it that every sample meets under a condition
  // it meets too (one value, or a sum or difference of two, at most a threshold: 0, ±1, or its own value there), the
  // choice (loc, say) at its value there as the guard. A condition no sample meets gives its negation instead. Only the
  // eight values most unusual at it are read (furthest past the samples in its guard, then the rarest there).
  const choiceMode = modes.find(mo => mo.choice && !atoms[mo.atom]!.cell)
  const condAtoms = plain.filter(i => !atoms[i]!.param && i !== choiceMode?.atom)
  const fromCti = (p: Point): Form[] => {
    const end = Math.min(until, now() + Math.max(300, (until - now()) / 8))
    const sc = p.scalar, pv = (coef: [number, number][]) => { let v = 0; for (const [i, c] of coef) v += c * valueOf(atoms[i]!, sc); return v }
    const gv = choiceMode ? valueOf(atoms[choiceMode.atom]!, sc) : undefined
    const inGuard: number[] = []
    for (let j = 0; j < NS; j++) if (gv === undefined || valsS[choiceMode!.atom]![j] === gv) inGuard.push(j)
    const unusual = (i: number) => {
      const v = valueOf(atoms[i]!, sc)
      let lo = Infinity, hi = -Infinity, same = 0
      for (const j of inGuard) { const w = valsS[i]![j]!; if (w < lo) lo = w; if (w > hi) hi = w; if (w === v) same++ }
      return [Math.max(0, lo - v, v - hi), -same] as const
    }
    const focus = condAtoms.map(i => ({i, u: unusual(i)})).sort((a, b) => b.u[0] - a.u[0] || b.u[1] - a.u[1]).slice(0, 8).map(x => x.i)
    // Over the focus: one or two values with the magnitudes, three with ±1.
    const bodies: {coef: [number, number][]}[] = []
    const signed = (ks: number[]) => ks.flatMap(k => [k, -k])
    for (const [a, i] of focus.entries()) {
      bodies.push({coef: [[i, 1]]}, {coef: [[i, -1]]})
      for (const [b2, k] of focus.slice(a + 1).entries()) {
        for (const c1 of signed(mags)) for (const c2 of signed(mags)) if (gcd(c1, c2) === 1) bodies.push({coef: [[i, c1], [k, c2]]})
        for (const q of focus.slice(a + b2 + 2)) for (const c1 of [1, -1]) for (const c2 of [1, -1]) for (const c3 of [1, -1]) bodies.push({coef: [[i, c1], [k, c2], [q, c3]]})
      }
    }
    const conds: [number, number][][] = []
    for (const [a, i] of focus.entries()) {
      conds.push([[i, 1]], [[i, -1]])
      for (const k of focus.slice(a + 1)) conds.push([[i, 1], [k, -1]], [[i, -1], [k, 1]], [[i, 1], [k, 1]])
    }
    const out: Form[] = [], guard = choiceMode ? {atom: choiceMode.atom, value: gv!} : undefined
    for (const coef of conds) {
      const here = pv(coef)
      for (const d of [...new Set([here, 0, 1, -1])].filter(d => here <= d)) {
        if (now() > end || stop()) break
        const rows: number[] = []
        used.rows += inGuard.length
        for (const j of inGuard) if (at(coef, valsS, j) <= d) rows.push(j)
        const when = {coef, d}, base = sizeOf(coef) + 80
        if (!rows.length) { out.push({coef: coef.map(([i, c]) => [i, -c]), d: -d - 1, cells: false, ...(guard ? {guard} : {}), size: base}); continue }
        const stride = Math.max(1, Math.ceil(rows.length / 600))
        for (const [q, sh] of bodies.entries()) {
          if (q % 256 === 0 && (now() > end || stop())) break
          const v = pv(sh.coef)
          used.rows += Math.ceil(rows.length / stride)
          let most = -Infinity, ok = true
          for (let t = 0; t < rows.length; t += stride) { const w = at(sh.coef, valsS, rows[t]!); if (w >= v) { ok = false; break } if (w > most) most = w }
          if (ok && Number.isFinite(most)) out.push({coef: sh.coef, d: most, cells: false, ...(guard ? {guard} : {}), when, size: base + sizeOf(sh.coef)})
        }
      }
    }
    // A stride may skip a sample that breaks a form: each is checked again at every sample in its guard.
    return out.sort((x, y) => x.size - y.size).slice(0, 2000).filter(f => inGuard.every(j => holdsRow(f, rowsS[j]!))).slice(0, 400)
  }

  // --- the join: an inductive invariant from the samples' hull (experiment: GDP_JOIN=1) -------------------------------------
  // Per value of the choice (loc), the affine hull of the samples there (its equalities, exact) and the largest value of
  // each direction (each value up and down, and pairs of them where there are few); the kernel's counterexample to the
  // induction of them all, replayed, is a state they allow whose successor they don't: it is joined in (the hull grows to
  // hold it, a bound rises to the next of the rule's constants, past three rises a bound is dropped), and so are the
  // states short walks from it reach, until the kernel proves them inductive. The caller's laws are then proven with
  // them assumed, and what their proofs read (and what those read, in turn) is the answer.
  const pool0 = pool.slice(), ctis0 = ctis.length
  if (joinOn && NS) try {
    const jT0 = performance.now(), jUntil = Math.min(until, now() + (until - now()) * (opts.join ?? joinShare))
    // The control state: the choice (loc) and, where they are few, the yes/nos (a program counter in bits), each of its
    // values reached a part of its own.
    const jChoice = modes.find(mo => mo.choice && !atoms[mo.atom]!.cell), bits = modes.filter(mo => mo.bool && !atoms[mo.atom]!.cell && !atoms[mo.atom]!.param)
    const locsReached = jChoice ? new Set(valsS[jChoice.atom]!).size : 1
    const keyModes = [...(jChoice ? [jChoice] : []), ...(bits.length && bits.length <= joinBits && locsReached * 2 ** bits.length <= joinKeys ? bits : [])]
    // Beside them, on demand (`refine`, below), the levels the rule's own comparisons with a constant cut a value into
    // (Ts ≤ 1 or past it, inflight 0 or more, a yes/no param): a value's level is a control value as a choice's is, the
    // value itself still a coordinate. The conditions read: the assumption, the step's terms and flags, the laws and the
    // step laws; a cut the runs' values all fall on one side of splits no samples and is left out.
    type Ctl = {atom: number, cuts: number[], top: number}
    const stepConds = stepLaws.flatMap(sl => [sl.then, ...(sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when])])
    const read = new Set([...laws.map(l => l.holds), ...stepConds].flatMap(c => [...JSON.stringify(c).matchAll(/"name":"([^"]+)"/g)].map(q => q[1]!)))
    const levelsOf = (cand: number[], vals: Float64Array[]): Ctl[] => {
      const cutsOf = new Map<number, Set<number>>()
      for (const {coef, d} of comparisons(m, laws, atoms, cand, stepConds)) {
        if (coef.length !== 1) continue
        const [i, c] = coef[0]!, t = c > 0 ? Math.floor(d / c) : Math.ceil(-d / -c) - 1
        if (t >= 0 && Number.isSafeInteger(t)) { if (!cutsOf.has(i)) cutsOf.set(i, new Set()); cutsOf.get(i)!.add(t) }
      }
      const name = (i: number) => (atoms[i]!.cell ? atoms[i]!.parts[0]![0] : atoms[i]!.name)
      const order = [...cutsOf.keys()].sort((a, b) => Number(read.has(name(b))) - Number(read.has(name(a))) || cutsOf.get(a)!.size - cutsOf.get(b)!.size)
      return (env.GDP_JOIN_LEVELS === '0' ? [] : order).flatMap(i => {
        const vs = vals[i]!, cuts = [...cutsOf.get(i)!].filter(t => vs.some(v => v <= t) && vs.some(v => v > t)).sort((a, b) => a - b)
        return cuts.length ? [{atom: i, cuts, top: Infinity}] : []
      })
    }
    const levelOf = (c: Ctl, v: number) => { let k = 0; while (k < c.cuts.length && c.cuts[k]! < v) k++; return k }
    const atOf = (c: Ctl, level: number): At => {
      const lo = level === 0 ? 0 : c.cuts[level - 1]! + 1, hi = level === c.cuts.length ? c.top : c.cuts[level]!
      return lo === hi ? {atom: c.atom, value: lo} : {atom: c.atom, value: lo, hi}
    }
    // The pairs: where the rule composes two keys into one (Link[N·a + b] beside Known[a], Known[b]), the cells at two
    // keys x and y and at N·x + y, a row per two keys a state holds (or the parts of a composed key it holds, or a fresh
    // one) that the frame (the assumption's of a and b) allows: their forms laws at every two keys.
    // Where no key is composed but a caller's law is about several keys (two counted approvals by distinct reviewers, two
    // holders of one lock), the same space over two distinct keys x ≠ y: the cells at x and at y (`n` 0, no third place).
    const pairing = mapNames.length ? pairingOf(m) ?? ([...laws, ...stepLaws].some(l => l.keys?.length) ? {n: 0, c: 0, frame: not(same(x(KEY), x(KEY2)))} : undefined) : undefined
    const cellLevels = pairing ? levelsOf(cellAtoms.filter(i => !atoms[i]!.int), valsK) : []
    // A view's atoms (each map at each place it is read at there) and rows: each assignment of its keys to keys a state
    // holds (by sort: the keys of the maps read at the key's place, the parts of composed keys there, and a fresh one;
    // per key at most `per`), the frame met, each map's cell at each of its places.
    // The join's rows of a space of keys (the cells, a view): rows alike but for their keys once, up to 6,000. The hull
    // and the levels read only which rows there are, so the cap holds as many of the samples' kinds of rows as it can.
    const distinctRows = (rowsOf: (params: Env, st: State) => Env[]): Env[] => {
      const rows: Env[] = [], seen = new Set<string>(), fresh = (r: Env) => { let t = ''; for (const q in r) if (q !== K) t += `${r[q]},`; return !seen.has(t) && !!seen.add(t) }
      for (const s2 of samples) { if (rows.length > 6000) break; rows.push(...rowsOf(s2.params, s2.st).filter(fresh)) }
      return rows
    }
    const addView = (v: Omit<View, 'atoms' | 'rows' | 'rowsOf'>, mapsAt: string[][], valuesOf2: (st: State) => number[][], per: number, extra: {name: string, term: E}[] = [], product = false) => {
      const vi = views.length, va: number[] = []
      // (`extra`: values of its keys that are atoms too, a key or a function of one: e ≤ Ep[a], idn(x) < idn(y))
      extra.forEach((t, j) => { va.push(atoms.length); atoms.push({name: t.name, parts: [[`$x${vi}:${j}`, 1]], param: false, int: false, cell: false, term: t.term, view: vi}) })
      mapsAt.forEach((mps, place) => {
        for (const i of cellAtoms) {
          const a = atoms[i]!
          if (!mps.includes(a.parts[0]![0])) continue
          va.push(atoms.length)
          atoms.push({name: `${a.parts[0]![0]}[${viewText(v as View, showE(v.places[place]!))}]`, parts: a.parts.map(([q, sg]) => [`${AT}${AT}${q}${AT}${vi}:${place}`, sg] as [string, 1 | -1]), param: false, int: a.int, cell: false, place, view: vi})
        }
      })
      const rowsOf = (params: Env, st: State, full = false): Env[] => {
        // (`per` values a key; the engine's views (`product`) at most per^keys rows a state, 64 at least, the fewer-valued
        // sorts' keys taking all of theirs and the cut on the most-valued: a sort's values past a few are still read where
        // another sort has few; a model's state, every row up to 1024, so that its diagram is read at the keys it names)
        const all2 = valuesOf2(st).map(vs => (named.has(st) ? vs.slice(0, -1) : vs)), lens = all2.map(vs => (product ? vs.length : Math.min(per, vs.length))), most = !product || full ? Infinity : named.has(st) ? 1024 : Math.max(64, per ** all2.length)
        for (let size = lens.reduce((a, b) => a * b, 1); size > most;) { const i = lens.indexOf(Math.max(...lens)); if (lens[i]! <= 1) break; size = size / lens[i]! * (lens[i]! - 1); lens[i]!-- }
        const cand = all2.map((vs, i) => vs.slice(0, lens[i])), out: Env[] = []
        const go = (i: number, env: Env): void => {
          if (i === v.vars.length) {
            try { if (!evalC(v.frame, env, st, m)) return } catch { return }
            const row: Env = {...params, ...st.scalars, [K]: env[v.vars[0]!]!, ...Object.fromEntries(extra.map((t, j) => { try { return [`$x${vi}:${j}`, evalE(t.term, env, st, m)] } catch { return [`$x${vi}:${j}`, 0] } }))}, cells: [string, string, number][] = []
            mapsAt.forEach((mps, place) => { const key = evalE(v.places[place]!, env, st, m); for (const mp of mps) { const q = `${AT}${AT}${mp}${AT}${vi}:${place}`; row[q] = cellOf(st, mp, key); cells.push([q, mp, key]) } })
            out.push(mark(withTerms(row, st), st, cells))
            return
          }
          for (const k2 of cand[i]!) go(i + 1, {...env, [v.vars[i]!]: k2})
        }
        go(0, {...params, ...st.scalars})
        return out
      }
      views.push({...v, atoms: va, rows: distinctRows(rowsOf), rowsOf})
    }
    // The pairs: where the rule composes two keys into one (Link[N·a + b] beside Known[a], Known[b]), the cells at two
    // keys x and y and at N·x + y, a row per two keys a state holds (or the parts of a composed key it holds, or a fresh
    // one) that the frame (the assumption's of a and b) allows: their forms laws at every two keys.
    // Where no key is composed but a caller's law is about several keys (two counted approvals by distinct reviewers, two
    // holders of one lock), the same space over two distinct keys x ≠ y: the cells at x and at y (`n` 0, no third place).
    const callerLaws = [...laws, ...stepLaws.map(sl => ({name: sl.name, holds: sl.then, ...(sl.forall ? {forall: sl.forall} : {}), ...(sl.keys ? {keys: sl.keys} : {})}) as Law)]
    const sorts = mapNames.length ? keySorts(m, callerLaws, pairing) : undefined
    if (pairing) {
      const P = pairing, composed = plus(times(P.n, x(KEY)), x(KEY2)), places = P.n ? [x(KEY), x(KEY2), P.c ? plus(composed, n(P.c)) : composed] : [x(KEY), x(KEY2)]
      // (by sort, where the rule composes: a row's maps at x, a column's at y, the composed maps at the composed key)
      const sorted = P.n && sorts ? [sorts.plainMaps(sorts.find('hi')), sorts.plainMaps(sorts.find('lo')), sorts.composedMaps] : undefined
      const held = (st: State) => {
        const ks = new Set<number>()
        for (const c of Object.values(st.maps)) for (const k of c.keys()) { ks.add(k); if (P.n && k >= P.c) { ks.add(Math.floor((k - P.c) / P.n)); ks.add((k - P.c) % P.n) } }
        const xs = [...ks, ks.size ? Math.max(...ks) + 1 : 0]
        return [xs, xs]
      }
      addView({vars: [KEY, KEY2], names: ['x', 'y'], places, covers: P.n ? [[0], [1], [0, 1]] : [[0], [1]], frame: P.frame, need: P.n ? 1 : 2, printable: !P.n}, sorted ?? places.map(() => mapNames), held, 24)
    }
    // A view of each caller's law about several keys that the pairs don't hold (three keys: two holders of a lock and
    // the lock; two keys of one sort where the pairs relate two sorts): its keys, each of the sort its reads give it
    // (keySorts: a sort is the places a key is read at, the rule's keys read alike as one), its places the composed keys
    // its reads name and each map read at a plain key of a key's sort, its frame its own guards on its keys and the keys
    // of one sort distinct.
    if (sorts) {
      const seen = new Set<string>()
      for (const l of callerLaws) {
        const bound = l.forall ? [l.forall, ...(l.keys ?? [])] : []
        if (!bound.length || bound.length > 4) continue
        const shape = sorts.shape(l, bound)
        if (!shape) continue
        const reads = (g: C) => bound.filter(b2 => JSON.stringify(g).includes(`"name":"${b2}"`)), moving = shape.guards.some((g: C) => sorts.moving(g, bound))
        // A key's domain that moves (its guards that read no other key but the state or params: k < size, j < next): a
        // view of that key alone, the cells of its sort at it where the domain holds (the cells' space reads every key a
        // state holds, a map written at every key holding its value past the domain too).
        for (const b2 of bound) {
          const dom = shape.guards.filter((g: C) => reads(g).length === 1 && reads(g)[0] === b2 && sorts.moving(g, bound)), mps = sorts.plainMaps(sorts.sortOf(l, b2))
          if (!dom.length || !mps.length) continue
          const frame = all(...dom.map((g: C) => substC(g, {vars: {[b2]: x(KEY)}, maps: {}, flags: {}}))), sig = JSON.stringify([sorts.sortOf(l, b2), frame])
          if (seen.has(sig)) continue
          seen.add(sig)
          addView({vars: [KEY], names: ['x'], places: [x(KEY)], covers: [[0]], frame, need: 1, printable: true}, [mps], st => [sorts.valuesAt(st, sorts.sortOf(l, b2))], 64)
        }
        // (two keys the pairs already relate: a row and a column of the composed key, or two plain keys where no domain
        // of the law's moves)
        if (bound.length < 2 || (bound.length === 2 && pairing && ((!pairing.n && !moving) || (shape.composites.length === 1 && sorts.sortOf(l, bound[0]!) !== sorts.sortOf(l, bound[1]!))))) continue
        const vars = bound.map((_, i) => (i ? `key${i + 1}$found` : KEY)), ren = Object.fromEntries(bound.map((b2, i) => [b2, x(vars[i]!)]))
        const places: E[] = [], mapsAt: string[][] = [], covers: number[][] = []
        for (const [a2, b2] of shape.composites) { places.push(sorts.compose(ren[a2]!, ren[b2]!)); mapsAt.push(sorts.composedMaps); covers.push([bound.indexOf(a2), bound.indexOf(b2)]) }
        bound.forEach((b2, i) => { const mps = sorts.plainMaps(sorts.sortOf(l, b2)); if (mps.length) { places.push(x(vars[i]!)); mapsAt.push(mps); covers.push([i]) } })
        const distinct = bound.flatMap((b2, i) => bound.slice(i + 1).flatMap((c2, j) => (sorts.sortOf(l, b2) === sorts.sortOf(l, c2) ? [not(same(x(vars[i]!), x(vars[i + 1 + j]!)))] : [])))
        const frame = all(...shape.guards.map((g: C) => substC(g, {vars: ren, maps: {}, flags: {}})), ...distinct)
        const sig = JSON.stringify([bound.map(b2 => sorts.sortOf(l, b2)), covers, mapsAt, frame])
        if (seen.has(sig) || !places.length) continue
        seen.add(sig)
        const per = Math.max(2, Math.floor(64 ** (1 / bound.length)))
        // (printed where its places are its two keys, x and y)
        const printable = bound.length === 2 && places.length === 2 && places.every((p2, i) => p2.op === 'var' && p2.name === vars[i])
        addView({vars, names: ['x', 'y', 'z', 'w'].slice(0, bound.length), places, covers, frame, need: bound.length, printable}, mapsAt,
          st => bound.map(b2 => sorts.valuesAt(st, sorts.sortOf(l, b2))), per)
      }
    }
    // The directions over some values: each value up and down, pairs of them where there are few, the rule's own
    // comparisons over the state (a guard, the query's condition) and the laws' preimages, each both ways.
    const directions = (cs: number[]): [number, number][][] => {
      const out: [number, number][][] = []
      for (const i of cs) out.push([[i, 1]], [[i, -1]])
      if (cs.length <= joinPairs) for (const [a2, i] of cs.entries()) for (const j of cs.slice(a2 + 1)) for (const [c1, c2] of [[1, 1], [1, -1], [-1, 1], [-1, -1]] as const) out.push([[i, c1], [j, c2]])
      const known = new Set(out.map(t => JSON.stringify(t))), pre = preimages(m, laws, stepLaws, atoms, cs)
      for (const {coef} of [...comparisons(m, laws, atoms, cs), ...pre]) if (coef.length > 1) for (const u of coef[0]![1] > 0 ? [coef, coef.map(([i, c]) => [i, -c] as [number, number])] : []) {
        const k2 = JSON.stringify(u)
        if (!known.has(k2) && out.length < 2 * cs.length + 4 * joinPairs * joinPairs + 64) { known.add(k2); out.push(u) }
      }
      return out
    }
    // Widening with thresholds: a bound a counterexample breaks rises to the next of the rule's constants (their sums and
    // products the first time, the constants alone after), and past that it is dropped.
    const fine = bounds, coarse = [...new Set([0, ...consts.flatMap(k => [k, -k])])].sort((p2, q2) => p2 - q2)
    type Group = {eqs: bigint[][], hi: number[], raised: number[]}
    const normal = (e: bigint[]) => { let g2 = 0n; for (const x2 of e) g2 = bgcd(g2, x2); if (g2 > 1n) for (let k = 0; k < e.length; k++) e[k]! /= g2; const lead = e.find(x2 => x2 !== 0n); if (lead !== undefined && lead < 0n) for (let k = 0; k < e.length; k++) e[k] = -e[k]!; return e }
    const dirValue = (t: [number, number][], vs: Float64Array | number[]) => { let v = 0; for (const [i, c] of t) v += c * vs[i]!; return v }
    let joins = 0, neversBroken = 0
    // A space of the join: the states (one row each, the scalars), or, for a rule with maps, the cells at a key (a row per
    // key a state's maps hold and a fresh one: the scalars and that key's cells), its control state, its coordinates
    // and directions, and per control state the hull and the bounds. A space's forms are laws of the state, or, of the
    // cells, laws at every key (those that read a cell; the others are the states' space's).
    const space = (kind: 'state' | 'cells' | number) => {
      const cells = kind === 'cells', view = typeof kind === 'number' ? views[kind]! : undefined
      const ctl: Ctl[] = keyModes.map(mo => ({atom: mo.atom, cuts: mo.values.slice(0, -1), top: mo.values.at(-1)!}))
      const exactAtoms = new Set(keyModes.map(mo => mo.atom)), own = cells ? [...plain, ...cellAtoms] : view ? [...plain, ...view.atoms] : plain
      // (a pair's cells take their map's cells' levels)
      const levelable = view ? cellLevels.flatMap(c => view.atoms.filter(i => atoms[i]!.parts[0]![0].slice(2, atoms[i]!.parts[0]![0].lastIndexOf(AT)) === atoms[c.atom]!.parts[0]![0]).map(i => ({...c, atom: i})))
        : levelsOf(own.filter(i => !exactAtoms.has(i) && !atoms[i]!.int && (!cells || atoms[i]!.cell)), cells ? valsK : valsS)
      const coords = own.filter(i => !exactAtoms.has(i)), CN = coords.length, dirs = directions(coords)
      const groups = new Map<string, Group>()
      let keyAtoms = ctl.map(c => c.atom)
      const residual = (e: bigint[], vs: Float64Array | number[]) => { let r = e[CN]!; for (let k = 0; k < CN; k++) if (e[k]) r += e[k]! * BigInt(vs[coords[k]!]!); return r }
      const join = (g: string, vs: Float64Array | number[], widen: boolean, into = groups) => {
        let grp = into.get(g)
        if (!grp) {
          grp = {eqs: coords.map((i, k) => { const e = Array.from({length: CN + 1}, () => 0n); e[k] = 1n; e[CN] = -BigInt(vs[i]!); return e }), hi: dirs.map(t => dirValue(t, vs)), raised: dirs.map(() => 0)}
          into.set(g, grp); return
        }
        const rs = grp.eqs.map(e => residual(e, vs)), nz = rs.flatMap((r, k) => (r !== 0n ? [k] : []))
        if (nz.length) {
          const piv = nz.reduce((p2, k) => (grp!.eqs[k]!.filter(x2 => x2 !== 0n).length < grp!.eqs[p2]!.filter(x2 => x2 !== 0n).length ? k : p2)), pe = grp.eqs[piv]!, pr = rs[piv]!
          for (const k of nz) if (k !== piv) grp.eqs[k] = normal(grp.eqs[k]!.map((x2, q2) => pr * x2 - rs[k]! * pe[q2]!))
          grp.eqs.splice(piv, 1)
        }
        dirs.forEach((t, k) => {
          const v = dirValue(t, vs)
          if (v <= grp!.hi[k]!) return
          if (!widen) { grp!.hi[k] = v; return }
          const n2 = ++grp!.raised[k]!, up = (n2 === 1 ? fine : coarse).find(b2 => b2 >= v)
          grp!.hi[k] = n2 > joinRaises || up === undefined ? Infinity : up
        })
        joins++
      }
      // an equality of the hull that is a form: at most joinSparse values, small coefficients
      const emitted = (e: bigint[]) => { let nz = 0; for (let k = 0; k < CN; k++) if (e[k]) { nz++; if (e[k]! > BigInt(joinCoef) || e[k]! < -BigInt(joinCoef)) return false } return nz > 0 && nz <= joinSparse && Number.isSafeInteger(Number(e[CN]!)) }
      const keyOf = (vs: Float64Array | number[]) => ctl.map(c => levelOf(c, vs[c.atom]!)).join(',')
      const combosOf = () => ctl.reduce<number[][]>((acc, c) => acc.flatMap(k2 => c.cuts.concat(0).map((_, lv) => [...k2, lv])), [[]])
      let combos = combosOf()
      // a control value by its level (as the keys hold it) as the values it stands for
      const atLevel = (a: At): At => atOf(ctl[keyAtoms.indexOf(a.atom)]!, a.value)
      // a point's rows in this space
      const vecs = (p: Point): Float64Array[] => (cells ? p.cells.map(valuesOf) : view ? (p.views[kind as number] ?? []).map(valuesOf) : [valuesOf(p.scalar)])
      const add = (p: Point, widen: boolean) => { for (const v of vecs(p)) join(keyOf(v), v, widen) }
      const rows = (cells ? distinctRows(cellRows) : view ? view.rows : rowsS).map(valuesOf)
      for (const v of rows) join(keyOf(v), v, false)
      opts.progress?.('join start', {space: kind, control: ctl.map(c => `${nameOf(c.atom)}:${c.cuts.join('/')}`).join(' '), groups: groups.size, dirs: dirs.length, coords: CN})
      // The control states no state reached, as fewer and smaller cubes (a program counter in bits: Spacer's clauses there
      // read two or three of its bits): each cube's values dropped one at a time, the yes/nos first, while it holds at no
      // control state reached, then the cubes another cube's values include left out. Together they say what the cubes
      // of every value say (the control state is one reached), but a goal reads fewer of them, and each of them less.
      const primes = (nev: At[][]): At[][] => {
        const reachedKeys = [...groups.keys()].map(k2 => k2.split(',').map(Number))
        const holdsAtSome = (c: At[]) => reachedKeys.some(vs => c.every(a => vs[keyAtoms.indexOf(a.atom)] === a.value))
        const out: At[][] = []
        for (const ats of nev) {
          let c = ats
          for (const a of [...ats.slice(1), ats[0]!]) {
            if (c.length <= 1) break
            const fewer = c.filter(b2 => b2 !== a)
            if (!holdsAtSome(fewer)) c = fewer
          }
          out.push(c)
        }
        const key2 = (c: At[]) => c.map(a => `${a.atom}=${a.value}`).sort().join('&')
        const uniq = [...new Map(out.map(c => [key2(c), c])).values()].sort((a, b) => a.length - b.length)
        return uniq.filter((c, i) => !uniq.slice(0, i).some(d => d.every(a => c.some(b2 => b2.atom === a.atom && b2.value === a.value))))
      }
      const forms = (push: (f: Form) => void) => {
        // (of the cells: only what reads one)
        // (over two plain keys, a form that reads one of them alone is the cells' form, which every key's instance covers)
        const keep = (f: Form) => {
          const read = atomsIn(f)
          const covered = new Set(read.flatMap(i => (atoms[i]!.place !== undefined ? view!.covers[atoms[i]!.place!]! : [])))
          if (kind === 'state' || (view ? covered.size >= view.need : read.some(i => atoms[i]!.cell))) push(view ? {...f, view: kind as number} : f)
        }
        // (a choice's value no state reached: one form, whatever the yes/nos; the control states no state reached, one form
        // for all, where there are several: each alone needs the others to be inductive, a goal each where one does)
        const reachedFirst = new Set([...groups.keys()].map(k2 => k2.split(',')[0])), nev: At[][] = []
        for (const combo of combos) {
          if (combo.length > 1 && !reachedFirst.has(String(combo[0]))) { if (combo.slice(1).every(v => v === 0)) nev.push([{atom: keyAtoms[0]!, value: combo[0]!}]); continue }
          const lv = combo.map((value, k) => ({atom: keyAtoms[k]!, value})), ats = lv.map(atLevel), grp = groups.get(combo.join(','))
          const guard = ats.length ? {guard: ats[0]!, ...(ats.length > 1 ? {also: ats.slice(1)} : {})} : {}
          if (!grp) { if (lv.length) nev.push(lv); continue }
          for (const e of grp.eqs) {
            if (!emitted(e)) continue
            const coef: [number, number][] = []
            for (let k = 0; k < CN; k++) if (e[k]) coef.push([coords[k]!, Number(e[k]!)])
            const d = -Number(e[CN]!)
            keep({coef, d, cells, ...guard, size: 0}); keep({coef: coef.map(([i, c]) => [i, -c]), d: -d, cells, ...guard, size: 0})
          }
          dirs.forEach((t, k) => {
            const hi = grp.hi[k]!
            if (!Number.isFinite(hi)) return
            // constant on the hull (the equalities say it), or a yes/no's own range
            const neg = dirs.findIndex(u => u.length === t.length && u.every(([i, c], q2) => i === t[q2]![0] && c === -t[q2]![1]))
            if (neg >= 0 && grp.hi[neg] === -hi) return
            if (t.length === 1 && modeOf(t[0]![0])?.bool && (t[0]![1] > 0 ? hi >= 1 : hi >= 0)) return
            keep({coef: t, d: hi, cells, ...guard, size: 0})
          })
        }
        // (once broken, each its own form from then on, so that a state joined in changes only the forms that
        // read its own control state, not every proof that read them all)
        if (nev.length > 1 && joinNevers && neversBroken < joinNeversBreaks) keep({coef: [], d: 0, cells, nevers: nev.map(c => c.map(atLevel)), size: 1})
        else for (const lvs of joinPrime ? primes(nev) : nev) { const ats = lvs.map(atLevel); keep({coef: [], d: 0, cells, ...(ats.length > 1 ? {never: ats} : {unreachable: ats[0]!}), size: 1}) }
      }
      // The control refined on demand (as CEGAR refines its predicates, here read off the rule): a counterexample to a
      // caller's law that the set allows and nothing rules out lies among the samples of its control state. A level of a
      // value the rule compares with a constant whose part of those samples and of the states joined in leaves it out
      // (past its hull or a bound, or with no state there at all) becomes a control value, and every state is joined
      // again: of those, the one that leaves out the most of the last counterexamples, then the one of fewest levels;
      // within joinKeys control states.
      // (2: left out with no state at its level, or by a form that reads what the laws read; 1: by another form; 0: not)
      const lawCoord = coords.map(i => read.has(atoms[i]!.cell ? atoms[i]!.parts[0]![0] : atoms[i]!.name))
      const lawDir = dirs.map(t => t.some(([i]) => lawCoord[coords.indexOf(i)]))
      const outOf = (c: Ctl, p: Point, all: Float64Array[]): number => Math.max(0, ...vecs(p).map(pv => {
        const key = keyOf(pv), side = all.filter(v => keyOf(v) === key && levelOf(c, v[c.atom]!) === levelOf(c, pv[c.atom]!))
        used.rows += all.length
        if (!side.length) return 2
        const tmp = new Map<string, Group>()
        for (const v of side) join('', v, false, tmp)
        const grp = tmp.get('')!
        let out = 0
        for (const e of grp.eqs) if (emitted(e) && residual(e, pv) !== 0n) out = Math.max(out, e.some((x2, k) => k < CN && x2 !== 0n && lawCoord[k]) ? 2 : 1)
        dirs.forEach((t, k) => { if (dirValue(t, pv) > grp.hi[k]!) out = Math.max(out, lawDir[k] ? 2 : 1) })
        return out
      }))
      const scored: string[] = []
      // (the samples' states alone: the states joined in are successors of states the coarser control allowed, which
      // the finer may not; the join starts again from the samples)
      const refine = (recent: Point[]): boolean => {
        scored.length = 0
        const all = rows
        let pick: Ctl | undefined, score = 0
        for (const c of levelable) {
          if (keyAtoms.includes(c.atom) || combos.length * (c.cuts.length + 1) > joinKeys) continue
          const first = outOf(c, recent[0]!, all)
          if (!first) continue
          const sc = recent.slice(1).reduce((k, q) => k + outOf(c, q, all), first) * 100 - c.cuts.length
          scored.push(`${nameOf(c.atom)}:${sc}`)
          if (sc > score) (pick = c, score = sc)
        }
        if (!pick) return false
        ctl.push(pick); keyAtoms = ctl.map(c2 => c2.atom); combos = combosOf()
        groups.clear()
        for (const v of all) join(keyOf(v), v, false)
        return true
      }
      // More directions (a form's own preimage), each bounded per control state by the states there, kept only where they
      // leave the point out (the bounds already there, widened or not, as they were).
      const deepen = (more: Rel[], reached: Point[], p: Point): boolean => {
        const known = new Set(dirs.map(t => JSON.stringify(t))), fresh = more.flatMap(r => [r.coef, r.coef.map(([i, c]) => [i, -c] as [number, number])]).filter(t => !known.has(JSON.stringify(t)) && t.every(([i]) => coords.includes(i)))
        if (!fresh.length) return false
        const his = new Map<string, number[]>()
        for (const v of [...rows, ...reached.flatMap(vecs)]) {
          const g = keyOf(v), h = his.get(g) ?? fresh.map(() => -Infinity)
          fresh.forEach((t, k) => { h[k] = Math.max(h[k]!, dirValue(t, v)) })
          his.set(g, h)
        }
        used.rows += rows.length
        if (!vecs(p).some(v => { const h = his.get(keyOf(v)); return !h || fresh.some((t, k) => dirValue(t, v) > h[k]!) })) return false
        dirs.push(...fresh); lawDir.push(...fresh.map(t => t.some(([i]) => lawCoord[coords.indexOf(i)])))
        for (const [g, grp] of groups) { const h = his.get(g) ?? fresh.map(() => -Infinity); grp.hi.push(...h); grp.raised.push(...fresh.map(() => 0)) }
        return true
      }
      return {cells, add, forms, refine, deepen, coords, control: () => `${ctl.map(c => nameOf(c.atom)).join(' ')} (${scored.join(' ')})`, groups}
    }
    const spaces = [space('state'), ...(mapNames.length && cellAtoms.length ? [space('cells')] : []), ...views.flatMap((v, i) => (v.rows.length ? [space(i)] : []))]
    const formsNow = (): Form[] => {
      const out: Form[] = [], seenT = new Set<string>()
      const push = (f: Form) => { const t = textOf(f); if (!seenT.has(t) && !names.has(t)) { seenT.add(t); out.push(f) } }
      for (const sp of spaces) sp.forms(push)
      return out
    }
    let rounds = 0, why = '', set: Form[] = []
    const params0: Env = {}
    // Beside the hull, forms of the candidates' that rule out a counterexample to the caller's laws (a state the set
    // allows whose successor breaks one): Houdini's, dropped when a counterexample's successor breaks them.
    const extras: Form[] = [], negs: Point[] = [], reached: Point[] = []
    let tried = 0
    // A caller's law broken after a step, or a step law by the step (`pre` and `input` its own).
    const breaks = (params: Env, st: State, pre?: State, input?: Request) => laws.some(l => { try { return !evalC(l.holds, params, st, m) } catch { return true } })
      || (!!pre && !!input && stepLaws.some(sl => { try { return !watch(m, run, sl, params, 4).step(pre, input, st) } catch { return true } }))
    // A request the rule allows at a state, found by the kernel (a model of the assumption there), some inputs fixed at
    // random first; the walks from a counterexample take these where random requests aren't allowed.
    const flagless = !Object.keys(m.step.flags ?? {}).length && !!m.assume
    // A kernel search's budget: wall time where the search is timed, else counted in the kernel's work (inferRates.work
    // a millisecond), so that what it finds doesn't depend on the machine.
    const budgeted = <T>(ms2: number, f: (until2: number) => T): T => (timed ? f(performance.now() + Math.max(200, Math.min(ms2, wallUntil - performance.now())))
      : counted(inferRates.work, () => f(clock() + ms2)))
    const requestAt = (params: Env, st: State): Request | undefined => {
      const vars: Record<string, E> = {}
      for (const [v, val] of Object.entries({...params, ...st.scalars})) vars[v] = n(val)
      for (let tries = 0; tries < 2; tries++) {
        const fix: C[] = []
        if (tries === 0) for (const i of m.inputs) if (rand(3) === 0) fix.push(same(x(i), n([0, 1, 2, ...Object.values(st.scalars)][rand(3 + scalars.length)]!)))
        const o = budgeted(joinRequestMs, until2 => grow({name: 'a request', hyps: [substC(m.assume!, {vars, maps: {}, flags: {}}), ...fix]}, new Map(), {nodes: 0, until: until2, units: false}))
        if (!('tree' in o) && o.stuck === 'sat' && o.witness) return Object.fromEntries(m.inputs.map(i => [i, o.witness![i] ?? 0])) as Request
      }
      return undefined
    }
    // Houdini on the cone of the caller's laws: each goal proven with the whole set assumed, beginning with the caller's
    // laws, then each form their trees read (usedHyps), breadth first; a proof stands while every form it read is still
    // in the set (the set only weakens). A goal's counterexample is a state the set allows: its successor is joined in
    // (or, breaking a caller's law, a candidate that rules the state out is added). Every goal of the cone proven, the
    // cone is inductive with the caller's laws, and it is the answer.
    const stood = new Map<string, string[]>(), blocked = new Set<string>(), callers = new Set([...laws, ...stepLaws].map(l => l.name))
    let cone: Form[] = [], dropped = 0
    const deepened = new Set<string>(), sameAgain = new Map<string, string>()
    // A state reached from one the set allows: joined in, and every extra false there dropped.
    const reach = (p2: Point) => {
      if (reached.length < 2000) reached.push(p2)
      for (const sp of spaces) sp.add(p2, true)
      for (let k = extras.length - 1; k >= 0; k--) if (!holdsAt(extras[k]!, p2)) { const f = extras[k]!; extras.splice(k, 1); pool = pool.filter(g2 => g2 !== f); dropped++ }
    }
    // A goal's step with these forms assumed (beside the caller's laws and the kinds'): its tree and the forms it read, or
    // the kernel's model.
    // A goal's hypotheses that are laws, by the law (the facts, the precondition and, for a law's step, the assumption
    // before them; a law about every key none, at no instances).
    const lawsFrom = (m0: Machine, ls: Law[], stepGoal: boolean, inst: Instances) => {
      const at = new Map<number, number>(), mm = plainOf(m0)
      let h = assumed(mm.facts ?? [], inst).length + (mm.pre ? 1 : 0) + (!stepGoal && mm.assume ? 1 : 0)
      ls.forEach((l, k) => { for (let q = assumed([l], inst).length; q > 0; q--) at.set(h++, k) })
      return at
    }
    // (a step law's goal: its step from a state the set allows)
    const stepLawOf = new Map(stepLaws.map(sl => [sl.name, sl]))
    // (the engine runs after a join that finds nothing, on a rule whose scalars the runs held at few values: below)
    let follows: boolean | undefined
    const engineFollows = () => (follows ??= !!sorts && callerLaws.some(l => l.keys?.length) && atoms.every((a, i) => a.cell || a.param || !!a.term || a.view !== undefined || i >= valsS.length || new Set(valsS[i]).size <= 4))
    const stepWith = (name: string, form: Form | undefined, ctx: Form[]) => {
      const ctxLaws = [...ctx, ...(form ? [form] : [])].map(lawFor), ls = [...given, ...ctxLaws], mm = forLaws(ctxLaws).m, sl = form ? undefined : stepLawOf.get(name)
      const idx = form ? ls.length - 1 : ls.findIndex(l => l.name === name)
      // (a rule with maps: the laws about every key at the instances the prover would read them at)
      const inst: Instances = !mapNames.length ? {} : sl ? stepLawInstances(mm, ls)(sl) : lawInstances(mm, ls, idx)
      const goalOf = (i2: Instances) => [sl ? stepLawObligations(mm, ls, i2, sl)[0]! : obligations(mm, ls, {[ls[idx]!.name]: i2}, idx)[1]!]
      type Asked = {used?: string[], stuck?: string, witness?: Record<string, number>, g: Goal}
      // (a model that breaks a law or a flag at a tuple of the goal's keys it wasn't assumed at: the goal asked again with
      // those instances; kernel/prove.ts's withModels)
      const ask = ([g]: Goal[], at: Instances): Asked => {
        const lawAt = lawsFrom(mm, ls, !!sl, at), used: string[] = []
        const read = (h: number) => { const k = lawAt.get(h); if (k !== undefined && k >= given.length && k !== idx && !used.includes(ls[k]!.name)) used.push(ls[k]!.name) }
        // First a model alone of the CDCL search (no tree unfolded): refuted, the hypotheses its leaves read are those
        // a tree would (the set's proof is the kernel's below, as before); a model is the counterexample; else the prover.
        if (joinCore) {
          const quick = budgeted(joinQueryMs / 4, until2 => growCdcl(g!, new Map(), {nodes: 0, until: until2}, {model: true, core: true})) as Refuted
          if (!('tree' in quick) && quick.why === REFUTED && quick.core) {
            for (const h of quick.core) read(h)
            return {used, g: g!}
          }
          if (!('tree' in quick) && quick.stuck === 'sat' && quick.witness) return {stuck: 'sat', witness: quick.witness, g: g!}
        }
        // (where the engine follows, the usual search on the wall too, joinGrowWall: the proving joins' searches take under a
        // second (decentralized lock's sums pass, 0.7–0.8 s), and an unknown one ran 13 s (wo's every k: Leader[k] <=
        // VoteRequestMsg[k]), the engine's time)
        const out = withWall(engineFollows() ? performance.now() + joinGrowWall : Infinity, () => budgeted(joinQueryMs, until2 => grow(g!, new Map(), {nodes: 0, until: until2})))
        if (!('tree' in out)) return {stuck: out.stuck, witness: out.stuck === 'sat' ? out.witness : undefined, g: g!}
        for (const h of usedHyps(g!, out.tree)) read(h)
        return {used, g: g!}
      }
      let at = inst
      const {result} = withModels<Asked>(mm, ls, inst, i2 => (at = i2, goalOf(i2)), gs => ask(gs, at), x => (mapNames.length && x.stuck === 'sat' && x.witness ? {goal: x.g, w: x.witness} : undefined), x => !!x.used || x.stuck === 'sat')
      return result.used ? {used: result.used} : {stuck: result.stuck, witness: result.witness}
    }
    const stateOf = (w: Record<string, number>): {params: Env, st: State} => {
      const st: State = {scalars: Object.fromEntries(scalars.map(v => [v, w[v] ?? 0])), maps: mapsOf(w)}
      named.set(st, new Set(Object.entries(st.maps).flatMap(([mp, cells]) => [...cells.keys()].map(k => `${mp}|${k}`))))
      return {params: m.params.length ? Object.fromEntries(m.params.map(p => [p, w[p] ?? 0])) : params0, st}
    }
    // (a step from a model's state names what it named and the cells the step wrote)
    const stepNamed = (st: State, next: State) => { const nm = named.get(st); if (nm) named.set(next, new Set([...nm, ...Object.entries(next.maps).flatMap(([mp, cells]) => [...cells].filter(([k, v]) => st.maps[mp]?.get(k) !== v).map(([k]) => `${mp}|${k}`))])) }
    // --- cubes: a point the samples leave out, as literals -------------------------------------------------------------
    const ctrl = modes.filter(mo => (mo.choice || mo.bool) && !atoms[mo.atom]!.cell && !atoms[mo.atom]!.param).map(mo => mo.atom)
    // (the rule's own comparisons first, then each value, then pairs: of two directions that leave out as many samples
    // the first is taken, so a bound the runs' depth sets, i0 <= 1 where they went 1 deep, gives way to the relation
    // that holds at every depth, i0 <= i1)
    const lc = plain.filter(i => !atoms[i]!.param && !ctrl.includes(i)), D0 = directions(lc), own = 2 * lc.length + (lc.length <= joinPairs ? 2 * lc.length * (lc.length - 1) : 0)
    const D = [...D0.slice(own), ...D0.slice(0, own)]
    const dot = (t: [number, number][], v: ArrayLike<number>) => { let s2 = 0; for (const [i, c] of t) s2 += c * v[i]!; return s2 }
    const litHolds = (l: Lit, v: ArrayLike<number>) => ('at' in l ? v[l.at.atom] === l.at.value : dot(l.lin.coef, v) <= l.lin.d)
    const inCube = (c: Lit[], v: ArrayLike<number>) => c.every(l => litHolds(l, v))
    const vecKey = (v: ArrayLike<number>) => Array.from(v).join(',')
    const S: Float64Array[] = rowsS.map(r => valuesOf(r)), sampled = new Set(S.map(vecKey))
    let initVec: Float64Array | undefined
    try { if (!m.params.length) initVec = valuesOf(pointOf({}, run.init({})).scalar) } catch { initVec = undefined }
    if (initVec && !sampled.has(vecKey(initVec))) { S.push(initVec); sampled.add(vecKey(initVec)) }
    const addSample = (v: Float64Array) => { const k2 = vecKey(v); if (!sampled.has(k2)) { sampled.add(k2); S.push(v) } }
    // a state from a point's values: an integer's two naturals normalized (the kernel's model may leave both above 0)
    const stateAt = (w: Record<string, number>): State => {
      const sc: Env = Object.fromEntries(scalars.map(v => [v, w[v] ?? 0]))
      for (const a of atoms) if (a.int && !a.param && !a.cell) { const [p, q] = [a.parts[0]![0], a.parts[1]![0]], v = (sc[p] ?? 0) - (sc[q] ?? 0); sc[p] = Math.max(0, v); sc[q] = Math.max(0, -v) }
      return {scalars: sc, maps: mapsOf(w)}
    }
    const vecOf = (st: State) => valuesOf(pointOf({}, st).scalar)
    // The cube of a point the samples leave out: its control literals and the rule's own comparisons true there (where
    // no sample is, a location the runs never reached, a cube of its control values alone isn't blocked: its
    // predecessors take it back to the samples; the comparisons are what a predecessor's guards say, as Spacer's
    // projections read them), then the direction that leaves out the most samples still in, its bound as weak as
    // leaves them out, until none is in (undefined: none leaves out the rest).
    const ruleLits: Lit[] = joinAtoms ? comparisons(m, laws, atoms, lc).map(lin => ({lin})) : []
    const cubeOf = (v: Float64Array): Lit[] | undefined => {
      const lits: Lit[] = ctrl.map(i => ({at: {atom: i, value: v[i]!}}))
      for (const l of ruleLits) if (litHolds(l, v)) lits.push(l)
      let alive = S.filter(s2 => inCube(lits, s2))
      while (alive.length) {
        let best = -1, bestN = 0
        for (let q = 0; q < D.length; q++) { const tv = dot(D[q]!, v); let cnt = 0; for (const s2 of alive) if (dot(D[q]!, s2) > tv) cnt++; if (cnt > bestN) (bestN = cnt, best = q) }
        if (best < 0) return undefined
        const t = D[best]!, tv = dot(t, v)
        let d = Infinity
        for (const s2 of alive) { const w2 = dot(t, s2); if (w2 > tv && w2 - 1 < d) d = w2 - 1 }
        lits.push({lin: {coef: t, d}})
        alive = alive.filter(s2 => dot(t, s2) <= d)
      }
      return lits
    }
    // A literal true at v and false at u (a control value first, then the direction u is furthest past v in), its
    // bound v's own (a bound just short of u would creep up one reached state at a time).
    const apart = (v: Float64Array, u: Float64Array): Lit | undefined => {
      for (const i of ctrl) if (v[i] !== u[i]) return {at: {atom: i, value: v[i]!}}
      let best: Lit | undefined, gap = 0
      for (const t of D) { const g2 = (dot(t, u) - dot(t, v)) / t.reduce((acc, [, c]) => acc + Math.abs(c), 0); if (g2 > gap) (gap = g2, best = {lin: {coef: t, d: dot(t, v)}}) }
      return best
    }
    // Literals put back from `from` until no sample is in the cube (false where a sample can't be left out).
    const outOfSamples = (c: Lit[], from: Lit[]): boolean => {
      for (let alive = S.filter(s2 => inCube(c, s2)); alive.length;) {
        let best: Lit | undefined, bestN = 0
        for (const l of from) { if (c.includes(l)) continue; let cnt = 0; for (const s2 of alive) if (!litHolds(l, s2)) cnt++; if (cnt > bestN) (bestN = cnt, best = l) }
        if (!best) return false
        c.push(best); alive = alive.filter(s2 => litHolds(best!, s2))
      }
      return true
    }
    const formOf = (c: Lit[], view?: number): Form => ({coef: [], d: 0, cells: false, cube: c, size: 1, ...(view !== undefined ? {view} : {})})
    // (a view's key read only by order literals bounding it from below (Ep[x] + 1 <= y, y nowhere else): a value past the
    // small instance's always has that literal, so the cube is a stronger one in disguise, and false where that is: no such
    // cube. One bounded from above alone is 0 there, the cube a true one (started is 0 and y + 1 <= Ep[x]: Ep is 0 before
    // init))
    const oneSided = (c: Lit[], vi: number): boolean => {
      const v = views[vi]!, side = new Map<string, number>(), held = new Set<string>()
      for (const l of c) for (const [a, k] of 'at' in l ? [[l.at.atom, 0] as [number, number]] : l.lin.coef) {
        const at = atoms[a]!
        if (at.place !== undefined) for (const ki of v.covers[at.place] ?? []) held.add(v.vars[ki]!)
        else if (at.term?.op === 'var' && k) { const s0 = side.get(at.term.name), dir = Math.sign(k); side.set(at.term.name, s0 === undefined || s0 === dir ? dir : 2) }
        else if (at.term) walk(at.term, o => { if (o.op === 'var') held.add(String(o.name)) })
      }
      return [...side].some(([nm, d]) => d === -1 && !held.has(nm))
    }
    const witnessStep = (w: Record<string, number>): {pre: State, post?: State} => {
      const pre = stateAt(w), input = requestOf(w)
      try { return {pre, post: run.step({}, pre, input)} } catch { return {pre} }
    }
    // Is the cube's negation inductive relative to these laws (the caller's and the kinds' beside)? Its literals after
    // the step are hypotheses of their own, so the refutation's core names those it read.
    const queryWith = (c: Lit[], frame: Law[], view?: number): {ok: true, core: Set<number>} | {ok: false, pre: State, post?: State} | undefined => {
      const f = formOf(c, view), own = lawFor(f), names2 = new Set([own.name]), ls = [...given, ...frame.filter(l => !names2.has(l.name) && !!names2.add(l.name)), own], mm = forLaws(ls).m
      // (a view's cube at the keys the prover would assume it and the rest at)
      const g = obligations(mm, ls, view !== undefined ? {[own.name]: lawInstances(mm, ls, ls.length - 1)} : {}, ls.length - 1)[1]!, last = g.hyps.at(-1)!
      const inner = last.op === 'not' && last.x.op === 'not' && last.x.x.op === 'and' && last.x.x.xs.length === c.length ? last.x.x.xs : undefined
      const tails = inner ?? [last], hyps = [...g.hyps.slice(0, -1), ...tails], base = hyps.length - tails.length
      const out = budgeted(joinCubeMs, until2 => growCdcl({name: 'a cube', hyps}, new Map(), {nodes: 0, until: until2}, {model: true, core: true})) as Refuted
      if ('tree' in out) return {ok: true, core: new Set(c.map((_, j) => j))}
      if (out.why === REFUTED) return {ok: true, core: inner && out.core ? new Set(out.core.filter(h => h >= base).map(h => h - base)) : new Set(c.map((_, j) => j))}
      if (out.stuck === 'sat' && out.witness) return {ok: false, ...witnessStep(out.witness)}
      return undefined
    }
    // A counterexample to a caller's law: its cube (its control state, the rule's comparisons and the bounds that keep
    // the samples out), blocked relative to the set (the set assumed before the step, and the cube's own negation, as
    // IC3's relative induction), its literals after the step those the refutation read (its core), the samples and the
    // start kept out. A predecessor the set allows into the cube: its own cube blocked first (a few deep), else the
    // cube made smaller to leave the predecessor's successor out. Each cube blocked is a form of the set (a
    // disjunction: never all its literals), which the join keeps or drops as any other.
    let cubed = 0, cubeWhy = ''
    // IC3's generalization of a cube blocked (Bradley's down, literal dropping as Een, Mishchenko and Brayton's): the
    // literals taken out a part at a time (half of them, then quarters, ..., then one by one), a part kept out where the
    // cube without it still leaves the start and the samples out and is still blocked relative to the same laws (the
    // refutation's core then cutting it further); within joinDownQueries queries. A cube's core reads most of its
    // literals where the step's terms are a chain of ifs (research/dag: a refutation's core is nearly its whole path), so
    // the core alone leaves a cube of every control value; Spacer's clauses on these tasks read two to four.
    const stateOut = (c: Lit[]) => !(initVec && inCube(c, initVec)) && !S.some(s2 => inCube(c, s2))
    const down = (c: Lit[], frame: Law[], out: (c: Lit[]) => boolean = stateOut, view?: number): Lit[] => {
      let cur = c, queries = 0
      for (let part = Math.ceil(cur.length / 2); part >= 1 && queries < joinDownQueries && now() < jUntil && !stop(); part = part === 1 ? 0 : Math.ceil(part / 2)) {
        for (let i = 0; i < cur.length && cur.length > 1 && queries < joinDownQueries && now() < jUntil && !stop();) {
          const cand = [...cur.slice(0, i), ...cur.slice(i + part)]
          if (!cand.length || !out(cand)) { i += part; continue }
          queries++
          const r = queryWith(cand, frame, view)
          if (!r?.ok) { i += part; continue }
          const cut = cand.filter((_, j) => r.core.has(j))
          cur = cut.length && out(cut) ? cut : cand
        }
      }
      return cur
    }
    const blockCube = (v: Float64Array, depth: number, within: Form[]): Form[] => {
      let c = cubeOf(v)
      const made: Form[] = []
      if (!c) cubeWhy = sampled.has(vecKey(v)) ? 'a sample' : 'inside'
      // (relative to as little of the set as will do, as the join's goals are: the forms that rule out each
      // predecessor found, doubling, then the whole set)
      let ctx: Form[] = []
      for (let tries = 0; c && tries < joinCubeTries && now() < jUntil && !stop(); tries++) {
        const r = queryWith(c, [...ctx, ...made].map(lawFor).filter(l => l.name !== textOf(formOf(c!))))
        if (!r) { cubeWhy = 'unknown'; break }
        if (r.ok) {
          const c2 = c.filter((_, j) => r.core.has(j))
          if (initVec && inCube(c2, initVec)) { const l = c.find(l2 => !litHolds(l2, initVec!)); if (l) c2.push(l) }
          const c3 = outOfSamples(c2, c) ? c2 : c
          made.push(formOf(joinDown ? down(c3, [...ctx, ...made].map(lawFor).filter(l => l.name !== textOf(formOf(c3)))) : c3))
          break
        }
        if (!r.post) { cubeWhy = 'no step'; break }
        const pv = vecOf(r.pre), qv = vecOf(r.post)
        const ruling = within.filter(f => !f.cells && !ctx.includes(f) && !holdsRow(f, {...r.pre.scalars}))
        if (ruling.length) { ctx = [...ctx, ...ruling.slice(0, Math.max(joinAdd, ctx.length))]; tries--; continue }
        if (!inCube(c, qv)) { cubeWhy = 'outside'; break }
        const sub = depth > 0 && !sampled.has(vecKey(pv)) ? blockCube(pv, depth - 1, [...within, ...made]) : []
        if (sub.length) { made.push(...sub); continue }
        // (a predecessor the runs reached: its successor is reached too, a sample now)
        if (sampled.has(vecKey(pv))) addSample(qv)
        const l = apart(v, qv)
        if (!l) { cubeWhy = 'reached'; break }
        c = [...c, l]
        cubeWhy = 'tries'
      }
      return made
    }
    // A view's cube (two holders, two tickets): a row of a counterexample no sample's row is, as literals over the view's
    // cells (each few-valued cell at its value, each equality between two cells of one map that holds there, then the
    // bounds that leave the samples' rows out), blocked as the state's cubes are (its negation proven relative to the
    // set, the literals it doesn't need taken out): a law at every tuple of the view's keys. The disjunctions a hull
    // can't say (two waiting threads' tickets differ) are such cubes.
    const viewSpaces = views.map(v => {
      const R = v.rows.slice(0, 3000).map(valuesOf), seen = new Set(R.map(vecKey)), mapOf = (i: number) => atoms[i]!.parts[0]![0].slice(2, atoms[i]!.parts[0]![0].lastIndexOf(AT))
      const own = v.atoms.filter(i => !atoms[i]!.int), few = own.filter(i => new Set(R.map(r => r[i])).size <= 3)
      const eqs: Lit[] = own.flatMap((i, a2) => own.slice(a2 + 1).filter(j => mapOf(i) === mapOf(j) && !few.includes(i)).flatMap(j => [{lin: {coef: [[i, 1], [j, -1]] as [number, number][], d: 0}}, {lin: {coef: [[j, 1], [i, -1]] as [number, number][], d: 0}}]))
      const dirs = own.filter(i => !few.includes(i)).flatMap(i => [[[i, 1]], [[i, -1]]] as [number, number][][])
      let starts: Float64Array[] = []
      try { if (!m.params.length) starts = v.rowsOf({}, run.init({})).map(valuesOf) } catch { starts = [] }
      const out = (c: Lit[]) => !starts.some(x2 => inCube(c, x2)) && !R.some(x2 => inCube(c, x2))
      return {R, seen, few, eqs, dirs, out}
    })
    const viewCube = (p: Point): Form[] => {
      for (const [vi, V] of viewSpaces.entries()) for (const r of (p.views[vi] ?? []).slice(0, 8)) {
        const x2 = valuesOf(r)
        if (V.seen.has(vecKey(x2))) continue
        const c: Lit[] = [...V.few.map(i => ({at: {atom: i, value: x2[i]!}})), ...V.eqs.filter(l => litHolds(l, x2))]
        for (let alive = V.R.filter(y => inCube(c, y)); alive.length;) {
          let best: [number, number][] | undefined, bestN = 0
          for (const t of V.dirs) { const tv = dot(t, x2); let cnt = 0; for (const y of alive) if (dot(t, y) > tv) cnt++; if (cnt > bestN) (bestN = cnt, best = t) }
          if (!best) break
          const d = dot(best, x2)
          c.push({lin: {coef: best, d}}); alive = alive.filter(y => dot(best!, y) <= d)
        }
        if (!V.out(c)) continue
        // (relative to the forms proven so far, as little of the set as will do; else the whole set, ungeneralized)
        const proven = set.filter(f => stood.has(textOf(f))).map(lawFor), r2 = queryWith(c, proven, vi)
        if (r2?.ok) return [formOf(joinDown ? down(c, proven, V.out, vi) : c, vi)]
        if (queryWith(c, set.map(lawFor), vi)?.ok) return [formOf(c, vi)]
      }
      return []
    }
    // The template (DistAI's): per sort, as many keys as the most places of that sort one map or a caller's law reads; a
    // view of each sub-template of one to four keys (each plain map at each key of its sort, each composed map at each
    // row and column key, a column's keys below N, keys of one sort distinct). Its cubes: each set of at most three
    // literals (a few-valued cell or scalar at a value, its largest as "at least") no row of the samples or the start is
    // in, minimal, reading every key, one per renaming of a sort's keys, the fewest literals first.
    const known = new Map<number, {R: Float64Array[], lits: Lit[]}>()
    // (each enumerated view's keys' sorts: minimal implication's renamings)
    const viewSorts = new Map<number, string[]>()
    // (order literals that can't hold together, p ≤ q + d around a cycle summing below 0: a cube nothing is in)
    const contradicts = (c: Lit[]) => {
      const e = c.flatMap(l => ('lin' in l && l.lin.coef.length === 2 && l.lin.coef[0]![1] === 1 && l.lin.coef[1]![1] === -1 ? [[l.lin.coef[0]![0], l.lin.coef[1]![0], l.lin.d] as const] : []))
      const ns = [...new Set(e.flatMap(([p, q]) => [p, q]))], dist = new Map(ns.map(q => [q, 0]))
      for (let k = 0; k <= ns.length; k++) for (const [p, q, d] of e) if (dist.get(q)! + d < dist.get(p)!) { if (k === ns.length) return true; dist.set(p, dist.get(q)! + d) }
      return false
    }
    const smallReq: {params: Env, combos: Request[]}[] = []
    // (each pool cube's near misses: rows of the filter's larger instances where every literal but one holds)
    const nearMiss = new Map<Form, number>()
    let smallAll: Sample[] = []
    // (a small state run under another table of a function: its params' table, the rule's functions swapped while it is read)
    const tableOf = new WeakMap<Env, Record<string, Fn>>()
    const withTable = <T>(params: Env, f: () => T): T => {
      const tb = tableOf.get(params)
      if (!tb || !m.fns) return f()
      const saved = Object.entries(tb).map(([k]) => [k, m.fns![k]!] as [string, Fn])
      Object.assign(m.fns, tb)
      try { return f() } finally { for (const [k, fn] of saved) m.fns[k] = fn }
    }
    const enumerated = (): Form[] => {
      const ks = sorts!, comp = ks.composedMaps.length && pairing?.n ? [ks.find('hi'), ks.find('lo')] : undefined
      const multi = [...ks.arity].map(([mp, k]) => ({mp, slots: Array.from({length: k}, (_, i) => ks.find(`${mp}:${i}`))}))
      const ss = [...new Set([...ks.plainRead.map(mp => ks.find(`M:${mp}`)), ...(comp ?? []), ...multi.flatMap(q => q.slots)])]
      // (a map's values of a key's sort, and the sorts an order compares: e < Ep[a] makes Ep's values epochs, ordered)
      const vp = new Map<string, string>(), vf = (a: string): string => { const q = vp.get(a); return q === undefined || q === a ? a : vf(q) }
      const node = (e: E): string | undefined => (e.op === 'var' ? (m.inputs.includes(e.name) ? ks.find(e.name) : m.params.includes(e.name) ? `P:${e.name}` : undefined) : e.op === 'get' && (mapSet.has(e.map) || m.fns?.[e.map]) ? `V:${e.map}` : undefined)
      const ord = new Set<string>(), leaves = (e: E): E[] => (e.op === 'if' ? [...leaves(e.then), ...leaves(e.else)] : [e])
      const relate = (a?: string, b?: string, less = false) => { if (a && b) { const ra = vf(a), rb = vf(b); if (ra !== rb) vp.set(ra, rb); if (less) ord.add(vf(b)) } }
      walk([m.step, m.assume], o => { const c = o as unknown as C; if (c.op === '<' || c.op === '<=' || c.op === '=') relate(node(c.a), node(c.b), c.op !== '=') })
      // (a param that bounds a sort's keys, k < p, is that sort's size in the small instance; a param a key equals, a write
      // at every key at it (k = first) or a read at it, is an element of that sort, which pins it against renaming)
      const bounding = new Map<string, Set<string>>(), elementOf = new Map<string, string>()
      walk([m.step, m.assume], o => { const c = o as unknown as C; if ((c.op === '<' || c.op === '<=') && c.b.op === 'var' && m.params.includes(c.b.name) && c.a.op === 'var' && m.inputs.includes(c.a.name)) bounding.set(c.b.name, new Set([...(bounding.get(c.b.name) ?? []), ks.find(c.a.name)])) })
      for (const [mp, w] of Object.entries(m.step.maps ?? {})) {
        const srt = ks.plainRead.includes(mp) ? ks.find(`M:${mp}`) : undefined
        if (srt && 'each' in w) walk(w.value, o => { const c = o as unknown as C; if (c.op === '=' && c.a.op === 'var' && c.b.op === 'var') { const q = c.a.name === w.each ? c.b.name : c.b.name === w.each ? c.a.name : undefined; if (q && m.params.includes(q)) elementOf.set(q, srt) } })
      }
      walk([m.step, m.assume], o => { const e = o as unknown as E; if (e.op === 'get' && e.key.op === 'var' && m.params.includes(e.key.name) && ks.plainRead.includes(e.map)) elementOf.set(e.key.name, ks.find(`M:${e.map}`)) })
      for (const [mp, w] of Object.entries(m.step.maps ?? {})) for (const l of leaves(w.value)) relate(`V:${mp}`, node(l))
      const valueSort = (mp: string) => ss.find(q => vf(q) === vf(`V:${mp}`)), ordered = (q: string) => [...ord].some(o => vf(o) === vf(q))
      // (a function of a key whose values are a composed map's rows: Pending[idn(x)·N + y])
      const fnHi = Object.keys(m.fns ?? {}).filter(f => comp && ss.includes(ks.find(`F:${f}`)) && vf(`V:${f}`) === vf(comp[0]!))
      const placesOf = (s: string) => (comp ? comp.filter(c => c === s).length + fnHi.filter(f => ks.find(`F:${f}`) === s).length : 0)
      const width = ss.map(s => Math.min(3, Math.max(ordered(s) ? 2 : 0, ks.plainMaps(s).length ? 1 : 0, placesOf(s) + (placesOf(s) >= 2 ? 1 : 0), ...multi.map(q => q.slots.filter(c => c === s).length), ...callerLaws.map(l => [l.forall, ...(l.keys ?? [])].filter(b => b && ks.sortOf(l, b) === s).length))))
      // (a key's own bounds and domain: a caller's law's guards on one key of the sort, k < 64, k < size)
      const bounds = new Map<string, C[]>()
      for (const l of callerLaws) {
        const b = [l.forall, ...(l.keys ?? [])].filter((q): q is string => !!q)
        for (const g of b.length ? ks.shape(l, b).guards : []) {
          const one = b.filter(q => JSON.stringify(g).includes(`"name":"${q}"`)), s = one.length === 1 ? ks.sortOf(l, one[0]!) : undefined
          if (s) bounds.set(s, [...(bounds.get(s) ?? []), substC(g, {vars: {[one[0]!]: x(KEY)}, maps: {}, flags: {}})])
        }
      }
      opts.progress?.('join template', {sorts: ss.map((s, i) => `${s}:${width[i]}`).join(' '), multi: multi.map(q => `${q.mp}:${q.slots.join(',')}`).join(' ')})
      // The small instance (BRAB's, DuoAI's simulation made complete): each key sort its first 2 to 3 elements (its width),
      // an ordered one 0..3, a function's values over its argument's, params small, each input over its sort's elements
      // (a carried set over their subsets, any other over the values a few draws give), every reachable state by BFS up
      // to 20,000 states and a seventh of what is left; its states the views' rows first.
      // (an instance: the small one (`grow` none, the samples), or `grow` more elements of a sort within `share` ms, its
      // BFS uncut and its own draws (the pool's data filter))
      const instance = (grow: (q: string) => number, share: number | undefined, rnd: Rand) => {
        const base = share === undefined, most = base ? 20_000 : 2_000_000, combosMax = base ? 2048 : 16_384, reqs: {params: Env, combos: Request[]}[] = []
        const size = (q: string) => Math.max(2, Math.min(3, width[ss.indexOf(q)] ?? 2)) + grow(q), keyDom = (q: string) => Array.from({length: ordered(q) ? 4 + grow(q) : size(q)}, (_, i) => i)
        const fnDom = (q: string) => Object.keys(m.fns ?? {}).filter(f => vf(`V:${f}`) === vf(q) && ss.includes(ks.find(`F:${f}`))).flatMap(f => keyDom(ks.find(`F:${f}`)).map(k => { try { return fnValue(m.fns![f]!, k) } catch { return 0 } }))
        const domOf = (v: string, drawn: Set<number>): number[] => { const q = ks.find(v); return ss.includes(q) ? (fnDom(q).length ? fnDom(q) : keyDom(q)) : [...drawn].sort((a, b) => a - b) }
        const pvs = new Map<string, Env>()
        for (let t = 0; t < 200 && pvs.size < (base ? 4 : 8); t++) {
          // (a param a sort's keys are compared with, n < size, is that sort's size in the instance)
          const p = randomParams(2, rnd)
          for (const q of m.params) {
            const el = elementOf.get(q), srts = ss.filter(r => vf(r) === vf(`P:${q}`))
            if (el && ss.includes(el)) p[q] = keyDom(el)[rnd(keyDom(el).length)]!
            else if (bounding.has(q) && [...bounding.get(q)!].some(r => ss.includes(r))) p[q] = Math.min(...[...bounding.get(q)!].filter(r => ss.includes(r)).map(r => keyDom(r).length))
            else if (srts.length) { const d = keyDom(srts[0]!); p[q] = d[rnd(d.length)]! }
          }
          if ((m.pre && !evalC(m.pre, p, {scalars: {}, maps: {}}, m)) || m.params.some(q => ss.includes(ks.find(q)) && !domOf(q, new Set()).includes(p[q]!))) continue
          pvs.set(JSON.stringify(p), p)
        }
        const t3 = performance.now(), seen = new Set<string>(), small: Sample[] = []
        let end2 = performance.now() + (share ?? Math.min(4000, (wallUntil - performance.now()) / 7))
        let cut = false
        // (a state's key: its cells off the map's default, in key order, the least under the renamings of each symmetric
        // sort's elements: a sort the step neither orders, nor computes on (a function's argument, a param's bound), nor
        // stores in a cell or a scalar; every map's key read as its parts' sorts, else no renaming)
        const layout = new Map<string, string[]>()
        for (const mp of Object.keys(m.maps ?? {})) {
          const ar = ks.arity.get(mp)
          if (ks.plainRead.includes(mp)) layout.set(mp, [ks.find(`M:${mp}`)])
          else if (ks.composedMaps.includes(mp) && pairing?.n) layout.set(mp, [ks.find('hi'), ks.find('lo')])
          else if (ar && pairing?.n) layout.set(mp, Array.from({length: ar}, (_, i) => ks.find(`${mp}:${i}`)))
        }
        const stored = new Set(m.inputs.filter(i => JSON.stringify(m.step.state ?? {}).includes(`"name":"${i}"`)).map(i => ks.find(i)))
        const pinned = new Set(elementOf.values()), sym = layout.size === Object.keys(m.maps ?? {}).length ? ss.filter(q => !pinned.has(q) && !ordered(q) && !valueSort2(q) && !stored.has(q) && !Object.keys(m.fns ?? {}).some(f => ks.find(`F:${f}`) === q) && !m.params.some(p2 => vf(`P:${p2}`) === vf(q))) : []
        function valueSort2(q: string) { return Object.keys(m.maps ?? {}).some(mp => valueSort(mp) === q) }
        const perms = (k: number): number[][] => (k <= 1 ? [[0]] : perms(k - 1).flatMap(p2 => Array.from({length: k}, (_, i) => [...p2.slice(0, i), k - 1, ...p2.slice(i)])))
        let rens: Map<string, number[]>[] = [new Map()]
        for (const q of sym) { const next = rens.flatMap(r2 => perms(size(q)).map(pm => new Map([...r2, [q, pm]]))); if (next.length > 36) break; rens = next }
        const renKey = (mp: string, k: number, ren: Map<string, number[]>): number => {
          const lay = layout.get(mp)
          if (!lay || !ren.size) return k
          if (lay.length === 1) { const pm = ren.get(lay[0]!); return pm && k < pm.length ? pm[k]! : k }
          if (k < pairing!.c) return k
          const digits: number[] = []
          for (let i = 0, r = k - pairing!.c; i < lay.length; i++, r = Math.floor(r / pairing!.n)) digits.unshift(i === lay.length - 1 ? r : r % pairing!.n)
          return pairing!.c + digits.reduce((acc, d, i) => { const pm = ren.get(lay[i]!); return acc * pairing!.n + (pm && d < pm.length ? pm[d]! : d) }, 0)
        }
        const textAt = (q: Sample, ren: Map<string, number[]>) => JSON.stringify([q.params, q.st.scalars, Object.entries(q.st.maps).map(([mp, cells]) => { const d = q.st.defaults?.[mp] ?? m.maps?.[mp] ?? 0; return [...cells].filter(([, v]) => v !== d).map(([k, v]) => [renKey(mp, k, ren), v]).sort((a, b) => a[0]! - b[0]!) }), q.st.defaults ?? null])
        // (the state's own text first, its renamings' only for a text not seen)
        const canon = new Map<string, string>()
        const keyOf3 = (q: Sample) => {
          const own = textAt(q, new Map())
          let best = canon.get(own)
          if (best === undefined) { best = own; for (const ren of rens) { const t = textAt(q, ren); if (t < best) best = t } canon.set(own, best) }
          return best
        }
        // (the step compiled once: core/machine.ts's JavaScript, its assumption refusing a request as `allowed` does)
        // (a function the kernel knows by its facts alone (no recurrence, no call) on a template sort: its own table and a
        // few others that keep its facts on the sort's keys (its values reversed, and each turned by one), each run as its
        // own machine; their states' rows read under their table. One table alone is a fact of it, not of the rule: ring's
        // ids, every node past another one's below it)
        const tables: {m: Machine, run: typeof run, js: ReturnType<typeof loadJs> | undefined, fns: Record<string, Fn>}[] = [{m, run, js: m.history ? undefined : loadJs(m), fns: {}}]
        for (const [f, fn] of Object.entries(m.fns ?? {})) {
          const arg = ks.find(`F:${f}`)
          if (fn.call || fn.recur || (fn.arity ?? 1) !== 1 || !ss.includes(arg) || m.history) continue
          const dom = keyDom(arg), vals = dom.map(k => { try { return fnValue(fn, k) } catch { return 0 } }), turn = (vs: number[]) => [...vs.slice(1), vs[0]!]
          for (const vs of [[...vals].reverse(), turn(vals), turn([...vals].reverse())]) {
            const fn2: Fn = {...fn, js: `(k) => (${JSON.stringify(Object.fromEntries(dom.map((k, i) => [k, vs[i]])))})[k] ?? (${fn.js})(k)`}, m2: Machine = {...m, fns: {...m.fns, [f]: fn2}}
            const keeps = (m.facts ?? []).every(fc => { const b = [fc.forall, ...(fc.keys ?? [])].filter((q): q is string => !!q); return b.reduce<number[][]>(acc => acc.flatMap(t2 => dom.map(k => [...t2, k])), [[]]).every(t => { try { return evalC(fc.holds, Object.fromEntries(b.map((q, k) => [q, t[k]!])), {scalars: {}, maps: {}}, m2) } catch { return false } }) })
            if (keeps && tables.length < 4) tables.push({m: m2, run: interpret(m2), js: loadJs(m2), fns: {[f]: fn2}})
          }
        }
        const stepIn = (tb: typeof tables[number], params: Env, st: State, input: Request): State | undefined => {
          try { if (tb.js) return tb.js.step(params, tb.js.fork(st), input); return allowed(tb.m, tb.run, params, st, input) ? tb.run.step(params, st, input) : undefined } catch { return undefined }
        }
        const stepOf = (params: Env, st: State, input: Request) => stepIn(tables[0]!, params, st, input)
        const others: Sample[] = []
        for (const params of pvs.values()) {
          const drawn = new Map<string, Set<number>>(m.inputs.map(i => [i, new Set<number>()]))
          for (let t = 0; t < 200; t++) { const inp = randomInput(params, 2, rnd); for (const i of m.inputs) if (typeof inp[i] === 'number') drawn.get(i)!.add(inp[i] as number) }
          // (an input no template sort holds, bounded by a param (n1 < size): every value below it)
          const boundBy = (i: string) => [...bounding].find(([, v2]) => v2.has(ks.find(i)))?.[0]
          const doms: [string, (number | Map<number, number>)[]][] = m.inputs.map(i => [i, !ss.includes(ks.find(i)) && boundBy(i) !== undefined && (params[boundBy(i)!] ?? 0) <= 8 ? Array.from({length: params[boundBy(i)!] ?? 0}, (_, k) => k) : domOf(i, drawn.get(i)!)])
          for (const q of m.inputMaps ?? []) { const ks2 = keyDom(ks.find(`M:${q}`)); doms.push([q, Array.from({length: 2 ** ks2.length}, (_, b) => new Map(ks2.filter((_, j) => b >> j & 1).map(k => [k, 1] as [number, number])))]) }
          let combos: Request[] = [{}]
          for (const [i, d] of doms) combos = combos.flatMap(c => d.map(v2 => ({...c, [i]: v2})))
          if (combos.length > combosMax) combos = Array.from({length: combosMax}, () => combos[rnd(combos.length)]!)
          reqs.push({params, combos})
          if (base) smallReq.push({params, combos})
          if (base) opts.progress?.('join small domains', {params: JSON.stringify(params), doms: doms.map(([i, d]) => `${i}:${d.length > 8 ? d.length : d.map(v2 => (typeof v2 === 'number' ? v2 : 'map')).join('/')}`).join(' '), combos: combos.length})
          let st0: State
          try { st0 = run.init(params) } catch { continue }
          const tB = performance.now(), queue = [{params, st: st0}], qi = {at: 0}, bfsEnd = performance.now() + (end2 - performance.now()) * 0.75 / (pvs.size - reqs.length + 1)
          seen.add(keyOf3(queue[0]!)); small.push(queue[0]!)
          // (a BFS that won't finish (a quarter of its share gone, 1 s at least, and its queue still a quarter of what it
          // found): cut there, the walks half a second after; an instance it does finish is what it was)
          const cutAt = base ? tB + Math.max(1000, (bfsEnd - tB) / 4) : Infinity
          while (qi.at < queue.length && small.length < most && performance.now() < bfsEnd) {
            if (performance.now() > cutAt && (queue.length - qi.at) * 4 >= small.length) { end2 = Math.min(end2, performance.now() + 500); break }
            const q0 = queue[qi.at++]!
            for (const input of combos) {
              used.tries++
              const next = stepOf(params, q0.st, input)
              if (!next) continue
              const q1 = {params, st: next}, k1 = keyOf3(q1)
              if (!seen.has(k1)) { seen.add(k1); small.push(q1); queue.push(q1) }
            }
          }
          if (qi.at < queue.length) cut = true
          queue.length = 0
          // (the other tables: a BFS each from the same start, within the same share)
          for (const tb of tables.slice(1)) {
            let s0: State
            try { s0 = tb.run.init(params) } catch { continue }
            const p2 = {...params}, q2 = [{params: p2, st: s0}], q2i = {at: 0}, seen2 = new Set([keyOf3(q2[0]!)]), end3 = Math.min(end2, performance.now() + (bfsEnd - tB))
            tableOf.set(p2, tb.fns); others.push(q2[0]!)
            while (q2i.at < q2.length && others.length < most && performance.now() < end3) {
              const q0 = q2[q2i.at++]!
              for (const input of combos) { const next = stepIn(tb, p2, q0.st, input); if (!next) continue; const q1 = {params: p2, st: next}, k1 = keyOf3(q1); if (!seen2.has(k1)) { seen2.add(k1); others.push(q1); q2.push(q1) } }
            }
          }
        }
        // (then random walks from its last states, deeper than the BFS's levels reach: each step the first of a few
        // requests that changes the state, to the end of its share)
        const bfs = small.length
        for (let t = 0; cut && reqs.length && small.length < most && performance.now() < end2; t++) {
          const from = small[Math.max(0, small.length - 1 - rnd(Math.min(small.length, 64)))]!, req = reqs.find(q => q.params === from.params)
          if (!req) break
          let at = from.st
          for (let d = 0; d < 40 && performance.now() < end2; d++) {
            let next: State | undefined
            for (let k = 0; k < 16 && !next; k++) {
              const input = req.combos[rnd(req.combos.length)]!
              used.tries++
              const s2 = stepOf(from.params, at, input)
              if (s2 && keyOf3({params: from.params, st: s2}) !== keyOf3({params: from.params, st: at})) next = s2
            }
            if (!next) break
            at = next
            const q1 = {params: from.params, st: at}, k1 = keyOf3(q1)
            if (!seen.has(k1)) { seen.add(k1); small.push(q1) }
          }
        }
        if (base) opts.progress?.('join small instance', {states: small.length, bfs, params: pvs.size, symmetric: sym.slice(0, rens.length > 1 ? sym.length : 0).join(), ms: Math.round(performance.now() - t0), took: Math.round(performance.now() - t3)})
        return {small, others, bfs, cut, params: pvs.size, ms: Math.round(performance.now() - t3)}
      }
      let baseMs = 0
      { const r0 = instance(() => 0, undefined, rand); baseMs = r0.ms; samples.unshift(...r0.small); smallAll = [...r0.small, ...r0.others] }
      const out: Form[] = []
      for (const counts of width.reduce<number[][]>((acc, w) => acc.flatMap(c => Array.from({length: w + 1}, (_, k) => [...c, k])), [[]])) {
        const keys = ss.flatMap((s, i) => Array.from({length: counts[i]!}, () => s)), vars = keys.map((_, i) => `key${i + 1}$enum`)
        if (!keys.length || keys.length > 5 || stop()) continue
        const places: E[] = [], mapsAt: string[][] = [], covers: number[][] = []
        keys.forEach((s, i) => { if (ks.plainMaps(s).length) { places.push(x(vars[i]!)); mapsAt.push(ks.plainMaps(s)); covers.push([i]) } })
        if (comp) keys.forEach((a, i) => keys.forEach((b, j) => { if (a === comp[0] && b === comp[1]) { places.push(ks.compose(x(vars[i]!), x(vars[j]!))); mapsAt.push(ks.composedMaps); covers.push(i === j ? [i] : [i, j]) } }))
        for (const q of multi) for (const t of q.slots.reduce<number[][]>((acc, s) => acc.flatMap(p => keys.flatMap((k2, j) => (k2 === s ? [[...p, j]] : []))), [[]])) { places.push(ks.composeAll(t.map(j => x(vars[j]!)))); mapsAt.push([q.mp]); covers.push([...new Set(t)]) }
        for (const f of fnHi) keys.forEach((a, i) => keys.forEach((b, j) => { if (a === ks.find(`F:${f}`) && b === comp![1]) { places.push(ks.compose(get(f, x(vars[i]!)), x(vars[j]!))); mapsAt.push(ks.composedMaps); covers.push(i === j ? [i] : [i, j]) } }))
        const names = ['x', 'y', 'z', 'w', 'u'].slice(0, keys.length), fns = Object.keys(m.fns ?? {}).filter(f => ordered(`V:${f}`) && ss.includes(ks.find(`F:${f}`)))
        const extra = [...keys.flatMap((q, i) => (ordered(q) ? [{name: names[i]!, term: x(vars[i]!)}] : [])), ...fns.flatMap(f => keys.flatMap((q, i) => (q === ks.find(`F:${f}`) ? [{name: `${f}(${names[i]})`, term: get(f, x(vars[i]!))}] : [])))]
        const frame = all(...keys.flatMap((s, i) => [...(comp && s === comp[1] && !bounds.has(s) ? [atMost(x(vars[i]!), n(pairing!.n - 1))] : []), ...[...new Set((bounds.get(s) ?? []).map(g => JSON.stringify(substC(g, {vars: {[KEY]: x(vars[i]!)}, maps: {}, flags: {}}))))].map(t => JSON.parse(t) as C), ...keys.slice(0, i).flatMap((t, j) => (t === s ? [not(same(x(vars[j]!), x(vars[i]!)))] : []))]))
        const vi = views.length
        addView({vars, names, places, covers, frame, need: keys.length, printable: false}, mapsAt, st => keys.map(s => ks.valuesAt(st, s)), Math.max(2, Math.floor(64 ** (1 / keys.length))), extra, true)
        // (the rows: every small state's, distinct, at most 20,000; the view's own rows stop at its first states, the shallow
        // ones, so a deep state's (a leader's) would be left out)
        viewSorts.set(vi, keys)
        const v = views[vi]!, R: Float64Array[] = [], seenRows = new Set<string>()
        for (const q of smallAll.length ? smallAll : []) { if (R.length >= 20_000) break; for (const row of withTable(q.params, () => v.rowsOf(q.params, q.st))) { const r = valuesOf(row), k2 = vecKey(r); if (!seenRows.has(k2)) { seenRows.add(k2); R.push(r) } } }
        if (!R.length) R.push(...v.rows.slice(0, 3000).map(valuesOf))
        try { if (!m.params.length) R.push(...v.rowsOf({}, run.init({})).map(valuesOf)) } catch { /* (the samples hold the start) */ }
        // (each literal with the rows it is true at, as bits; `id` its atoms, `name` its text under a renaming of the keys)
        const W = Math.ceil(R.length / 32), lits: {lit: Lit, id: string, name: (ren: number[]) => string, reads: number[], bits: Uint32Array, before?: [number, number], state: boolean}[] = []
        const where = (i: number) => { const pl = atoms[i]!.place; return pl === undefined ? [] : covers[pl]! }
        // (an extra atom's key, and its function where it is one)
        const keyOf2 = (i: number) => { const t = atoms[i]!.term; return t?.op === 'var' ? v.vars.indexOf(t.name) : t?.op === 'get' && t.key.op === 'var' ? v.vars.indexOf(t.key.name) : -1 }
        const fnOf = (i: number) => { const t = atoms[i]!.term; return t?.op === 'get' ? t.map : undefined }
        const term = (i: number, ren: number[]) => (atoms[i]!.place !== undefined ? `${atoms[i]!.parts[0]![0].split(AT)[2]}[${where(i).map(k => ren[k]).join()}]` : keyOf2(i) >= 0 ? `${fnOf(i) ?? ''}#${ren[keyOf2(i)]}` : `s${i}`)
        const reads = (i: number) => (keyOf2(i) >= 0 ? [keyOf2(i)] : where(i))
        const add = (lit: Lit, id: string, name: (ren: number[]) => string, rd: number[], holds: (r: Float64Array) => boolean, before?: [number, number]) => {
          const bits = new Uint32Array(W)
          R.forEach((r, k) => { if (holds(r)) bits[k >> 5]! |= 1 << (k & 31) })
          lits.push({lit, id, name, reads: rd, bits, ...(before ? {before} : {}), state: ('at' in lit ? [lit.at.atom] : lit.lin.coef.map(([a]) => a)).some(a => atoms[a]!.place !== undefined || (!atoms[a]!.term && !atoms[a]!.param))})
        }
        const valued = (i: number) => atoms[i]!.place !== undefined && !!valueSort(atoms[i]!.parts[0]![0].split(AT)[2]!)
        for (const i of [...v.atoms.filter(j => !atoms[j]!.int && !atoms[j]!.term), ...modes.filter(mo => !atoms[mo.atom]!.cell && !atoms[mo.atom]!.param).map(mo => mo.atom)]) {
          const vals = [...new Set(R.map(r => r[i]!))].sort((a, b) => a - b)
          // (a value of a key's sort: 0 alone, an order literal below)
          for (const value of valued(i) ? vals.filter(q => q === 0) : vals.length <= 3 ? vals : []) {
            const top = value > 0 && value === vals.at(-1)
            add(top ? {lin: {coef: [[i, -1]], d: -value}} : {at: {atom: i, value}}, `${i}`, ren => `${term(i, ren)}=${value}`, reads(i), r => (top ? r[i]! >= value : r[i] === value))
          }
        }
        // (an ordered sort's keys and values compared: t ≤ u and u < t, of a key and a value or two values)
        const ts = v.atoms.filter(i => keyOf2(i) >= 0 || valued(i))
        const sortOf2 = (i: number) => vf(fnOf(i) ? `V:${fnOf(i)}` : keyOf2(i) >= 0 ? keys[keyOf2(i)]! : valueSort(atoms[i]!.parts[0]![0].split(AT)[2]!)!)
        for (const [a2, i] of ts.entries()) for (const j of ts.slice(a2 + 1)) {
          if (sortOf2(i) !== sortOf2(j)) continue
          // (two keys of one sort are distinct: one before the other)
          const keysOnly = !fnOf(i) && !fnOf(j) && atoms[i]!.place === undefined && atoms[j]!.place === undefined
          for (const [p, q] of [[i, j], [j, i]] as const) for (const d of keysOnly ? [-1] : [0, -1]) add({lin: {coef: [[p, 1], [q, -1]], d}}, `${i}~${j}`, ren => `${term(p, ren)}<=${d}+${term(q, ren)}`, [...reads(p), ...reads(q)], r => r[p]! - r[q]! <= d, keysOnly ? [keyOf2(p), keyOf2(q)] : undefined)
        }
        used.rows += R.length * lits.length
        opts.progress?.('join view', {keys: keys.join(), places: places.length, lits: lits.length, rows: R.length, names: lits.map(l => l.name(keys.map((_, i) => i))).join(' ').slice(0, 900)})
        if (lits.length > 96) continue
        const empty = (b: Uint32Array) => b.every(w => w === 0), and = (a: Uint32Array, b: Uint32Array) => a.map((w, k) => w & b[k]!)
        const none = (ls: number[]) => empty(ls.slice(1).reduce((b, l) => and(b, lits[l]!.bits), lits[ls[0]!]!.bits))
        // (a renaming of a sort's keys moves each literal to the place its keys go to)
        const perms = keys.reduce<number[][]>((acc, s) => acc.flatMap(p => keys.flatMap((t, j) => (t === s && !p.includes(j) ? [[...p, j]] : []))), [[]])
        const canon = (ls: number[]) => perms.map(ren => ls.map(l => lits[l]!.name(ren)).sort().join('&')).sort()[0]!
        const seen = new Set<string>(), found: number[][] = []
        const dfs = (from: number, chosen: number[], size: number, bits?: Uint32Array, most = 400) => {
          for (let j = from; j < lits.length && found.length < most; j++) {
            if (chosen.some(c => lits[c]!.id === lits[j]!.id)) continue
            const now2 = [...chosen, j], b = bits ? and(bits, lits[j]!.bits) : lits[j]!.bits
            if (now2.length < size) { if (!empty(b)) dfs(j + 1, now2, size, b, most); continue }
            if (!empty(b) || now2.some((_, k) => now2.length > 1 && none(now2.filter((__, q) => q !== k)))) continue
            // (a cube reading no state (keys and functions alone) is a fact of the functions' tables, or false: none)
            if (contradicts(now2.map(l => lits[l]!.lit)) || !now2.some(l => lits[l]!.state) || oneSided(now2.map(l => lits[l]!.lit), vi)) continue
            const read = new Set(now2.flatMap(l => lits[l]!.reads)), k2 = canon(now2)
            if (read.size === keys.length && !seen.has(k2)) { seen.add(k2); found.push(now2) }
          }
        }
        // (four literals where a view's literals are few: a ring's order of three keys with what holds there)
        for (let size = 1; size <= (lits.length <= 40 ? 4 : 3); size++) dfs(0, [], size)
        // (where they are more: the four-literal cubes with a chain of three keys of one sort, a < b < c (betweenness, and a
        // cycle's turns of it), the two order literals and any two others, 200 at most; and the doubled patterns below)
        if (lits.length > 40) {
          const at = found.length
          lits.forEach((a, i) => lits.forEach((b, j) => { if (a.before && b.before && a.before[1] === b.before[0] && a.before[0] !== b.before[1] && found.length < at + 200) { const ab = and(a.bits, b.bits); if (!empty(ab)) dfs(0, [i, j], 4, ab, at + 200) } }))
          // (and "two of a pattern are one", DuoAI's: a two-literal pattern some row has, beside its image under a renaming of
          // the view's keys within their sorts (Transfer[z, x] and Ep[x] < z, twice: two live transfers), 200 at most)
          const byName = new Map(lits.map((l, i) => [l.name(keys.map((_, k) => k)), i])), at2 = found.length
          for (const ren of perms.filter(r => r.some((k, i) => k !== i))) for (let i = 0; i < lits.length && found.length < at2 + 200; i++) for (let j = i + 1; j < lits.length && found.length < at2 + 200; j++) {
            const i2 = byName.get(lits[i]!.name(ren)), j2 = byName.get(lits[j]!.name(ren))
            if (i2 === undefined || j2 === undefined || new Set([i, j, i2, j2]).size < 4 || lits[i]!.id === lits[j]!.id || empty(and(lits[i]!.bits, lits[j]!.bits))) continue
            const ls2 = [i, j, i2, j2], b2 = ls2.slice(1).reduce((b, l) => and(b, lits[l]!.bits), lits[i]!.bits)
            if (!empty(b2) || ls2.some((_, k) => none(ls2.filter((__, q) => q !== k))) || contradicts(ls2.map(l => lits[l]!.lit)) || oneSided(ls2.map(l => lits[l]!.lit), vi)) continue
            const read = new Set(ls2.flatMap(l => lits[l]!.reads)), k2 = canon(ls2)
            if (read.size === keys.length && !seen.has(k2)) { seen.add(k2); found.push(ls2) }
          }
        }
        known.set(vi, {R, lits: lits.map(l => l.lit)})
        out.push(...found.map(ls => formOf(ls.map(l => lits[l]!.lit), vi)))
      }
      const made0 = out.filter((f, i) => !set.some(g => textOf(g) === textOf(f)) && out.findIndex(g => textOf(g) === textOf(f)) === i)
      return env.GDP_POOL !== '0' ? dataFilter(made0) : made0
      // The pool's data filter (DuoAI's junk killed by data before any solver call; research/protocols/engine/DESIGN.md,
      // gen/pool): each cube asked at every reachable state of larger instances, one more element of every sort and then
      // of each sort alone, within a budget of its own (3 s, at most a tenth of what is left: half an instance's share its
      // BFS, uncut, the rest reading its states); a cube some row of such a state is in is no law, and goes
      function dataFilter(pool: Form[]): Form[] {
        // (its budget scales with the small instance's own search: ten times it, 3 s at least, 15 s and a quarter of what is
        // left at most; ring's one more node needs about 8 s, and a slow container that reads fewer of its states kills
        // fewer cubes: ring's pool past 44 costs its first round 24–36 s, not 18–20, and the wall (DESIGN.md, gen/laneA))
        const t5 = performance.now(), until5 = t5 + Math.min(Number(env.GDP_POOL_MS ?? 15_000), (wallUntil - t5) / 4, Math.max(3000, 10 * baseMs))
        const litAt = (l: Lit, r: Env) => ('at' in l ? valueOf(atoms[l.at.atom]!, r) === l.at.value : l.lin.coef.reduce((s2, [i, c]) => s2 + c * valueOf(atoms[i]!, r), 0) <= l.lin.d)
        const plans: ((q: string) => number)[] = [() => 1, ...(ss.length > 1 ? ss.map(s2 => (q: string) => (q === s2 ? 1 : 0)) : [])]
        let live = pool, states = 0
        for (const [k, grow] of plans.entries()) {
          if (!live.length || performance.now() > until5 - 100) break
          const r = instance(grow, (until5 - performance.now()) / (plans.length - k) / 2, seeded(29 + k)), killed = new Set<Form>()
          const byView = new Map<number, Form[]>()
          for (const f of live) byView.set(f.view!, [...(byView.get(f.view!) ?? []), f])
          for (const q of [...r.small, ...r.others]) {
            if (performance.now() > until5) break
            states++
            for (const [vi, fs] of byView) {
              const alive = fs.filter(f => !killed.has(f))
              if (!alive.length) continue
              const rows = withTable(q.params, () => views[vi]!.rowsOf(q.params, q.st, true))
              for (const f of alive) { let near = 0; for (const row of rows) { let off = 0; for (const l of f.cube!) if (!litAt(l, row) && ++off > 1) break; if (off === 0) { killed.add(f); break } if (off === 1) near++ } if (near) nearMiss.set(f, (nearMiss.get(f) ?? 0) + near) }
            }
          }
          live = live.filter(f => !killed.has(f))
          // (no instance after one that kills nothing; GDP_POOL_STOP=0 runs them all)
          if (env.GDP_POOL_STOP !== '0' && k > 0 && !killed.size) break
        }
        opts.progress?.('join pool', {made: pool.length, left: live.length, states, ms: Math.round(performance.now() - t5)})
        return live
      }
    }
    // The control refined on demand (as CEGAR refines its predicates, here read off the rule): a counterexample to a
    // caller's law that the set allows and nothing rules out lies among the samples of its control state. A level of a
    // value the rule compares with a constant (the first, of the values the laws read first, whose levels keep the control
    // states within joinKeys) whose part of those samples and of the states joined in leaves it out (past its hull or a
    // bound, or with no state there at all) becomes a control value, and every state is joined again.
    const refine = (p: Point): boolean => { const recent = [p, ...negs.slice(-8)]; used.rows += recent.length; const ok = spaces.some(sp => sp.refine(recent)); if (ok) { stood.clear(); reached.length = 0 } return ok }
    // The engine, after a join that found nothing, on a rule of keyed maps whose scalars take few values (no counters;
    // research/protocols/engine/DESIGN.md): the template's cubes (DuoAI's ∀ candidates, research/protocols/enum/
    // DESIGN.md) read off the small instance, those the caller's and the kinds' laws don't imply; then Houdini, the
    // caller's laws first, every cube assumed: the CDCL search's refutation (its core settles the goal while the laws it
    // read stay) or model, else the proof path's. A model the interpreter reads as a real step out of the goal drops its
    // cube; one out of the caller's law from a state no small state is has its diagrams blocked as cubes, the caller asked
    // again first (IC3's order); the caller's law unproven otherwise ends it. A round with nothing real drops the
    // unsettled. The set is then proven, its trees kept. Later rounds leave a sums pass its reserve (core/dsl.ts's:
    // decentralized lock's) while the caller's law fails from the set.
    const engine = () => {
    if (sorts && callerLaws.some(l => l.keys?.length) && now() < until && !stop()) {
      opts.progress?.('join engine', {wall: Math.round(performance.now() - t0)})
      // (a sums pass's reserve where one follows: 10 s, or a quarter of what is left where less is)
      const v0 = views.length, reserve = rule?.withMapSums() ? Math.min(10_000, (wallUntil - performance.now()) / 4) : 0
      const implied = (f: Form) => {
        const v = views[f.view!]!, sk = {vars: Object.fromEntries(v.vars.map(k => [k, x(`${k}#`)])), maps: {}, flags: {}}, hyps = [substC(v.frame, sk), not(substC(condOf(f), sk))]
        for (const l of given) {
          const b = [l.forall, ...(l.keys ?? [])].filter((q): q is string => !!q)
          if (v.vars.length ** b.length > 64) return false
          for (const t of b.reduce<string[][]>(acc => acc.flatMap(t2 => v.vars.map(k => [...t2, k])), [[]])) hyps.push(substC(l.holds, {vars: Object.fromEntries(b.map((q, k) => [q, sk.vars[t[k]!]!])), maps: {}, flags: {}}))
        }
        return 'tree' in withWall(wallUntil, () => budgeted(joinQueryMs / 8, until2 => grow({name: 'implied', hyps}, new Map(), {nodes: 0, until: until2})))
      }
      // (the cubes that read a map the caller's laws read first)
      const callerMaps = new Set(laws.flatMap(l => [...JSON.stringify(l.holds).matchAll(/"map":"([^"]+)"/g)].map(q => q[1]!)))
      const near = (f: Form) => (f.cube!.some(l => atomsIn(formOf([l])).some(i => callerMaps.has(atoms[i]!.parts[0]![0].split(AT)[2] ?? ''))) ? 0 : 1)
      // (the rounds over the data-filtered pool cut to its minimal cubes)
      const minPool = env.GDP_POOL !== '0' ? minimal(enumerated()) : {kept: enumerated(), by: new Map<Form, Form[]>()}, made = minPool.kept
      const tEngine = performance.now()
      let cubes: Form[] = []
      // (in turn by the maps a cube reads, those reading the caller's first: one of each kind before a second of any; in
      // a kind, the fewer literals first (DuoAI's minimal clauses), then the cube over more distinct keys (the law its
      // diagonal case is a case of))
      const mapsOfCube = (f: Form) => [...new Set(f.cube!.flatMap(l => atomsIn(formOf([l])).map(i => atoms[i]!.parts[0]![0].split(AT)[2] ?? '')))].sort().join()
      const byMaps = new Map<string, Form[]>()
      const width2 = (f: Form) => views[f.view!]!.vars.length
      for (const f of [...made].sort((a, b) => near(a) - near(b) || a.cube!.length - b.cube!.length || width2(b) - width2(a))) { const k2 = mapsOfCube(f); byMaps.set(k2, [...(byMaps.get(k2) ?? []), f]) }
      // (each turn the kinds in order of their own first cube: its fewer literals, then whether it reads the caller's maps)
      const kinds2 = [...byMaps.values()].sort((a, b) => a[0]!.cube!.length - b[0]!.cube!.length || near(a[0]!) - near(b[0]!)), turns: Form[] = []
      for (let i = 0; turns.length < made.length; i++) for (const fs of kinds2) if (fs[i]) turns.push(fs[i]!)
      // (every cube of at most two literals first, DuoAI's minimal clauses, the turns' order kept within each part)
      turns.sort((a, b) => Math.min(a.cube!.length, 3) - Math.min(b.cube!.length, 3))
      // (round 0 the minimal cubes, at most 24, or the whole enumeration where it is 16 or fewer; the rest by relevance to
      // the counterexamples, IC3's order)
      const whole = made.length <= 16
      for (const f of turns) { if (cubes.length >= 24 || stop()) break; if ((whole || f.cube!.length <= 2) && !names.has(textOf(f)) && !implied(f)) cubes.push(f) }
      opts.progress?.('join enumerated', {views: views.length - v0, cubes: cubes.length, ms: Math.round(performance.now() - t0)})
      opts.progress?.('join cubes', {cubes: cubes.map(textOf).join(' | ')})
      opts.progress?.('join made', {cubes: made.map(textOf).join(' | ')})
      // (a goal's proof within the search's own end, on the cost model's clock: a counted search inside it keeps the end)
      const within = <T>(endWall: number, f: () => T): T => withWall(endWall, () => counted(fullRate, () => withDeadline(clock() + Math.max(0, endWall - performance.now()), f), true))
      // (a model's values past the rule's constants renamed onto small ones in order, a gap kept up to 64: the step then
      // runs at every key, and the model's equalities, order, +1 and comparisons with the constants are kept)
      const top = Math.max(1024, ...[...JSON.stringify([m.step, m.assume ?? null, m.pre ?? null]).matchAll(/"value":(\d+)/g)].map(q => Number(q[1])))
      const smallOf = (w: Record<string, number>): Record<string, number> => {
        const big = [...new Set(Object.values(w).filter(v => v > top))].sort((a, b) => a - b)
        if (!big.length) return w
        const to = new Map<number, number>()
        big.forEach((v, i) => to.set(v, i ? to.get(big[i - 1]!)! + Math.min(64, v - big[i - 1]!) : top + 1))
        return Object.fromEntries(Object.entries(w).map(([c, v]) => [c, to.get(v) ?? v]))
      }
      const realCti = (w0: Record<string, number>, f: Form | undefined, others: Form[]) => { const w = smallOf(w0); return withFnsOf(w, () => {
        const {params, st} = stateOf(w), read = new Set([...others, f].map(g => g?.view))
        // (a model's cells past the keys the interpreter steps at every key, a million, left out)
        for (const cells of Object.values(st.maps)) for (const k of [...cells.keys()]) if (k > 1_000_000) cells.delete(k)
        const at = (s2: State): Point => ({scalar: withTerms({...params, ...s2.scalars}, s2), cells: [], views: views.map((v, i) => (read.has(i) ? v.rowsOf(params, s2) : []))})
        let post: State
        if (performance.now() > wallUntil) return false
        try { post = run.step(params, st, requestOf(w)); stepNamed(st, post) } catch { return false }
        if (performance.now() > wallUntil) return false
        const before = at(st)
        if (!others.every(g => holdsAt(g, before))) return false
        lastPre = {params, st, w}
        if (!f) return breaks(params, post, st, requestOf(w))
        return (at(post).views[f.view!] ?? []).some(r => judged(f, r) && !holdsRow(f, r))
      }) }
      // (a cube false at a start: its start goal's model, judged at the interpreter's own start at the model's params (a
      // start is reachable, so it is a real counterexample); such a cube is not asked, nor kept)
      const startBad = new Map<Form, boolean>()
      // (the law at the model's keys, at the interpreter's start for the model's params, with the model's function values
      // where they keep the facts at those keys)
      const badAtStart = (f: Form, w0: Record<string, number>) => { const w = smallOf(w0), l = lawFor(f); return withFnsOf(w, () => { const {params} = stateOf(w); try {
        const st = run.init(params), env2: Env = {...params, ...st.scalars}
        for (const k of [l.forall, ...(l.keys ?? [])]) if (k) env2[k] = w[k] ?? w[`${k}#`] ?? 0
        const vals = [...new Set([l.forall, ...(l.keys ?? [])].filter((k): k is string => !!k).map(k => env2[k]!))]
        for (const fct of m.facts ?? []) { const b = [fct.forall, ...(fct.keys ?? [])].filter((q): q is string => !!q); if (vals.length ** b.length > 4096) return false
          for (const t of b.reduce<number[][]>(acc => acc.flatMap(t2 => vals.map(v => [...t2, v])), [[]])) if (!evalC(fct.holds, {...env2, ...Object.fromEntries(b.map((q, k) => [q, t[k]!]))}, st, m)) return false }
        return !evalC(l.holds, env2, st, m)
      } catch { return false } }) }
      const atStart = (f: Form): boolean => {
        let b = startBad.get(f)
        if (b === undefined) {
          const ls2 = [...given, lawFor(f)], g = obligations(forLaws(ls2).m, ls2, {}, given.length)[0]!
          const q = budgeted(joinQueryMs / 32, until2 => growCdcl(g, new Map(), {nodes: 0, until: until2}, {model: true, wall: wallUntil})) as Refuted
          b = !('tree' in q) && q.stuck === 'sat' && !!q.witness && badAtStart(f, q.witness)
          startBad.set(f, b)
        }
        return b
      }
      // (a counterexample's diagram (UPDR's, IC3PO's): in each template view, a row of its state no reachable small state's
      // row is, as the literals true there, generalized by taking out each literal while no small state's row is inside;
      // blocked as a law ¬diagram, at most four a counterexample)
      let lastPre: {params: Env, st: State, w: Record<string, number>} | undefined
      const reachedRows = new Map<number, Set<string>>()
      const diagrams = (pre: {params: Env, st: State}): Form[] => {
        const out2: Form[] = []
        for (const [vi, k] of known) {
          const seenR = reachedRows.get(vi) ?? new Set(k.R.map(vecKey)); reachedRows.set(vi, seenR)
          // (a model names some cells: the literals over those alone)
          for (const row of views[vi]!.rowsOf(pre.params, pre.st)) {
            const r = valuesOf(row)
            if (!unnamed.get(row) && seenR.has(vecKey(r))) continue
            let c = k.lits.filter(l => litHolds(l, r) && judged(formOf([l], vi), row))
            if (!c.length || k.R.some(y => inCube(c, y))) continue
            for (const l of [...c]) { const c2 = c.filter(x2 => x2 !== l); if (c2.length && !k.R.some(y => inCube(c2, y))) c = c2 }
            if (c.length <= 5 && !k.R.some(y => inCube(c, y)) && !oneSided(c, vi)) out2.push(formOf(c, vi))
            if (out2.length >= 4) return out2
          }
        }
        return out2
      }
      // ∀∃ (DuoAI's): where the caller's counterexample is a reachable small state's row in every view, a law
      // A → ∃y. B(y): A the scalars' literals (or none), B one or two literals of a one-key view at y, true at every small
      // state (A there, some key has B), B not at every key. Its witness a ghost (a value at the start, 0, and after
      // each step: an input where an update of a map B reads takes its branch, else the value before), the first that
      // holds along random runs of the small instance; then the ghost a state variable of the machine Houdini reads, its
      // law a goal, and the final proof the ∃ law with that witness (core/exists.ts's).
      type Ghost = {name: string, start: E, step: E, plain: Law, some: Law}
      let ghost: Ghost | undefined, ghosts: Ghost[] | undefined
      const ghosted = new WeakMap<Machine, Machine>()
      const withGhost = (mm: Machine): Machine => {
        if (!ghost) return mm
        let g = ghosted.get(mm)
        if (!g) { g = {...mm, state: {...mm.state, [ghost.name]: ghost.start}, step: {...mm.step, state: {...mm.step.state, [ghost.name]: ghost.step}}}; ghosted.set(mm, g) }
        return g
      }
      const ghostsOf = (): Ghost[] => {
        const out3: Ghost[] = []
        const states = samples.slice(0, 3000), conds = new Map<string, C>()
        for (const w of Object.values(m.step.maps ?? {})) walk(w.value, o => { if (o.op === 'if' && conds.size < 16) conds.set(JSON.stringify(o.c), o.c as C) })
        for (const [vi, k] of known) {
          const v = views[vi]!
          if (v.vars.length !== 1 || stop()) continue
          const keyed = (l: Lit) => atomsIn(formOf([l])).some(i => atoms[i]!.place !== undefined || !!atoms[i]!.term)
          const As = [[], ...k.lits.filter(l => !keyed(l)).map(l => [l])], Bs0 = k.lits.filter(keyed)
          const off = (l: Lit) => !('at' in l) || l.at.value !== 0
          const Bs = [...Bs0.map(l => [l]), ...Bs0.flatMap((l, i) => Bs0.slice(i + 1).map(l2 => [l, l2]))].filter(b => !contradicts(b) && b.some(off))
          const rowsAt = states.map(q => v.rowsOf(q.params, q.st).map(valuesOf))
          for (const A of As) for (const B of Bs) {
            if (out3.length >= 6) return out3
            let some2 = false, notAll = false, ok = true
            for (const rows of rowsAt) {
              if (!rows.length || !inCube(A, rows[0]!)) continue
              some2 = true
              if (!rows.some(r => inCube(B, r))) { ok = false; break }
              if (!rows.every(r => inCube(B, r))) notAll = true
            }
            if (!ok || !some2 || !notAll) continue
            const y = `some$enum${vi}`, sub = {vars: {[v.vars[0]!]: x(y)}, maps: {}, flags: {}}
            const holds = any(...(A.length ? [condOf(formOf(A, vi))] : []), all(substC(v.frame, sub), substC(not(condOf(formOf(B, vi))), sub)))
            const name = `${A.length ? textOf(formOf(A, vi)) + ' else ' : ''}some ${textOf(formOf(B, vi))}`
            // (the witness: along random runs of the small instance, the first ghost the law holds at)
            witness: for (const c of [all(), ...conds.values()]) for (const i of m.inputs) {
              const step: E = {op: 'if', c, then: x(i), else: x(y)}
              let held2 = 0, bad = false
              for (const {params, combos} of smallReq) for (let walk2 = 0; walk2 < 40 && !bad; walk2++) {
                let st: State, g = 0
                try { st = run.init(params) } catch { break }
                for (let d = 0; d < 30 && !bad; d++) {
                  const input = combos[rand(combos.length)]!
                  try {
                    if (!allowed(m, run, params, st, input)) continue
                    const env2: Env = {...params, ...st.scalars, ...Object.fromEntries(m.inputs.map(i2 => [i2, input[i2] as number])), [y]: g}, seen2 = carriedView(m, st, input)
                    for (const [fl, c2] of Object.entries(m.step.flags ?? {})) env2[`?${fl}`] = evalC(c2, env2, seen2, m) ? 1 : 0
                    const next = run.step(params, st, input)
                    g = evalE(step, env2, seen2, m); st = next
                    if (evalC(holds, {...params, ...st.scalars, [y]: g}, st, m)) held2++; else bad = true
                  } catch { continue }
                }
              }
              if (bad || held2 < 50) continue
              out3.push({name: y, start: n(0), step, plain: {name, holds}, some: {name, holds, some: [y], witness: {ghost: {[y]: {start: n(0), step}}}}})
              break witness
            }
          }
        }
        return out3
      }
      // (a goal the CDCL search refuted, by the laws its core read: settled while each is still in the set, Houdini's
      // cores)
      // (`stands`: the goals proven since the set last lost a law; a set that only grows keeps their proofs)
      // (a goal's proof had every cube in the set as it stood: a drop takes back the proofs since the dropped cube came in)
      const settled = new Map<string, string[]>(), kept2 = new Set<Form>(), stands = new Set<string>(), provenAt = new Map<string, number>(), addedAt = new Map<Form, number>()
      const unstand = (gs: Iterable<Form>) => { const r = Math.min(...[...gs].map(g => addedAt.get(g) ?? 0)); for (const [nm, at] of provenAt) if (at >= r) { stands.delete(nm); provenAt.delete(nm) } }
      let held = false
      // (the counterexamples so far, each a state the set must rule out, the caller's and then the cubes' kept unsure (PDR's
      // obligations): the enumeration's cubes false there are the relevant ones, the most of the caller's first, then the
      // most of the cubes'; and the goals a round can afford, a quarter of what is left at the last round's cost a goal)
      type Pre = {params: Env, st: State, w: Record<string, number>}
      const pres: Pre[] = [], subs: Pre[] = [], preAt = new WeakMap<object, Point>()
      let perGoal = 0, houdinied = false
      const engineStart = performance.now()
      const ptOf = (q: Pre) => { let pt = preAt.get(q); if (!pt) { pt = withFnsOf(q.w, () => pointOf(q.params, q.st)); preAt.set(q, pt) } return pt }
      // (a kernel model's state, its values past the rule's constants renamed small, its cells past a million left out)
      const preOf = (wit: Record<string, number>): Pre => { const w2 = smallOf(wit); return withFnsOf(w2, () => { const {params, st} = stateOf(w2); for (const cells of Object.values(st.maps)) for (const k of [...cells.keys()]) if (k > 1_000_000) cells.delete(k); return {params, st, w: w2} }) }
      // (the cubes dropped, never asked again: false at a start)
      const dead = new Set<string>()
      // (IC3's frames: a cube whose relative induction fails without a counterexample from a start is not dropped but
      // pending: out of the set the others assume, asked again (pushed) with the set and itself once the set has changed
      // since its last try, back in the set where that proves; twice at most)
      const pending = new Set<Form>(), tried = new Map<Form, string>(), backs = new Map<Form, number>()
      const versionOf = () => cubes.map(textOf).sort().join('|')
      // (what blocks a counterexample's state: the enumeration's minimal cubes false there (the antichain is the
      // generalization), or that may be (cells the model leaves unnamed), four at most (the frames' pushes prune the wrong
      // ones; distributed's needed blockers ranked 2nd to 4th): the false first, then those false at
      // the most of the counterexamples' states so far, then the fewest literals; else its diagrams)
      const seenCtis: Pre[] = []
      // (every cube ranked in the top eight at some counterexample: the pool a fixpoint's Houdini runs over)
      const pool = new Set<Form>()
      const blockers = (pre: Pre): Form[] => {
        const pt = ptOf(pre), pts = (seenCtis.push(pre), seenCtis.slice(-16).map(ptOf)), bs: Form[] = []
        const scored = made.filter(g => !dead.has(textOf(g)) && !pending.has(g)).map(g => ({g, f: !holdsAt(g, pt) ? 2 : mayFail(g, pt) ? 1 : 0})).filter(q => q.f).map(({g, f}) => ({g, k: f * 1024 + pts.filter(p2 => !holdsAt(g, p2)).length}))
        const ranked = scored.sort((a, b) => b.k - a.k || a.g.cube!.length - b.g.cube!.length || width2(b.g) - width2(a.g))
        for (const {g} of ranked.slice(0, 8)) pool.add(g)
        for (const {g} of ranked) { if (bs.length >= 4) break; if (!bs.some(h => textOf(h) === textOf(g)) && !atStart(g)) bs.push(g) }
        return bs.length ? bs : withFnsOf(pre.w, () => diagrams(pre)).filter(g => !dead.has(textOf(g)) && !atStart(g))
      }
      // (a cube that may be false at a counterexample: at a row where it reads cells the model doesn't name, every literal
      // the model does name in its pattern)
      const mayFail = (g: Form, pt: Point) => g.view !== undefined && (pt.views[g.view] ?? []).some(r => !judged(g, r) && g.cube!.every(l => { const h = formOf([l], g.view); return !judged(h, r) || !holdsRow(h, r) }))
      const relevant = (room: number, kept: Form[]): Form[] => {
        if (room <= 0 || !pres.length && !subs.length) return []
        const have = new Set([...kept.map(textOf), ...dead, ...[...pending].map(textOf)]), pts = pres.map(ptOf), sts = subs.slice(-32).map(ptOf)
        const scored = made.filter(g => !have.has(textOf(g)) && !names.has(textOf(g))).map(g => ({g, k: pts.filter(pt => !holdsAt(g, pt)).length * 4096 + pts.filter(pt => mayFail(g, pt)).length * 64 + sts.filter(pt => !holdsAt(g, pt)).length})).filter(q => q.k > 0)
        // (ties: the fewer literals, then the fewer keys, the more particular law)
        scored.sort((a, b) => b.k - a.k || a.g.cube!.length - b.g.cube!.length || width2(a.g) - width2(b.g))
        const out3: Form[] = []
        for (const {g} of scored) { if (out3.length >= room || stop()) break; if (!implied(g) && !atStart(g)) out3.push(g) }
        return out3
      }
      // (minimal implication, DuoAI's: a cube B goes where a kept cube A's law implies B's law: A's keys sent into B's one
      // to one within each sort, each literal of A entailed by one of B's (the same; the same sum at a bound no larger; a
      // value at least A's bound); `by`, B's kept impliers)
      function minimal(pool: Form[]): {kept: Form[], by: Map<Form, Form[]>} {
        const letters = ['x', 'y', 'z', 'w', 'u'], tok = /\b([xyzwu])\b/g
        type L2 = {sum: string, d: number, at?: number}
        const litsOf = (f: Form, ren: number[]): L2[] => f.cube!.map(l => {
          const nm = (i: number) => atoms[i]!.name.replace(tok, (_, c: string) => letters[ren[letters.indexOf(c)]!]!)
          return 'at' in l ? {sum: nm(l.at.atom), d: 0, at: l.at.value} : {sum: l.lin.coef.map(([i, c]) => `${c}*${nm(i)}`).sort().join('+'), d: l.lin.d}
        })
        const entails = (b: L2, a: L2) => (a.at !== undefined ? b.at !== undefined && b.sum === a.sum && b.at === a.at
          : b.at !== undefined ? a.sum === `-1*${b.sum}` && -b.at <= a.d : b.sum === a.sum && b.d <= a.d)
        const sortsOf = (f: Form) => viewSorts.get(f.view!) ?? []
        const maps2 = (sa: string[], sb: string[]): number[][] => sa.reduce<number[][]>((acc, s2) => acc.flatMap(r => sb.flatMap((t2, j) => (t2 === s2 && !r.includes(j) ? [[...r, j]] : []))), [[]])
        const own = new Map(pool.map(f => [f, litsOf(f, sortsOf(f).map((_, i) => i))]))
        const implies = (a: Form, b: Form) => a !== b && maps2(sortsOf(a), sortsOf(b)).some(ren => { const la = litsOf(a, ren), lb = own.get(b)!; return la.every(x2 => lb.some(y2 => entails(y2, x2))) })
        const order = [...pool].sort((p2, q2) => p2.cube!.length - q2.cube!.length || sortsOf(p2).length - sortsOf(q2).length)
        const kept: Form[] = [], by = new Map<Form, Form[]>()
        for (const b of order) if (!kept.some(a => implies(a, b))) kept.push(b)
        for (const b of pool) if (!kept.includes(b)) by.set(b, kept.filter(a => implies(a, b)))
        return {kept: pool.filter(f => kept.includes(f)), by}
      }
      // The top-down phase (DuoAI's, research/protocols/engine/DESIGN.md gen/ring2, gen/ring3): the filtered minimal
      // pool, not given, not implied by the caller's laws, not false at a start; Houdini, each round every cube's goal with
      // the others assumed (decideLaw, a short cap first, the undecided again at a longer one only where the round would
      // end with no drop), every failure dropped at once, a cube a dropped one implied back where nothing kept implies it,
      // and only the goals whose proofs read a dropped cube asked again; then the caller's goals, the cone (their support,
      // closed under each cube's; a cube with no known support asked with the cone alone, a model's pre-state bringing in
      // the fixpoint's cubes false there), and prove() of the cone. A fixpoint that doesn't prove leaves the rounds below.
      // (by default where the pool is past what the rounds' first round takes, 24, and Houdini can afford it, 64: GDP_TD=1
      // always, GDP_TD=0 never)
      if ((env.GDP_TD === '1' || (env.GDP_TD !== '0' && made.length > 24 && made.length <= 64)) && !stop()) withTrees(() => withStrict(() => {
        const T0 = performance.now(), ph = (o: Record<string, unknown>) => opts.progress?.('join td', {...o, td: Math.round(performance.now() - T0), wall: Math.round(performance.now() - t0)})
        const by = minPool.by, q1 = Number(env.GDP_TD_Q1 ?? joinQueryMs / 8), q2 = Number(env.GDP_TD_Q2 ?? q1)
        ph({phase: 'start', made: made.length, before: Math.round(tEngine - t0)})
        const fresh = (f: Form) => !names.has(textOf(f)) && !dead.has(textOf(f)) && !implied(f) && !atStart(f)
        let hs = made.filter(fresh)
        ph({phase: 'pool', cubes: hs.length})
        const uses = new Map<string, string[]>(), undecided = new Set<Form>(), reasked = new Set<Form>()
        let asked = new Set<Form>(hs)
        for (let r = 0; hs.length && performance.now() < wallUntil && !stop(); r++) {
          const ls = [...given, ...hs.map(lawFor)], mm = forLaws(ls).m, failed = new Set<Form>(), tr = performance.now(), at = new Map(hs.map((f, i) => [f, given.length + i]))
          const ask = (f: Form, ms2: number) => {
            if (performance.now() > wallUntil) { undecided.add(f); return }
            const dl = within(Math.min(wallUntil, performance.now() + ms2), () => decideLaw(mm, ls, at.get(f)!))
            if (!dl) { undecided.add(f); return }
            undecided.delete(f)
            if (dl.proven) uses.set(textOf(f), dl.uses); else { failed.add(f); uses.delete(textOf(f)) }
          }
          // (a goal left undecided is kept, as optimistic Houdini keeps it, and asked again only once a round has dropped
          // nothing: a drop's round would ask it again at the same cap for nothing most rounds)
          let todo = r === 0 ? hs : hs.filter(f => asked.has(f) && !undecided.has(f))
          // (the goals with the most near misses in the larger instances first, and a failure dropped at
          // once, the round's later goals asked with the smaller set)
          if (env.GDP_TD_ORDER !== '0') {
            todo = [...todo].sort((a2, b2) => (nearMiss.get(b2) ?? 0) - (nearMiss.get(a2) ?? 0))
            let cur = hs.filter(f => !failed.has(f))
            for (const f of todo) {
              if (performance.now() > wallUntil) { undecided.add(f); continue }
              const ls2 = [...given, ...cur.map(lawFor)], dl = within(Math.min(wallUntil, performance.now() + q1), () => decideLaw(mm, ls2, given.length + cur.indexOf(f)))
              if (!dl) { undecided.add(f); continue }
              undecided.delete(f)
              if (dl.proven) uses.set(textOf(f), dl.uses); else { failed.add(f); uses.delete(textOf(f)); cur = cur.filter(g => g !== f) }
            }
          } else for (const f of todo) ask(f, q1)
          let second = 0
          // (each once: one still undecided then is kept, the cone's proof deciding)
          if (!failed.size && undecided.size) for (const f of hs.filter(g => undecided.has(g) && !reasked.has(g))) { second++; reasked.add(f); ask(f, Math.max(q1, q2)) }
          ph({phase: 'round', round: r, cubes: hs.length, asked: todo.length, second, failed: failed.size, undecided: undecided.size, ms: Math.round(performance.now() - tr)})
          if (!failed.size) break
          for (const f of failed) dead.add(textOf(f))
          const gone = new Set([...failed].map(textOf)), inSet = new Set(hs.filter(f => !failed.has(f)))
          const back = [...by].filter(([b, as]) => !inSet.has(b) && !dead.has(textOf(b)) && as.some(a => failed.has(a)) && !as.some(a => inSet.has(a))).map(([b]) => b).filter(fresh)
          hs = [...inSet, ...back]
          // (only the goals whose proofs read a dropped cube, the new ones, and the undecided are asked again)
          asked = new Set([...back, ...hs.filter(f => !uses.has(textOf(f)) || uses.get(textOf(f))!.some(u => gone.has(u)))])
        }
        if (stop() || performance.now() > wallUntil) { ph({phase: 'out of time'}); return }
        // (GDP_TD_DECIDED=1: the cubes Houdini left undecided out before the caller's goals: the cone of decided cubes)
        if (env.GDP_TD_DECIDED === '1') hs = hs.filter(f => !undecided.has(f))
        const tc = performance.now(), need = new Set<string>()
        const callerFrom = (): boolean => {
          need.clear()
          const ls = [...given, ...hs.map(lawFor), ...(ghost ? [ghost.plain] : [])], mm = withGhost(forLaws(ls).m)
          for (const l of [...laws, ...(ghost ? [ghost.plain] : [])]) {
            const dl = within(Math.min(wallUntil, performance.now() + joinQueryMs), () => decideLaw(mm, ls, ls.findIndex(k => k.name === l.name)))
            if (!dl?.proven) return false
            for (const u of dl.uses) need.add(u)
          }
          return true
        }
        let callerOk = callerFrom()
        if (!callerOk && !ghosts) { ghosts = ghostsOf(); for (ghost = ghosts.shift(); ghost && !(callerOk = callerFrom()); ghost = ghosts.shift()); }
        const close = () => { for (const todo = [...need]; todo.length;) for (const u of uses.get(todo.pop()!) ?? []) if (!need.has(u)) { need.add(u); todo.push(u) } }
        close()
        for (let it = 0; callerOk && it < 8 && performance.now() < wallUntil && !stop(); it++) {
          const inCone = hs.filter(f => need.has(textOf(f))), open = inCone.filter(f => !uses.has(textOf(f)))
          if (!open.length) break
          const ls = [...given, ...inCone.map(lawFor), ...(ghost ? [ghost.plain] : [])], mm = withGhost(forLaws(ls).m)
          let grew = 0, settledN = 0
          for (const f of open) {
            if (performance.now() > wallUntil) break
            const dl = within(Math.min(wallUntil, performance.now() + q2), () => decideLaw(mm, ls, ls.findIndex(k => k.name === textOf(f))))
            if (dl?.proven) { uses.set(textOf(f), dl.uses); settledN++; continue }
            if (!dl || !dl.goal.endsWith('@step')) continue
            const pt = ptOf(preOf(dl.witness))
            for (const g of hs) if (!need.has(textOf(g)) && !holdsAt(g, pt)) { need.add(textOf(g)); grew++ }
          }
          close()
          if (!grew && !settledN) break
        }
        let cut = hs.filter(f => need.has(textOf(f)))
        ph({phase: 'cone', fixpoint: hs.length, undecided: undecided.size, caller: callerOk ? 1 : 0, cone: cut.length, undecidedInCone: cut.filter(f => undecided.has(f)).length, ms: Math.round(performance.now() - tc)})
        if (callerOk) for (let k = 0; k < 24 && performance.now() < wallUntil && !stop(); k++) {
          const t2 = performance.now(), setLaws = [...laws, ...cut.map(lawFor), ...(ghost ? [ghost.some] : [])]
          const h0 = memoHits.n, m0 = memoHits.miss
          let v = within(t0 + ms, () => prove(setLaws, true))
          const hits = memoHits.n - h0, misses = memoHits.miss - m0, fastMs = Math.round(performance.now() - t2), fast = v.proven && v.checked ? 1 : 0, fastAt = String(v.goal ?? '').slice(0, 100)
          if (!(v.proven && v.checked)) v = within(t0 + ms, () => prove(setLaws))
          const at = String(v.goal ?? ''), g = v.proven && v.checked ? undefined : cut.find(c => at.startsWith(`${textOf(c)} @`))
          ph({phase: 'prove', cubes: cut.length, proven: v.proven && v.checked ? 1 : 0, ms: Math.round(performance.now() - t2), fastMs, fast, hits, misses, setKey: memoHits.setKey, tdKey: env.GDP_MEMO_TRACE ? machineKey(forLaws([...given, ...cut.map(lawFor)]).m) : '', diff: env.GDP_MEMO_TRACE ? ((x: string, y: string) => { let i = 0; while (i < x.length && x[i] === y[i]) i++; return `${i}: ${x.slice(Math.max(0, i - 60), i + 60)} || ${y.slice(Math.max(0, i - 60), i + 60)}` })(JSON.stringify(forLaws([...given, ...cut.map(lawFor)]).m), memoHits.setJson) : '', fastAt, at: at.slice(0, 100)})
          if (v.proven && v.checked) { why = 'inductive'; cone = cut; enumProof = v; enumSome = ghost ? [ghost.some] : []; cubes = cut; break }
          if (!g) break
          cut = cut.filter(c => c !== g)
        }
      }))
      for (let round = 0, over = false; !over && cubes.length && !stop(); round++) withTrees(() => {
        // (one cube once: a cube in the set is not pending, and a text in the set once)
        cubes = cubes.filter((g, i) => !atStart(g) && cubes.findIndex(h => textOf(h) === textOf(g)) === i)
        for (const g of cubes) if (pending.has(g) || [...pending].some(h => textOf(h) === textOf(g))) for (const h of [...pending]) if (textOf(h) === textOf(g)) pending.delete(h)
        for (const g of cubes) if (!addedAt.has(g)) addedAt.set(g, round)
        const stand = (nm: string) => { stands.add(nm); provenAt.set(nm, round) }
        // (DuoAI's: the Houdini fixpoint of the relevant candidates, once, with 40% of the engine's time left: the set, the pending cubes and every cube a
        // counterexample ranked in its top eight, a cube the fast proof fails at dropped (the usual proof where it fails at
        // a cube the rounds proved), until the whole proves or the time is out)
        if (!houdinied && !enumProof && performance.now() > wallUntil - 0.4 * (wallUntil - engineStart)) {
          houdinied = true
          let hs = [...new Map([...cubes, ...pending, ...pool].filter(g => !dead.has(textOf(g)) && !atStart(g)).map(g => [textOf(g), g])).values()]
          for (let k = 0; k < 200 && hs.length && performance.now() < wallUntil && !stop(); k++) {
            const t2 = performance.now(), hl = [...laws, ...hs.map(lawFor), ...(ghost ? [ghost.some] : [])]
            let v = within(t0 + ms, () => prove(hl, true))
            const at0 = String(v.goal ?? ''), g0 = v.proven && v.checked ? undefined : hs.find(c => at0.startsWith(`${textOf(c)} @`))
            // (or at a law the caller gave, a kind's: no cube to blame, so the usual proof's verdict)
            if (!(v.proven && v.checked) && (g0 ? at0.endsWith('@step') && stands.has(lawFor(g0).name) : true)) v = within(t0 + ms, () => prove(hl))
            const at = String(v.goal ?? ''), g = v.proven && v.checked ? undefined : hs.find(c => at.startsWith(`${textOf(c)} @`))
            opts.progress?.('join houdini', {cubes: hs.length, proven: v.proven && v.checked ? 1 : 0, ms: Math.round(performance.now() - t2), at: at.slice(0, 100)})
            if (v.proven && v.checked) { why = 'inductive'; cone = hs; enumProof = v; enumSome = ghost ? [ghost.some] : []; cubes = hs; break }
            if (!g) break
            hs = hs.filter(c => c !== g)
          }
        }
        if (enumProof) { over = true; return }
        let asked = 0, cubeMs = 0, tGoal = 0
        // (later rounds less the sums pass's reserve, unless the caller's law holds from the set: Houdini's part, then)
        const kUntil = () => wallUntil - (round && !held ? reserve : 0)
        const real = new Set<Form>(), unsure = new Set<Form>(), lsAll = [...given, ...cubes.map(lawFor), ...(ghost ? [ghost.plain] : [])], blocked2: Form[] = [], mmRound = withGhost(forLaws(lsAll).m), at2 = new Map(cubes.map((g, i) => [g, i]))
        const version = versionOf(), startReal = new Set<Form>(), promoted: Form[] = []
        let caller = false, complete = true, again = false, coneTried = false
        // (relative induction of the caller's cone first, IC3's: once the caller's goals (and the ∃ law's) are proven, the
        // cubes their proofs read, closed under each cube's own proof's, each asked (one undecided stays, its support
        // unknown), and the cone proven whole; a proof ends the rounds. A cone cube with a model, or the one the cone's
        // proof fails at, is left out and the caller asked again (Houdini over the cone), a few times. The memo keeps every
        // decision for the round's goals after it. GDP_IC3_CONE=0 off)
        const tryCone = (): boolean => {
          const t1 = performance.now(), out2 = new Set<Form>()
          for (let it = 0; it < 6; it++) {
            const cs = cubes.filter(c => !out2.has(c)), ls2 = it ? [...given, ...cs.map(lawFor), ...(ghost ? [ghost.plain] : [])] : lsAll, mm2 = it ? withGhost(forLaws(ls2).m) : mmRound
            const byName = new Map(cs.map(c => [textOf(c), c])), at3 = new Map(cs.map((c, i) => [c, given.length + i])), need = new Set<string>(), todo: string[] = []
            const ask = (i: number) => (performance.now() > kUntil() || stop() ? undefined : within(Math.min(kUntil(), performance.now() + joinQueryMs / 8), () => decideLaw(mm2, ls2, i)))
            const add = (us: string[]) => { for (const u of us) if (!need.has(u)) { need.add(u); todo.push(u) } }
            for (const l of [...laws, ...(ghost ? [ghost.plain] : [])]) { const dl = ask(ls2.findIndex(k => k.name === l.name)); if (!dl?.proven) return false; add(dl.uses) }
            let open2 = 0, failed: Form | undefined
            while (todo.length && !failed) {
              const c = byName.get(todo.pop()!)
              if (!c) continue
              if (performance.now() > kUntil() || stop()) return false
              const dl = ask(at3.get(c)!)
              if (!dl) { open2++; continue }
              if (dl.proven) add(dl.uses); else failed = c
            }
            if (failed) { out2.add(failed); opts.progress?.('join cone', {round, it, failed: textOf(failed).slice(0, 100), need: need.size, ms: Math.round(performance.now() - t1)}); continue }
            const cut = cs.filter(c => need.has(textOf(c)))
            const v = within(t0 + ms, () => prove([...laws, ...cut.map(lawFor), ...(ghost ? [ghost.some] : [])], true))
            const at = String(v.goal ?? ''), g = v.proven && v.checked ? undefined : cut.find(c => at.startsWith(`${textOf(c)} @`))
            opts.progress?.('join cone', {round, it, cubes: cubes.length, cone: cut.length, undecided: open2, proven: v.proven && v.checked ? 1 : 0, ms: Math.round(performance.now() - t1), at: at.slice(0, 100)})
            if (v.proven && v.checked) { why = 'inductive'; cone = cut; enumProof = v; enumSome = ghost ? [ghost.some] : []; cubes = cut; return true }
            if (!g) return false
            out2.add(g)
          }
          return false
        }
        {
          for (const goal of [...laws.map(l => l.name), ...(ghost ? [ghost.plain.name] : []), ...cubes]) {
            if (performance.now() > kUntil() || stop()) { complete = false; break }
            const f = typeof goal === 'string' ? undefined : goal, ls = lsAll, others = cubes.filter(g => g !== f)
            const idx = f ? given.length + at2.get(f)! : ls.findIndex(l => l.name === goal), mm = mmRound
            if (f && !coneTried && env.GDP_IC3_CONE !== '0') { coneTried = true; if (tryCone()) { over = true; return } }
            if (f) held = true
            if ((f && kept2.has(f)) || stands.has(ls[idx]!.name)) continue
            const was = settled.get(ls[idx]!.name)
            if (was && was.every(n2 => ls.some(l => l.name === n2))) continue
            settled.delete(ls[idx]!.name)
            // (a goal decided by the EPR path alone first (a proof or a model, a cube's within a quarter of a join query, the
            // caller's within one); else a model or a refutation of the CDCL search alone, then the proof path's)
            if (f) { if (tGoal) cubeMs += performance.now() - tGoal; tGoal = performance.now(); asked++ } else tGoal = 0
            const tDl = performance.now(), dlEnd = Math.min(kUntil(), performance.now() + (f ? joinQueryMs / 8 : joinQueryMs)), dl = within(dlEnd, () => decideLaw(mm, ls, idx))
            // (the EPR path out of time on the caller's goal, or refuting it with a core the kernel's search didn't finish:
            // the proof path would be no quicker)
            const outOfTime = !dl && (performance.now() - tDl >= 0.9 * (dlEnd - tDl) || decideNote.refuted)
            if (dl?.proven) { stand(ls[idx]!.name); continue }
            let isReal = !!dl && (f && dl.goal.endsWith('@start') ? badAtStart(f, dl.witness) : realCti(dl.witness, f, others)), wit = dl?.witness
            if (f && isReal && dl!.goal.endsWith('@start')) startReal.add(f)
            // (a cube the EPR path ran out of time on: unsure at once, kept as optimistic Houdini keeps it; the CDCL search
            // after it would be no quicker)
            if (!dl && !(f && outOfTime)) {
              const inst = mapNames.length ? lawInstances(mm, ls, idx) : undefined, g = obligations(mm, ls, inst ? {[ls[idx]!.name]: inst} : {}, idx)[1]!
              // (the engine's wall too: a counted budget alone runs on past it, wo's 6 s)
              // (its share on the wall too: a counted budget of 2 s ran 8.8 s on wo's 3-key cubes)
              const quick = budgeted(joinQueryMs / 4, until2 => growCdcl(g, new Map(), {nodes: 0, until: until2}, {model: true, core: true, wall: Math.min(kUntil(), performance.now() + joinQueryMs / 4)})) as Refuted
              if (!('tree' in quick) && quick.why === REFUTED && quick.core) { const lawAt = lawsFrom(mm, ls, false, inst ?? {}); settled.set(ls[idx]!.name, [...new Set([...quick.core].map(h => lawAt.get(h)).filter((k): k is number => k !== undefined && k >= given.length && k !== idx).map(k => ls[k]!.name))]) }
              if ('tree' in quick || quick.why === REFUTED) { stand(ls[idx]!.name); continue }
              // (the caller's law's model from the proof path alone: EPR's, real or with the instances that refute it)
              isReal = !!f && quick.stuck === 'sat' && !!quick.witness && realCti(quick.witness, f, others)
              if (quick.stuck === 'sat') wit = quick.witness
              // (a cube the EPR path doesn't decide: the CDCL search's answer alone; the caller's, the proof path's too)
              if (!isReal && !f && !outOfTime) {
                proofs++
                const r2 = within(Math.min(kUntil() - 2000, performance.now() + Math.max(joinQueryMs * 1.25, (kUntil() - performance.now()) / 2)), () => proveLaw(mm, ls, idx))
                if (r2.proven) { stand(ls[idx]!.name); continue }
                isReal = !!r2.witness && realCti(r2.witness, f, others)
                wit = r2.witness ?? wit
              }
            }
            // (a real counterexample from a state no small state is: its diagram blocked, the goal's laws kept)
            // (a blocker blocked already this round blocks as well: the goal kept, nothing new blocked; one in the set doesn't
            // (a model the set rules out is no counterexample to learn from))
            const fresh = (g: Form) => !blocked2.some(h => textOf(h) === textOf(g)) && !!blocked2.push(g)
            const outside = (g: Form) => !ls.some(l => l.name === textOf(g))
            const ds = isReal && lastPre ? blockers(lastPre).filter(outside) : []
            ds.filter(fresh)
            // (the caller's: blocked at once, IC3's order, the caller asked again before the cubes)
            if (ds.length && !f && lastPre) pres.push(lastPre)
            if (ds.length) { if (!f) { held = false; if (!ghosts) { ghosts = ghostsOf(); ghost = ghosts.shift(); if (ghost) opts.progress?.('join exists', {law: ghost.plain.name.slice(0, 160)}) } break } continue }
            // (a model the interpreter doesn't confirm: PDR's obligation at its state, its diagrams blocked and the goal kept
            // (the caller's asked again first) where a row of it no small state has; else unsure)
            if (!isReal && wit) {
              const pre = preOf(wit)
              const ds2 = blockers(pre).filter(outside)
              ds2.filter(fresh)
              if (ds2.length && !f) pres.push(pre)
              if (ds2.length) { if (!f) { held = false; break } continue }
              ;(f ? subs : pres).push(pre)
            } else if (!f && isReal && lastPre) pres.push(lastPre)
            // (the ∃ law's own goal unproven: it goes; the caller's unproven with no diagram (every view's rows reached, or no
            // model to read): the ∀∃ laws, once)
            if (!f && ghost && goal === ghost.plain.name) { opts.progress?.('join exists', {dropped: ghost.plain.name.slice(0, 120)}); ghost = ghosts?.shift(); stands.clear(); again = true; break }
            if (!f && !ghosts) { const t1 = performance.now(); ghosts = ghostsOf(); ghost = ghosts.shift(); opts.progress?.('join exists', {law: ghost ? `${ghost.plain.name.slice(0, 160)}; ${ghost.name} := ${JSON.stringify(ghost.step).slice(0, 160)}` : 'none', ms: Math.round(performance.now() - t1)}); if (ghost) { again = true; held = false; break } }
            if (!f) { caller = true; held = false; break }
            ;(isReal ? real : unsure).add(f)
          }
        }
        opts.progress?.('join enumerated', {round, cubes: cubes.length, real: real.size, unsure: unsure.size, caller: caller ? 1 : 0, diagrams: blocked2.length, ms: Math.round(performance.now() - t0)})
        // (optimistic Houdini: an unsure cube holds at every small state and every step from one (they are its rows), so
        // it stays; the set's proof decides, a cube it fails at dropped and the rounds go on)
        // (IC3's push: the pending cubes asked together, each with the set and every other pending one assumed (one frame),
        // those with a model out (an undecided one stays, as Houdini keeps it) and the rest asked again, until none has
        // one; what is left comes back into the set together.
        // Once the set has changed since the last push; each cube back twice at most)
        let frame = complete && !caller ? [...pending].filter(g => tried.get(g) !== version && (backs.get(g) ?? 0) < 2) : []
        const pushed = frame.length
        for (const g of frame) tried.set(g, version)
        for (let pass = 0; frame.length && pass < 4 && performance.now() < kUntil() && !stop(); pass++) {
          frame = frame.filter((g, i) => !lsAll.some(l => l.name === textOf(g)) && frame.findIndex(h => textOf(h) === textOf(g)) === i)
          const lsP = [...lsAll, ...frame.map(lawFor)], mmP = withGhost(forLaws(lsP).m), failed = new Set<Form>()
          frame.forEach((g, i) => {
            if (performance.now() > kUntil()) { failed.add(g); return }
            const dl = within(Math.min(kUntil(), performance.now() + joinQueryMs / 8), () => decideLaw(mmP, lsP, lsAll.length + i))
            if (!dl || dl.proven) return
            failed.add(g)
            // (the push's counterexample an obligation, IC3's: blocked as a round's are, by the enumeration's cubes false
            // there, so that the next push has what it lacked)
            if (dl.goal.endsWith('@step')) for (const b of blockers(preOf(dl.witness))) if (!lsP.some(l => l.name === textOf(b)) && !pending.has(b) && !blocked2.some(h => textOf(h) === textOf(b))) blocked2.push(b)
          })
          if (!failed.size) { promoted.push(...frame); break }
          frame = frame.filter(g => !failed.has(g))
        }
        if (pending.size) opts.progress?.('join frames', {round, pending: pending.size, pushed, promoted: promoted.length})
        // (IC3's frames: a failing cube pending, not dropped, unless a start breaks it)
        const drops = new Set<Form>(real)
        for (const g of unsure) kept2.add(g)
        const demote = (gs: Iterable<Form>) => { for (const g of gs) { if (startReal.has(g)) dead.add(textOf(g)); else pending.add(g); addedAt.delete(g); tried.delete(g) } }
        const back = (): Form[] => { for (const g of promoted) { pending.delete(g); backs.set(g, (backs.get(g) ?? 0) + 1); addedAt.delete(g) } return promoted }
        // (the costliest round's mean a goal, 250 ms at least: round 0's minimal cubes are the cheapest)
        if (asked > 1) perGoal = Math.max(perGoal, 250, cubeMs / (asked - 1))
        // (the next round's new cubes: what a quarter of what is left affords past the goals it asks again, 8 at least)
        const grow = (kept: Form[]) => { const ask = kept.filter(g => !kept2.has(g) && !stands.has(lawFor(g).name)).length, afford = perGoal ? Math.floor((wallUntil - performance.now()) / (4 * perGoal)) : 16; return relevant(Math.max(8, Math.min(256 - kept.length, afford - ask)), kept) }
        if (blocked2.length) { if (drops.size) unstand(drops); demote(drops); const kept = [...cubes.filter(g => !drops.has(g)), ...back(), ...blocked2]; cubes = [...kept, ...grow(kept)]; return }
        if (again) return
        // (the caller's law unproven with no diagram: the cubes its counterexamples make relevant, while there are some)
        if (caller && complete) { if (drops.size) unstand(drops); demote(drops); const kept = [...cubes.filter(g => !drops.has(g)), ...back()], more = grow(kept); if (more.length) { cubes = [...kept, ...more]; return } }
        // (the set's proof, relative induction over the set: a cube it fails at dropped and the proof asked again at once, the
        // rounds again only where the caller's law fails or a cube's goal can't be named)
        const gone: Form[] = []
        let grown = false
        if (complete && !caller && !drops.size) for (let k = 0; k < 24 && !stop() && performance.now() < wallUntil; k++) {
          const t2 = performance.now(), setLaws = [...laws, ...cubes.map(lawFor), ...(ghost ? [ghost.some] : [])]
          let v = within(t0 + ms, () => prove(setLaws, true))
          // (the fast proof failing at a cube whose own goal the rounds proved from this set: the two disagree, and the
          // usual proof decides (proveSetFast has a spurious model on ring's own-id law))
          const at0 = String(v.goal ?? ''), g0 = v.proven && v.checked ? undefined : cubes.find(c => at0.startsWith(`${textOf(c)} @`))
          if (g0 && at0.endsWith('@step') && stands.has(lawFor(g0).name)) v = within(t0 + ms, () => prove(setLaws))
          const at = String((v as {goal?: string}).goal ?? ''), g = v.proven && v.checked ? undefined : cubes.find(c => at.startsWith(`${textOf(c)} @`))
          opts.progress?.('join set', {cubes: cubes.length, exists: ghost ? 1 : 0, proven: v.proven && v.checked ? 1 : 0, ms: Math.round(performance.now() - t2), at: at.slice(0, 120)})
          if (v.proven && v.checked) { why = 'inductive'; cone = cubes; enumProof = v; enumSome = ghost ? [ghost.some] : []; break }
          if (!g) break
          // (IC3's: the failing cube's model at its step, blocked by the enumeration's cubes false at its state where there
          // are some new ones, the cube kept and the rounds again; else the cube dropped)
          const wit2 = v.witness, bs = wit2 && at.endsWith('@step') ? blockers(preOf(wit2)).filter(b => !cubes.some(c => textOf(c) === textOf(b)) && ![...pending].some(c => textOf(c) === textOf(b)) && !dead.has(textOf(b)) && !atStart(b)) : []
          if (bs.length) { cubes = [...cubes, ...bs]; grown = true; break }
          if (wit2 && at.endsWith('@step')) subs.push(preOf(wit2))
          cubes = cubes.filter(c => c !== g); gone.push(g)
        }
        if (!complete || caller || (!drops.size && !gone.length && !grown && !promoted.length && !pending.size) || enumProof) over = true
        if (drops.size || gone.length) unstand([...drops, ...gone])
        demote([...drops, ...gone])
        cubes = [...cubes.filter(g => !drops.has(g)), ...back()]
        // (nothing changed and nothing left to push: the frames at their fixpoint, the set grown by relevance to the
        // counterexamples while there is something relevant)
        if (!enumProof && !drops.size && !gone.length && !grown && !promoted.length && [...pending].every(g => tried.get(g) === versionOf() || (backs.get(g) ?? 0) >= 2)) {
          const more = complete && !enumProof ? grow(cubes) : []; if (more.length) { cubes = [...cubes, ...more]; over = false } else over = true
        }
      })
    }
    }
    for (;;) {
      if (now() > jUntil || stop()) { why = 'time'; break }
      rounds++
      set = [...formsNow(), ...extras].filter(f => !blocked.has(textOf(f)))
      const byText = new Map(set.map(f => [textOf(f), f]))
      for (const [t, used] of stood) if (used.some(u => !byText.has(u))) stood.delete(t)
      const order = [...laws, ...stepLaws].map(l => l.name), inOrder = new Set(order)
      let todo: string | undefined
      for (let q = 0; q < order.length; q++) {
        const used = stood.get(order[q]!)
        if (!used) { todo = order[q]; break }
        for (const u of used) if (!inOrder.has(u)) { inOrder.add(u); order.push(u) }
      }
      if (todo === undefined) { why = 'inductive'; cone = order.filter(t => !callers.has(t)).map(t => byText.get(t)!); break }
      // The goal with as little of the set assumed as will do (relative induction, as IC3 has it): first none of it; a
      // counterexample the set rules out adds to what is assumed the forms that rule it out that the cone already has
      // (else those proven before, else the smallest), a few at a time; past a few tries, or stuck, the whole set. A
      // counterexample the whole set allows is one to learn from.
      const todoForm = callers.has(todo) ? undefined : byText.get(todo)!
      const inCone = new Set(order)
      const rank = (f: Form) => (inCone.has(textOf(f)) ? 0 : stood.has(textOf(f)) ? 1 : 2) * 1000 + f.coef.length * 10 + (f.never || f.nevers || f.also ? 1 : 0)
      const whole = set.filter(f => f !== todoForm)
      let ctx: Form[] = [], witness: Record<string, number> | undefined, lastStuck = '', qms = 0, settled = false
      // (before the whole set, the forms proven so far beside the context: a proof there is a proof with the whole set,
      // at a fraction of its hypotheses; a model there, the whole set asked as before)
      const provenFirst = (): Form[] | undefined => { const ps = whole.filter(f => !ctx.includes(f) && stood.has(textOf(f))); return ps.length && ctx.length + ps.length < whole.length / 2 ? [...ctx, ...ps] : undefined }
      // (a few tries, more where the set is large: until the context would hold a sixteenth of it)
      const tries = Math.max(joinAttempts, Math.ceil(whole.length / 16 / joinAdd))
      for (let attempt = 0; attempt <= tries; attempt++) {
        if (attempt === tries && ctx !== whole) {
          const pf = provenFirst()
          if (pf) { const out = stepWith(todo, todoForm, pf); if ('used' in out) { stood.set(todo, out.used!); opts.progress?.('join', {round: rounds, set: set.length, ms: qms, proven: todo.slice(0, 60), reads: out.used!.length, ctx: pf.length, attempt}); settled = true; break } }
          ctx = whole
        }
        const tq = performance.now(), out = stepWith(todo, todoForm, ctx)
        qms += Math.round(performance.now() - tq)
        if ('used' in out) {
          stood.set(todo, out.used!)
          opts.progress?.('join', {round: rounds, set: set.length, ms: qms, proven: todo.slice(0, 60), reads: out.used!.length, ctx: ctx.length, attempt})
          settled = true; break
        }
        lastStuck = out.stuck!
        if (!out.witness) { if (ctx === whole) break; ctx = whole; attempt = tries - 1; continue }
        const w = out.witness, {params: pp0, st: st0} = stateOf(w), pre0 = pointOf(pp0, st0)
        if (ctx === whole) { witness = w; break }
        const ruling = whole.filter(f => !ctx.includes(f) && !holdsAt(f, pre0)).sort((p2, q2) => rank(p2) - rank(q2))
        if (!ruling.length) { witness = w; break }
        ctx = [...ctx, ...ruling.slice(0, joinAdd)]
      }
      if (settled) continue
      if (!witness) {
        opts.progress?.('join', {round: rounds, set: set.length, ms: qms, result: lastStuck, goal: todo.slice(0, 60)})
        if (callers.has(todo)) { why = `stuck ${lastStuck}`; break }
        blocked.add(todo); continue
      }
      const w = witness, {params, st} = stateOf(w)
      if (todoForm?.nevers) neversBroken++
      const input = requestOf(w)
      let post: State | undefined
      try { post = run.step(params, st, input); stepNamed(st, post) } catch { post = undefined }
      const pre = pointOf(params, st)
      // A model the interpreter reads otherwise (a remainder's term the kernel left free, a value past what doubles hold):
      // for a form, its goal is set aside; for a caller's law, the state is still one to rule out.
      const outside = !post || set.some(f => !holdsAt(f, pre))
      if (outside && !callers.has(todo)) { blocked.add(todo); opts.progress?.('join', {round: rounds, set: set.length, ms: qms, result: 'outside', goal: todo.slice(0, 60)}); continue }
      if (outside || breaks(params, post!, st, input)) {
        // the caller's law broken from a state the set allows: a candidate false there and at every state reached, the
        // one false at the most such states (then the smallest), or one made from it (fromCti); else its cube blocked,
        // as IC3 blocks one. Where no sample holds its control state (the samples say nothing of it) the cube comes first.
        negs.push(pre); ctis.push(pre)
        const pv = valuesOf(pre.scalar), alone = !S.some(s2 => ctrl.every(i => s2[i] === pv[i]))
        const cube = (): boolean => {
          if (outside || !joinCubes || !initVec || cubed >= joinCubeMax) return false
          const made = blockCube(pv, joinCubeDepth, set), fresh = made.filter((f, i) => !set.some(g2 => textOf(g2) === textOf(f)) && made.findIndex(g2 => textOf(g2) === textOf(f)) === i)
          opts.progress?.('join', {round: rounds, set: set.length, cubes: made.map(f => textOf(f).slice(0, 100)).join('; ') || `none: ${cubeWhy}`})
          cubed += fresh.length; extras.push(...fresh)
          return fresh.length > 0
        }
        if (alone && cube()) continue
        // (the control refined first, where a level leaves the state out: the samples then say what holds there)
        if (!outside && refine(pre)) { opts.progress?.('join', {round: rounds, refined: spaces.map(sp => sp.control()).join('; ')}); continue }
        const pick = (fs: Form[]) => { let bestF: Form | undefined, score = -Infinity; for (const f of fs) { if (f.cells || f.cong || extras.includes(f) || blocked.has(textOf(f)) || holdsAt(f, pre) || !reached.every(p2 => holdsAt(f, p2))) continue; const sc = negs.reduce((k2, c) => k2 + (holdsAt(f, c) ? 0 : 1), 0) * 1000 - f.size; if (sc > score) (bestF = f, score = sc) } return bestF }
        const room = extras.length < joinExtras && tried < joinTries
        let next = room ? pick(pool) : undefined
        if (!next && room) { const made = fromCti(pre); pool.push(...made); next = pick(made) }
        if (next) tried++
        opts.progress?.('join', {round: rounds, set: set.length, ms: qms, target: next ? textOf(next).slice(0, 60) : 'none', ...(next ? {} : {outside: outside ? 1 : 0, goal: todo.slice(0, 120)})})
        if (!next && !alone && cube()) continue
        // (where the state's cube isn't blocked, a view's)
        if (!next && joinCubes && !outside && cubed < joinCubeMax && views.length) {
          const made = viewCube(pre).filter(f => !set.some(g2 => textOf(g2) === textOf(f)))
          opts.progress?.('join', {round: rounds, set: set.length, viewCubes: made.map(f => textOf(f).slice(0, 120)).join('; ') || 'none'})
          if (made.length) { cubed += made.length; extras.push(...made); continue }
        }
        // (a found form nothing strengthens is dropped, as Houdini drops one: the cone finds its way round it or fails on
        // a caller's law)
        if (!next && !callers.has(todo)) { blocked.add(todo); continue }
        if (!next) { why = 'target'; break }
        extras.push(next); continue
      }
      const after = post!, postP = pointOf(params, after)
      // (a model the interpreter reads otherwise, a quotient's term the kernel left free, say: nothing to join, and the
      // goal is set aside)
      if (!set.some(f => !holdsAt(f, postP))) {
        // (a caller's goal: asked again, as before; the same counterexample again, a counted search's, has nothing to teach)
        if (callers.has(todo)) { const wk = JSON.stringify(w); if (sameAgain.get(todo) === wk) { why = 'no violation'; break } sameAgain.set(todo, wk) }
        blocked.add(todo); opts.progress?.('join', {round: rounds, set: set.length, ms: qms, result: 'no violation', goal: todo.slice(0, 60)}); continue }
      // (a form's counterexample: its own preimage's directions first, bounded by the states, where they leave the
      // state out; else the state it steps to is joined in)
      if (todoForm && !deepened.has(todo)) {
        deepened.add(todo)
        const more = spaces.map(sp => sp.deepen(preimages(m, [lawFor(todoForm)], [], atoms, sp.coords), reached, pre)).some(Boolean)
        if (more && formsNow().some(f => !holdsAt(f, pre))) { stood.clear(); opts.progress?.('join', {round: rounds, deepened: todo.slice(0, 60)}); continue }
      }
      const j0 = joins, d0 = dropped
      reach(postP)
      // short walks from the state joined: every state they reach is a successor of one the invariant holds at
      let walked = 0
      for (let t = 0, at = after, misses = 0; t < joinWalk && misses < 3; t++) {
        let inp: Request | undefined = randomInput(params, 4), next: State | undefined
        try { if (allowed(m, run, params, at, inp)) next = run.step(params, at, inp) } catch { next = undefined }
        if (!next && flagless) { inp = requestAt(params, at); try { if (inp) next = run.step(params, at, inp) } catch { next = undefined } }
        if (!next) { misses++; continue }
        if (breaks(params, next, at, inp)) break
        reach(pointOf(params, next)); at = next; walked++
      }
      opts.progress?.('join', {round: rounds, set: set.length, ms: qms, goal: todo.slice(0, 60), joins: joins - j0, walked, dropped: dropped - d0})
    }
    // (a rule whose scalars the runs held at a few values each: no counter, the engine's shape)
    if (engineFollows() && why !== 'inductive') engine()
    opts.progress?.('join end', {rounds, set: set.length, why, cone: cone.length, ms: Math.round(performance.now() - jT0)})
    // (unproven, the search below begins as it would have: the candidates and the counterexamples as they were)
    if (why === 'inductive') chosen = cone
    else { pool = pool0; ctis.length = ctis0 }
  } catch (e) { pool = pool0; ctis.length = ctis0; chosen = []; opts.progress?.('join failed', {why: String((e as Error).message).slice(0, 120)}) }
  // The search proves one law at a time (proveLaw), each with every law assumed, and keeps what it proved while laws
  // are only added (more laws assumed keep a proof a proof); dropping one forgets it all. Once every law is proven so,
  // the set is proven as a whole, by the rule's own prover: that verdict is the answer.
  // A law of the caller's (or a kind's) proven before any candidate was added stays proven whatever is added or dropped.
  const done = new Set<string>(), base = new Set<string>()
  const forget = () => { done.clear(); for (const b of base) done.add(b) }
  const drop = (f: Form) => { chosen = chosen.filter(g => g !== f); pool = pool.filter(g => g !== f); forget() }
  const search = (ls: Law[]): Verdict => {
    // (laws with "there exists" are proven as a set, their witnesses chosen together: core/exists.ts)
    if (ls.some(l => l.some?.length)) { const whole = prove([...laws, ...chosen.map(lawFor)]); if (!(whole.proven && whole.checked)) forget(); return whole }
    for (let i = 0; i < ls.length; i++) {
      if (done.has(ls[i]!.name)) continue
      proofs++
      const r = proveLaw(forLaws(ls).m, ls, i)
      if (!r.proven) return {proven: false, checked: false, goal: r.goal, stuck: r.stuck, ...(r.witness ? {witness: r.witness} : {})}
      done.add(ls[i]!.name)
      if (!chosen.length) base.add(ls[i]!.name)
    }
    if (stepLaws.length) { proofs++; const r = proveStepLaws(forLaws(ls).m, ls, stepLaws); if (!r.proven) return {proven: false, checked: false, ...(r.failed ? {goal: r.failed.goal, stuck: r.failed.stuck, ...(r.failed.witness ? {witness: r.failed.witness} : {})} : {})} }
    const whole = prove([...laws, ...chosen.map(lawFor)])
    if (!(whole.proven && whole.checked)) forget()
    return whole
  }
  // A cell form's mirror, −Σ ≤ −d beside Σ ≤ d under the same guard (its text).
  const mirrorText = (f: Form): string | undefined => (!f.cells || f.mod || f.cong || f.never || f.nevers || f.cube || f.unreachable || f.also || !f.coef.length ? undefined : textOf({...f, coef: f.coef.map(([i, c]) => [i, -c]), d: -f.d}))
  if (enumProof) last = enumProof
  for (let iter = 0; iter < 300 && !enumProof && now() < until && !stop(); iter++) {
    const began = now(), wall = performance.now()
    // (each law proven alone, then the set as a whole: the same goals, grown once)
    last = withTrees(() => search([...given, ...chosen.map(lawFor)]))
    const took = now() - began
    opts.progress?.('proof', {chosen: chosen.length, goal: last.goal ?? '', stuck: last.stuck ?? '', ms: Math.round(performance.now() - wall), counted: Math.round(took)})
    if (last.proven && last.checked) break
    if (!last.goal) break
    const name = goalName(last.goal), stuckOn = chosen.find(f => lawFor(f).name === name)
    if (last.run) {
      // A real run breaks it: a candidate is false (dropped); a law of the caller's is false (the answer).
      if (!stuckOn) break
      drop(stuckOn); continue
    }
    // A proof the last candidate made slow (more cases to split) fails: that candidate goes.
    if (chosen.length && took > slow) { drop(chosen.at(-1)!); continue }
    const p = /@step|@\d+ steps/.test(last.goal) && last.witness ? witnessPoint(last.witness) : undefined
    if (p) ctis.push(p)
    let next = p ? best(p) : undefined
    if (!next && p) next = best(p, true)
    if (!next && p) { const t = performance.now(), made = fromCti(p); pool.push(...made); next = best(p); opts.progress?.('cti', {forms: made.length, ms: Math.round(performance.now() - t)}) }
    // (a cell form chosen with its mirror where that is alive: the equality both halves state at every key, neither
    // inductive without the other, as the real-world corpus's Timelock and blnk need; on CHC's scalar forms, measured,
    // it cost s_split tasks, so cell forms only)
    if (next) { chosen.push(next); const mt = inferHalves ? mirrorText(next) : undefined, mirror = mt && pool.find(g => !chosen.includes(g) && textOf(g) === mt); if (mirror) chosen.push(mirror); continue }
    // Stuck with no counterexample on a goal not a candidate's: the last candidate made it harder, so it goes.
    if (chosen.length && !stuckOn && !p) { drop(chosen.at(-1)!); continue }
    if (!stuckOn) break
    drop(stuckOn)
  }
  // Unproven: each congruence the runs left alive, with the laws alone (the counterexamples' choice may have gone to the
  // bounds instead), at most four.
  if (!(last.proven && last.checked)) {
    for (const f of alive.filter(g => g.cong).slice(0, 4)) {
      if (now() > until || stop()) break
      const v = prove([...laws, lawFor(f)])
      if (v.proven && v.checked) { chosen = [f]; last = v; break }
    }
  }
  trace('kernel', {chosen: chosen.length, proven: !!(last.proven && last.checked)})
  if (!(last.proven && last.checked)) { trace('end', {proven: false, stopped: stop()}); return {...last, found: [], stats: stats(samples.length, forms.length, alive.length)} }
  // Take out what the proof doesn't need, the last added first (not the engine's set: Houdini's, each cube minimal).
  for (const f of opts.minimize === false || enumProof ? [] : [...chosen].reverse()) {
    if (now() > until || stop()) break
    const without = chosen.filter(g => g !== f), v = prove([...laws, ...without.map(lawFor)])
    if (v.proven && v.checked) (chosen = without, last = v)
  }
  const kept = chosen.flatMap(f => (f.mod ? [f.mod.k] : []))
  if (kept.length) rule?.dividesBy(...kept)
  trace('end', {proven: true, stopped: stop(), found: chosen.map(f => textOf(f)).join('; ')})
  return {...last, found: [...chosen.map(f => { const law = lawFor(f), text = law.name, source = sourceOf(f, text); return {law, text, ...(source ? {source} : {})} }), ...(enumProof ? enumSome : []).map(law => ({law, text: law.name}))], stats: stats(samples.length, forms.length, alive.length)}
}
