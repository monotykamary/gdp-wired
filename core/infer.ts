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
//   - the join: per control state (the choice, loc, and a few yes/nos), the samples' affine hull (its equalities, exact)
//     and each direction's largest value (each value up and down, pairs where there are few, the rule's own comparisons);
//     Houdini on the cone of the caller's laws: each goal proven with as little of that set assumed as will do (none,
//     then the forms a counterexample breaks, as IC3's relative induction, then all), each asked first of the CDCL
//     search for a model alone (a refutation's core: the forms it read), a counterexample the whole set allows joined in
//     (the hull grows to hold it, a bound rises to the next of the rule's constants, then goes), one to a caller's law
//     ruled out by a candidate or by a cube blocked as IC3 blocks one (its control state, the rule's own comparisons
//     true there and the bounds that keep the samples out, the literals its refutation's core read, its predecessors
//     blocked first), the cube first where no sample is at its control state; every goal of the cone proven, the cone
//     is the answer
//   - the kernel (where the join proves nothing, as it was): the laws with the candidates chosen so far, proven one law
//     at a time; when a goal is stuck at a step, its witness is a counterexample to induction, so the candidate that
//     rules it out (and the most of those seen) is added; a chosen candidate that nothing supports, or that makes a proof slow, is dropped; the set proven as a whole
//     is the answer, after each chosen candidate the proof doesn't need is taken out again
import {quietly} from './cyclic.ts'
import {type C, type E, type Law, type Machine, type Request, type State, all, any, atMost, divisorsIn, evalC, get, interpret, machineTerms, modName, n, not, plus, same, seeded, times, withArithmetic, x} from './machine.ts'
import {type StepLaw, type Verdict, proveRule, proveSteps, verdictOf} from './dsl.ts'
import {allowed, watch} from './watch.ts'
import {clock, counted, grow, proveLaw, proveLaws, proveStepLaws, usedHyps, withDeadline, withTrees} from '../kernel/prove.ts'
import {obligations, substC} from '../kernel/kernel.ts'
import {env, gcd, work} from './solver.ts'
import {bgcd} from './q.ts'
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
type Atom = {name: string, parts: [string, 1 | -1][], param: boolean, int: boolean, cell: boolean}
type Guard = {atom: number, value: number} | {keyNot: number}
// `when`: a linear condition the form holds under (Σ c·v ≤ d over scalars), beside its guard; the search makes such forms
// from a counterexample to induction no candidate rules out.
// `mod`: the form is a remainder, (Σ c·v) mod k = r (d unused). `cong`: a congruence, ∃k. Σ c·v = mod·k + rest
// (core/exists.ts: proven through a witness, a ghost the kernel's counterexamples choose), k a natural or, over an
// integer, an integer; the same claim, made only where remainders are off (InferOptions.remainders).
// `also`: more values the form holds under, beside its guard (a control state: loc and the yes/nos at once); `never`:
// values never all held at once (a control state no run reaches). The join makes both.
// `nevers`: control states none of which is ever held (the join's control states no run reached, one law for all).
// `cube`: literals never all true at once (a value at one value, or Σ c·v ≤ d): a cube the join blocked.
type At = {atom: number, value: number}
type Lit = {at: At} | {lin: {coef: [number, number][], d: number}}
type Form = {coef: [number, number][], d: number, cells: boolean, guard?: Guard, also?: At[], when?: {coef: [number, number][], d: number}, unreachable?: At, never?: At[], nevers?: At[][], cube?: Lit[], mod?: {k: number, r: number}, cong?: {mod: number, rest: number}, size: number}

const KEY = 'key$found', AT = '@', K = '#', SOME = 'k$found'
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
const joinShare = 0.6, joinQueryMs = 8000, joinRequestMs = 150, joinWalk = 8, joinPairs = 10, joinRaises = 2, joinSparse = 4, joinCoef = 1000
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

// A cell's key as the kernel names it (kernel.ts keyOf): `name:coef` parts joined by ',', '1' the constant.
const keyValue = (cell: string, w: Record<string, number>): number | undefined => {
  const inner = cell.slice(cell.indexOf('[') + 1, -1)
  if (inner.includes('[')) return undefined
  let value = 0
  for (const part of inner.split(',').filter(Boolean)) {
    const at = part.lastIndexOf(':'), name = part.slice(0, at), coef = Number(part.slice(at + 1))
    if (name === '1') value += coef
    else if (name in w) value += coef * w[name]!
    else return undefined
  }
  return value
}

// The linear comparisons a machine's conditions make over the state alone (its assumption, its step's conditions and the
// laws), over the atoms given (an integer atom's two parts with opposite coefficients), each as Σ t·v ≤ d beside its
// negation (an equality's two sides and theirs): the directions a bound of the join may take beside the atoms' own,
// and the literals of a cube at a point.
type Rel = {coef: [number, number][], d: number}
function comparisons(m: Machine, laws: Law[], atoms: Atom[], coords: number[]): Rel[] {
  const lin = (e: E, k: number, out: Map<string, number>): boolean => {
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
  Object.values(m.step.state ?? {}).forEach(visitE)
  laws.forEach(l => visitC(l.holds))
  return [...found.values()]
}

export function inferLaws(target: AnyRule | Machine, laws: Law[], stepLaws: StepLaw[] = [], opts: InferOptions = {}): Inferred {
  return quietly(() => withDeadline(clock() + (opts.ms ?? 20000), () => inferLawsSearch(target, laws, stepLaws, opts)))
}
function inferLawsSearch(target: AnyRule | Machine, laws: Law[], stepLaws: StepLaw[] = [], opts: InferOptions = {}): Inferred {
  const t0 = performance.now(), ms = opts.ms ?? 20000, wallUntil = t0 + ms, rule = isRule(target) ? target : undefined
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
  const prove = (ls: Law[]): Verdict => {
    proofs++
    const {r: searchRule, m: mm} = forLaws(ls)
    if (searchRule) return stepLaws.length ? proveSteps(searchRule, ls, stepLaws, {search: false}) : proveRule(searchRule, ls, {search: false})
    const out = stepLaws.length ? proveStepLaws(mm, ls, stepLaws) : proveLaws(mm, ls)
    return verdictOf(out)
  }
  const stats = (samples: number, candidates: number, alive: number) => ({samples, candidates, alive, proofs, ms: Math.round(performance.now() - t0), stopped: stop()})
  const first = opts.first ?? prove(laws)
  if ((first.proven && first.checked) || first.run) return {...first, found: [], stats: stats(0, 0, 0)}

  // --- runs ------------------------------------------------------------------------------------------------------------
  const run = interpret(m), rand = seeded(17), kinds = rule ? rule.kindsOfState() : []
  const given = rule ? [...rule.kindLaws().filter(k => !laws.some(l => l.name === k.name)), ...laws] : laws
  const randomParams = (bound: number): Env => (rule ? rule.randomParams(rand, bound) : Object.fromEntries(m.params.map(p => [p, rand(bound + 1)])))
  const randomInput = (params: Env, bound: number): Request => (rule ? rule.randomInput(rand, bound, params)
    : {...Object.fromEntries(m.inputs.map(i => [i, rand(bound + 1)])), ...Object.fromEntries((m.inputMaps ?? []).map(i => [i, new Map<number, number>()]))})
  type Sample = {params: Env, st: State}
  const samples: Sample[] = [], cap = 3000
  const keep = (s: Sample) => { if (samples.length < cap) samples.push(s); else if (rand(4) === 0) samples[rand(cap)] = s }
  for (const st of opts.seen ?? []) if (!m.params.length) keep({params: {}, st})
  trace('start')
  const mapsText = (st: State) => JSON.stringify(Object.values(st.maps).map(c => [...c]))
  // Counted: `runs` requests tried at least, and on until the samples are full (a trial keeps its start at least, so as
  // many trials as they hold fill them), the trials at most `runs` or that many. Timed: `runsMs` of wall time.
  const runsTimed = timed || opts.runsMs !== undefined, runsUntil = Math.min(wallUntil, performance.now() + (opts.runsMs ?? 500)), least = opts.runs ?? inferRuns
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
  const A = atoms.length, cellAtoms = atoms.flatMap((a, i) => (a.cell ? [i] : []))
  const valueOf = (a: Atom, env: Env) => { let s = 0; for (const [p, sign] of a.parts) s += sign * (env[a.cell ? AT + p : p] ?? 0); return s }
  const cellOf = (st: State, map: string, key: number) => st.maps[map]?.get(key) ?? st.defaults?.[map] ?? m.maps![map]!
  // The scalar rows (one per state reached), and the cell rows (one per state and key a map holds, and one fresh key).
  const keysIn = (st: State) => { const ks = new Set<number>(); for (const c of Object.values(st.maps)) for (const k of c.keys()) ks.add(k); return [...ks] }
  const cellRows = (params: Env, st: State): Env[] => {
    if (!mapNames.length) return []
    const ks = keysIn(st), fresh = ks.length ? Math.max(...ks) + 1 : 0
    return [...ks, fresh].map(k => ({...params, ...st.scalars, [K]: k, ...Object.fromEntries(mapNames.map(mp => [AT + mp, cellOf(st, mp, k)]))}))
  }
  const rowsS = samples.map(s => ({...s.params, ...s.st.scalars}))
  const rowsK: Env[] = []
  for (const s of samples) { if (rowsK.length > 6000) break; rowsK.push(...cellRows(s.params, s.st)) }
  const valsS = atoms.map(a => Float64Array.from(rowsS, r => valueOf(a, r))), valsK = atoms.map(a => Float64Array.from(rowsK, r => valueOf(a, r)))
  const kindOf = new Map(kinds.map(([name, k]) => [name, k]))
  // Modes: a yes/no, a choice, or a state natural (or cell) no run took past a few values.
  type Mode = {atom: number, values: number[], choice?: readonly string[], bool?: boolean}
  const modes: Mode[] = []
  atoms.forEach((a, i) => {
    if (a.param || a.int) return
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
  if (cellAtoms.length) {
    const all = atoms.flatMap((_, i) => (modeOf(i)?.choice ? [] : [i])), cellOk = (acc: [number, number][]) => acc.some(([i]) => atoms[i]!.cell) && acc.filter(([i]) => !atoms[i]!.cell).length <= 1
    pick(1, [1], cellAtoms, () => true, true)
    pick(2, [1], all, cellOk, true)
    if (choose(3, A) * 8 <= maxCandidates / 4) pick(3, [1], all, acc => cellOk(acc) && acc.filter(([i]) => atoms[i]!.cell).length >= 2, true)
  }
  const sizeOf = (coef: [number, number][]) => coef.length * 100 + coef.reduce((s, [, c]) => s + Math.abs(c), 0)
  const forms: Form[] = []
  const NS = rowsS.length, NK = rowsK.length
  const at = (coef: [number, number][], vals: Float64Array[], j: number) => { let s = 0; for (const [i, c] of coef) s += c * vals[i]![j]!; return s }
  const keyNots = plain.filter(i => !atoms[i]!.param && !atoms[i]!.int)
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
    const here = guards.filter(mode => !coef.some(([i]) => i === mode.atom) && (cells || !atoms[mode.atom]!.cell))
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
  const modAtoms = terms.filter(i => !atoms[i]!.param && !modeOf(i)?.bool), modShapes: [number, number][][] = modAtoms.map(i => [[i, 1]])
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
  const textOf = (f: Form): string => {
    const atText = (g: At) => `${nameOf(g.atom)} is ${shownValue(g.atom, g.value)}`
    if (f.never) return `never ${f.never.map(atText).join(' and ')}`
    if (f.nevers) return `never ${f.nevers.map(c => c.map(atText).join(' and ')).join('; nor ')}`
    if (f.cube) return `never ${f.cube.map(l => ('at' in l ? atText(l.at) : (({l: a, r: b}) => `${a} <= ${b}`)(sides({coef: l.lin.coef, d: l.lin.d, cells: false, size: 0})))).join(' and ')}`
    if (f.also) return `${f.also.map(atText).join(' and ')} → ${textOf({...f, also: undefined})}`
    if (f.unreachable) return `${nameOf(f.unreachable.atom)} is never ${shownValue(f.unreachable.atom, f.unreachable.value)}`
    if (f.cong) return `∃k. ${f.coef.map(([i, c], j) => `${j ? (c > 0 ? ' + ' : ' − ') : c < 0 ? '−' : ''}${nameOf(i)}`).join('')} = ${f.cong.mod}·k${f.cong.rest ? ` + ${f.cong.rest}` : ''}`
    const {l, r} = sides(f), within = allowedValues(f)
    const body = f.mod ? `${f.coef.map(([i, c], j) => `${c < 0 ? (j ? ' − ' : '−') : j ? ' + ' : ''}${nameOf(i)}`).join('')} mod ${f.mod.k} = ${f.mod.r}` : within ? `${nameOf(f.coef[0]![0])} is ${within.map(v => shownValue(f.coef[0]![0], v)).join(' or ')}` : `${l} <= ${r}`
    const under = f.when ? (({l: wl, r: wr}) => `${wl} <= ${wr} → `)(sides({coef: f.when.coef, d: f.when.d, cells: false, size: 0})) : ''
    const guarded = !f.guard ? under + body : 'keyNot' in f.guard ? `k = ${nameOf(f.guard.keyNot)} or ${body}` : `${nameOf(f.guard.atom)} is ${shownValue(f.guard.atom, f.guard.value)} → ${under}${body}`
    return f.cells ? `every k: ${guarded}` : guarded
  }
  const sum = (es: E[]): E => es.reduce((p, q) => plus(p, q), n(0))
  // Each congruence its own witness's name (each may be a ghost of the machine).
  const someNames = new Map<Form, string>(), someName = (f: Form) => { let k = someNames.get(f); if (!k) someNames.set(f, (k = `${SOME}${someNames.size}`)); return k }
  const part = (a: Atom, p: string): E => (a.cell ? get(p, x(KEY)) : x(p))
  const partsOf = (f: Form, sign: 1 | -1): E[] => f.coef.flatMap(([i, c]) => atoms[i]!.parts.filter(([, s]) => s * c * sign > 0).map(([p]) => { const e = part(atoms[i]!, p); return Math.abs(c) === 1 ? e : times(Math.abs(c), e) }))
  // Σ c·v ≤ d over naturals: the positive parts on the left, the negative ones and d on the right (an integer's
  // negative part goes to the other side of its sign).
  const condOf = (f: Form): C => {
    // Not at a value, one-sided where it can be (less splitting for the kernel): a natural not 0 is at least 1, and a
    // yes/no or a choice not at its last value is below it (its kind's law bounds it).
    const notAt = (i: number, value: number): C => {
      const e = part(atoms[i]!, atoms[i]!.parts[0]![0]), mo = modeOf(i), lastValue = mo?.bool ? 1 : mo?.choice ? mo.choice.length - 1 : undefined
      return value === 0 ? atMost(n(1), e) : value === lastValue ? atMost(e, n(value - 1)) : not(same(e, n(value)))
    }
    if (f.never) return any(...f.never.map(g => notAt(g.atom, g.value)))
    if (f.nevers) return all(...f.nevers.map(c => any(...c.map(g => notAt(g.atom, g.value)))))
    if (f.cube) return not(all(...f.cube.map(l => ('at' in l ? same(part(atoms[l.at.atom]!, atoms[l.at.atom]!.parts[0]![0]), n(l.at.value)) : condOf({coef: l.lin.coef, d: l.lin.d, cells: false, size: 0})))))
    if (f.also) return any(...f.also.map(g => notAt(g.atom, g.value)), condOf({...f, also: undefined}))
    if (f.unreachable) return notAt(f.unreachable.atom, f.unreachable.value)
    if (f.mod) {
      // Σ c·v = P − N over naturals (P the positive parts, N the negative ones), whose remainder by k is that of the
      // natural P + (k − 1)·N.
      const {k: dk, r} = f.mod, neg = partsOf(f, -1), e = get(modName(dk), sum([...partsOf(f, 1), ...neg.map(t => times(dk - 1, t))]))
      const body = same(e, n(r))
      return !f.guard ? body : 'keyNot' in f.guard ? any(same(x(KEY), x(atoms[f.guard.keyNot]!.parts[0]![0])), body) : any(notAt(f.guard.atom, f.guard.value), body)
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
    return !f.guard ? body : 'keyNot' in f.guard ? any(same(x(KEY), x(atoms[f.guard.keyNot]!.parts[0]![0])), body) : any(notAt(f.guard.atom, f.guard.value), body)
  }
  // The builder call, for a rule whose atoms are its own variables (naturals, or integers alone).
  const sourceOf = (f: Form, text: string): string | undefined => {
    if (!rule || f.when || f.mod || f.also || f.never || f.nevers || f.cube) return undefined
    const used = [...new Set([...f.coef.map(([i]) => i), ...(f.guard ? ['keyNot' in f.guard ? f.guard.keyNot : f.guard.atom] : []), ...(f.unreachable ? [f.unreachable.atom] : [])])]
    const ints = f.coef.filter(([i]) => atoms[i]!.int).length
    if (ints && ints !== f.coef.length) return undefined
    const ref = (i: number) => (atoms[i]!.cell ? `${atoms[i]!.parts[0]![0]}.at(k)` : nameOf(i))
    const val = (i: number) => { const mo = modeOf(i); return mo?.choice && !atoms[i]!.cell ? `${ref(i)}.index` : mo?.bool && !atoms[i]!.cell ? `${ref(i)}.n` : ref(i) }
    const cond = (i: number, value: number) => { const mo = modeOf(i); return mo?.choice && !atoms[i]!.cell ? `${ref(i)}.is('${mo.choice[value]}')` : mo?.bool && !atoms[i]!.cell ? (value === 1 ? ref(i) : `${ref(i)}.not()`) : `${ref(i)}.eq(${value})` }
    const args = `({${[...new Set(used.map(i => (atoms[i]!.cell ? atoms[i]!.parts[0]![0] : nameOf(i))))].join(', ')}})`
    const wrap = (body: string) => (f.cells ? `forall(k => ${body})` : body)
    if (f.unreachable) return `r.law('${text}', ${args} => ${cond(f.unreachable.atom, f.unreachable.value)}.not())`
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
    const guarded = !f.guard ? body : 'keyNot' in f.guard ? `k.eq(${nameOf(f.guard.keyNot)}).or(${body})` : `${cond(f.guard.atom, f.guard.value)}.implies(${body})`
    return `r.law('${text}', ${args} => ${wrap(guarded)})`
  }

  // --- evaluating a form ---------------------------------------------------------------------------------------------
  // (each row's atom values read once, however many forms are evaluated there: rows are never changed once made)
  const valuesAt = new WeakMap<Env, Float64Array>()
  const valuesOf = (env: Env): Float64Array => {
    let vs = valuesAt.get(env)
    if (!vs) { vs = new Float64Array(A); for (let i = 0; i < A; i++) vs[i] = valueOf(atoms[i]!, env); valuesAt.set(env, vs) }
    return vs
  }
  const holdsRow = (f: Form, env: Env): boolean => {
    used.evals++
    const vs = valuesOf(env)
    if (f.never) return f.never.some(g => vs[g.atom] !== g.value)
    if (f.nevers) return f.nevers.every(c => c.some(g => vs[g.atom] !== g.value))
    if (f.cube) return !f.cube.every(l => ('at' in l ? vs[l.at.atom] === l.at.value : l.lin.coef.reduce((acc, [i, c]) => acc + c * vs[i]!, 0) <= l.lin.d))
    if (f.also?.some(g => vs[g.atom] !== g.value)) return true
    if (f.unreachable) return vs[f.unreachable.atom] !== f.unreachable.value
    if (f.cong) {
      let v = 0
      for (const [i, c] of f.coef) v += c * vs[i]!
      const nat = f.coef.every(([i, c]) => !atoms[i]!.int && c > 0)
      return ((v - f.cong.rest) % f.cong.mod + f.cong.mod) % f.cong.mod === 0 && (!nat || v >= f.cong.rest)
    }
    if (f.guard) {
      if ('keyNot' in f.guard) { if (env[K] === vs[f.guard.keyNot]) return true }
      else if (vs[f.guard.atom] !== f.guard.value) return true
    }
    if (f.when) { let w = 0; for (const [i, c] of f.when.coef) w += c * vs[i]!; if (w > f.when.d) return true }
    let s = 0
    for (const [i, c] of f.coef) s += c * vs[i]!
    return f.mod ? residue(s, f.mod.k) === f.mod.r : s <= f.d
  }
  // At a state: a cell form at every key the maps hold and a fresh one.
  type Point = {scalar: Env, cells: Env[]}
  const pointOf = (params: Env, st: State): Point => ({scalar: {...params, ...st.scalars}, cells: cellRows(params, st)})
  const holdsAt = (f: Form, p: Point) => (f.cells ? p.cells.every(r => holdsRow(f, r)) : holdsRow(f, p.scalar))
  // A kernel witness as a point: its scalars, and a cell row per key it reads a map at.
  const witnessPoint = (w: Record<string, number>): Point => {
    const scalar: Env = Object.fromEntries([...scalars, ...m.params].map(v => [v, w[v] ?? 0]))
    const byKey = new Map<number, Env>()
    for (const [name, value] of Object.entries(w)) {
      const br = name.indexOf('[')
      if (br < 0 || !name.endsWith(']') || !mapSet.has(name.slice(0, br))) continue
      const key = keyValue(name, w)
      if (key === undefined) continue
      const row = byKey.get(key) ?? {...scalar, [K]: key}
      row[AT + name.slice(0, br)] = value
      byKey.set(key, row)
    }
    return {scalar, cells: [...byKey.values()]}
  }

  // --- Houdini on the runs' neighbors ----------------------------------------------------------------------------------
  let alive = forms.slice().sort((p, q) => p.size - q.size).slice(0, maxCandidates)
  const ctis: Point[] = []
  const lawful = (params: Env, st: State) => { used.watched += given.length; try { return given.every(l => watch(m, run, l, params, 4).start(st)) } catch { return false } }
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
  const lawFor = (f: Form) => { let l = lawOf.get(f); if (!l) lawOf.set(f, (l = {name: textOf(f), holds: condOf(f), ...(f.cells ? {forall: KEY} : {}), ...(f.cong ? {some: someOf(f)} : {})})); return l }
  const names = new Set(given.map(l => l.name))
  alive = alive.filter(f => !names.has(textOf(f)))
  let pool = alive.slice(), chosen: Form[] = []
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
  if (joinOn && !mapNames.length && NS) try {
    const jT0 = performance.now(), jUntil = Math.min(until, now() + (until - now()) * (opts.join ?? joinShare))
    // The control state: the choice (loc) and, where they are few, the yes/nos (a program counter in bits), each of its
    // values reached a part of its own.
    const jChoice = modes.find(mo => mo.choice && !atoms[mo.atom]!.cell), bits = modes.filter(mo => mo.bool && !atoms[mo.atom]!.cell && !atoms[mo.atom]!.param)
    const locsReached = jChoice ? new Set(valsS[jChoice.atom]!).size : 1
    const keyModes = [...(jChoice ? [jChoice] : []), ...(bits.length && bits.length <= joinBits && locsReached * 2 ** bits.length <= joinKeys ? bits : [])]
    const keyAtoms = keyModes.map(mo => mo.atom), coords = plain.filter(i => !keyAtoms.includes(i)), CN = coords.length
    // The directions over some values: each value up and down, pairs of them where there are few, and the rule's own
    // comparisons over the state (a guard, the query's condition), each both ways.
    const directions = (cs: number[]): [number, number][][] => {
      const out: [number, number][][] = []
      for (const i of cs) out.push([[i, 1]], [[i, -1]])
      if (cs.length <= joinPairs) for (const [a2, i] of cs.entries()) for (const j of cs.slice(a2 + 1)) for (const [c1, c2] of [[1, 1], [1, -1], [-1, 1], [-1, -1]] as const) out.push([[i, c1], [j, c2]])
      const known = new Set(out.map(t => JSON.stringify(t)))
      for (const {coef} of comparisons(m, laws, atoms, cs)) if (coef.length > 1) for (const u of coef[0]![1] > 0 ? [coef, coef.map(([i, c]) => [i, -c] as [number, number])] : []) {
        const k2 = JSON.stringify(u)
        if (!known.has(k2) && out.length < 2 * cs.length + 4 * joinPairs * joinPairs + 64) { known.add(k2); out.push(u) }
      }
      return out
    }
    const dirs = directions(coords)
    // Widening with thresholds: a bound a counterexample breaks rises to the next of the rule's constants (their sums and
    // products the first time, the constants alone after), and past that it is dropped.
    const fine = bounds, coarse = [...new Set([0, ...consts.flatMap(k => [k, -k])])].sort((p2, q2) => p2 - q2)
    type Group = {eqs: bigint[][], hi: number[], raised: number[]}
    const groups = new Map<string, Group>()
    const normal = (e: bigint[]) => { let g2 = 0n; for (const x2 of e) g2 = bgcd(g2, x2); if (g2 > 1n) for (let k = 0; k < e.length; k++) e[k]! /= g2; const lead = e.find(x2 => x2 !== 0n); if (lead !== undefined && lead < 0n) for (let k = 0; k < e.length; k++) e[k] = -e[k]!; return e }
    const dirValue = (t: [number, number][], vs: Float64Array | number[]) => { let v = 0; for (const [i, c] of t) v += c * vs[i]!; return v }
    const residual = (e: bigint[], vs: Float64Array | number[]) => { let r = e[CN]!; for (let k = 0; k < CN; k++) if (e[k]) r += e[k]! * BigInt(vs[coords[k]!]!); return r }
    let joins = 0
    const join = (g: string, vs: Float64Array | number[], widen: boolean) => {
      let grp = groups.get(g)
      if (!grp) {
        grp = {eqs: coords.map((i, k) => { const e = Array.from({length: CN + 1}, () => 0n); e[k] = 1n; e[CN] = -BigInt(vs[i]!); return e }), hi: dirs.map(t => dirValue(t, vs)), raised: dirs.map(() => 0)}
        groups.set(g, grp); return
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
    const keyOf = (vs: Float64Array | number[]) => keyAtoms.map(i => vs[i]!).join(',')
    const combos = keyModes.reduce<number[][]>((acc, mo) => acc.flatMap(c => mo.values.map(v => [...c, v])), [[]])
    for (let j = 0; j < NS; j++) join(keyOf(valsS.map(col => col[j]!)), valsS.map(col => col[j]!), false)
    let neversBroken = 0
    const formsNow = (): Form[] => {
      const out: Form[] = [], seenT = new Set<string>()
      const push = (f: Form) => { const t = textOf(f); if (!seenT.has(t) && !names.has(t)) { seenT.add(t); out.push(f) } }
      // (a choice's value no state reached: one form, whatever the yes/nos; the control states no state reached, one form
      // for all, where there are several: each alone needs the others to be inductive, a goal each where one does)
      const reachedFirst = new Set([...groups.keys()].map(k2 => k2.split(',')[0])), nev: At[][] = []
      for (const combo of combos) {
        if (combo.length > 1 && !reachedFirst.has(String(combo[0]))) { if (combo.slice(1).every(v => v === 0)) nev.push([{atom: keyAtoms[0]!, value: combo[0]!}]); continue }
        const ats = combo.map((value, k) => ({atom: keyAtoms[k]!, value})), grp = groups.get(combo.join(','))
        const guard = ats.length ? {guard: ats[0]!, ...(ats.length > 1 ? {also: ats.slice(1)} : {})} : {}
        if (!grp) { if (ats.length) nev.push(ats); continue }
        for (const e of grp.eqs) {
          const coef: [number, number][] = []
          for (let k = 0; k < CN; k++) if (e[k]) coef.push([coords[k]!, Number(e[k]!)])
          const d = -Number(e[CN]!)
          if (!coef.length || coef.length > joinSparse || coef.some(([, c]) => Math.abs(c) > joinCoef) || !Number.isSafeInteger(d)) continue
          push({coef, d, cells: false, ...guard, size: 0}); push({coef: coef.map(([i, c]) => [i, -c]), d: -d, cells: false, ...guard, size: 0})
        }
        dirs.forEach((t, k) => {
          const hi = grp.hi[k]!
          if (!Number.isFinite(hi)) return
          // constant on the hull (the equalities say it), or a yes/no's own range
          const neg = dirs.findIndex(u => u.length === t.length && u.every(([i, c], q2) => i === t[q2]![0] && c === -t[q2]![1]))
          if (neg >= 0 && grp.hi[neg] === -hi) return
          if (t.length === 1 && modeOf(t[0]![0])?.bool && (t[0]![1] > 0 ? hi >= 1 : hi >= 0)) return
          push({coef: t, d: hi, cells: false, ...guard, size: 0})
        })
      }
      // (once broken, each its own form from then on, so that a state joined in changes only the forms that
      // read its own control state, not every proof that read them all)
      if (nev.length > 1 && joinNevers && neversBroken < joinNeversBreaks) push({coef: [], d: 0, cells: false, nevers: nev, size: 1})
      else for (const ats of joinPrime ? primes(nev) : nev) push({coef: [], d: 0, cells: false, ...(ats.length > 1 ? {never: ats} : {unreachable: ats[0]!}), size: 1})
      return out
    }
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
    let rounds = 0, why = '', set: Form[] = []
    const params0: Env = {}
    // Beside the hull, forms of the candidates' that rule out a counterexample to the caller's laws (a state the set
    // allows whose successor breaks one): Houdini's, dropped when a counterexample's successor breaks them.
    const extras: Form[] = [], negs: Point[] = [], reached: Point[] = []
    let tried = 0
    const breaks = (params: Env, st: State) => laws.some(l => { try { return !evalC(l.holds, params, st, m) } catch { return true } })
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
    const stood = new Map<string, string[]>(), blocked = new Set<string>(), callers = new Set(laws.map(l => l.name))
    let cone: Form[] = [], dropped = 0
    // A state reached from one the set allows: joined in, and every extra false there dropped.
    const reach = (p2: Point) => {
      if (reached.length < 2000) reached.push(p2)
      const vs = valuesOf(p2.scalar)
      join(keyOf(vs), vs, true)
      for (let k = extras.length - 1; k >= 0; k--) if (!holdsAt(extras[k]!, p2)) { const f = extras[k]!; extras.splice(k, 1); pool = pool.filter(g2 => g2 !== f); dropped++ }
    }
    // A goal's step with these forms assumed (beside the caller's laws and the kinds'): its tree and the forms it read, or
    // the kernel's model.
    const stepWith = (name: string, form: Form | undefined, ctx: Form[]) => {
      const ctxLaws = [...ctx, ...(form ? [form] : [])].map(lawFor), ls = [...given, ...ctxLaws], mm = forLaws(ctxLaws).m
      const idx = form ? ls.length - 1 : ls.findIndex(l => l.name === name)
      const g = obligations(mm, ls, {}, idx)[1]!, base0 = g.hyps.length - 1 - ls.length, used: string[] = []
      // First a model alone of the CDCL search (no tree unfolded): refuted, the hypotheses its leaves read are those
      // a tree would (the set's proof is the kernel's below, as before); a model is the counterexample; else the prover.
      if (joinCore) {
        const quick = budgeted(joinQueryMs / 4, until2 => growCdcl(g, new Map(), {nodes: 0, until: until2}, {model: true, core: true})) as Refuted
        if (!('tree' in quick) && quick.why === REFUTED && quick.core) {
          for (const h of quick.core) { const k = h - base0; if (k >= given.length && k < ls.length && k !== idx) used.push(ls[k]!.name) }
          return {used}
        }
        if (!('tree' in quick) && quick.stuck === 'sat' && quick.witness) return {stuck: 'sat', witness: quick.witness}
      }
      const out = budgeted(joinQueryMs, until2 => grow(g, new Map(), {nodes: 0, until: until2}))
      if (!('tree' in out)) return {stuck: out.stuck, witness: out.stuck === 'sat' ? out.witness : undefined}
      for (const h of usedHyps(g, out.tree)) { const k = h - base0; if (k >= given.length && k < ls.length && k !== idx) used.push(ls[k]!.name) }
      return {used}
    }
    const stateOf = (w: Record<string, number>): {params: Env, st: State} => ({params: m.params.length ? Object.fromEntries(m.params.map(p => [p, w[p] ?? 0])) : params0, st: {scalars: Object.fromEntries(scalars.map(v => [v, w[v] ?? 0])), maps: {}}})
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
      return {scalars: sc, maps: {}}
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
    const formOf = (c: Lit[]): Form => ({coef: [], d: 0, cells: false, cube: c, size: 1})
    const witnessStep = (w: Record<string, number>): {pre: State, post?: State} => {
      const pre = stateAt(w), input = Object.fromEntries(m.inputs.map(i => [i, w[i] ?? 0])) as Request
      try { return {pre, post: run.step({}, pre, input)} } catch { return {pre} }
    }
    // Is the cube's negation inductive relative to these laws (the caller's and the kinds' beside)? Its literals after
    // the step are hypotheses of their own, so the refutation's core names those it read.
    const queryWith = (c: Lit[], frame: Law[]): {ok: true, core: Set<number>} | {ok: false, pre: State, post?: State} | undefined => {
      const f = formOf(c), own = lawFor(f), names2 = new Set([own.name]), ls = [...given, ...frame.filter(l => !names2.has(l.name) && !!names2.add(l.name)), own], mm = forLaws(ls).m
      const g = obligations(mm, ls, {}, ls.length - 1)[1]!, last = g.hyps.at(-1)!
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
    const down = (c: Lit[], frame: Law[]): Lit[] => {
      let cur = c, queries = 0
      for (let part = Math.ceil(cur.length / 2); part >= 1 && queries < joinDownQueries && now() < jUntil && !stop(); part = part === 1 ? 0 : Math.ceil(part / 2)) {
        for (let i = 0; i < cur.length && cur.length > 1 && queries < joinDownQueries && now() < jUntil && !stop();) {
          const cand = [...cur.slice(0, i), ...cur.slice(i + part)]
          if (!cand.length || (initVec && inCube(cand, initVec)) || S.some(s2 => inCube(cand, s2))) { i += part; continue }
          queries++
          const r = queryWith(cand, frame)
          if (!r?.ok) { i += part; continue }
          const cut = cand.filter((_, j) => r.core.has(j))
          cur = cut.length && !(initVec && inCube(cut, initVec)) && !S.some(s2 => inCube(cut, s2)) ? cut : cand
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
        const ruling = within.filter(f => !ctx.includes(f) && !holdsRow(f, {...r.pre.scalars}))
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
    for (;;) {
      if (now() > jUntil || stop()) { why = 'time'; break }
      rounds++
      set = [...formsNow(), ...extras].filter(f => !blocked.has(textOf(f)))
      const byText = new Map(set.map(f => [textOf(f), f]))
      for (const [t, used] of stood) if (used.some(u => !byText.has(u))) stood.delete(t)
      const order = laws.map(l => l.name), inOrder = new Set(order)
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
      for (let attempt = 0; attempt <= joinAttempts; attempt++) {
        if (attempt === joinAttempts) ctx = whole
        const tq = performance.now(), out = stepWith(todo, todoForm, ctx)
        qms += Math.round(performance.now() - tq)
        if ('used' in out) {
          stood.set(todo, out.used!)
          opts.progress?.('join', {round: rounds, set: set.length, ms: qms, proven: todo.slice(0, 60), reads: out.used!.length, ctx: ctx.length, attempt})
          settled = true; break
        }
        lastStuck = out.stuck!
        if (!out.witness) { if (ctx === whole) break; ctx = whole; attempt = joinAttempts - 1; continue }
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
      const input = Object.fromEntries(m.inputs.map(i => [i, w[i] ?? 0])) as Request
      let post: State | undefined
      try { post = run.step(params, st, input) } catch { post = undefined }
      const pre = pointOf(params, st)
      // A model the interpreter reads otherwise (a remainder's term the kernel left free, a value past what doubles hold):
      // for a form, its goal is set aside; for a caller's law, the state is still one to rule out.
      const outside = !post || set.some(f => !holdsAt(f, pre))
      if (outside && !callers.has(todo)) { blocked.add(todo); opts.progress?.('join', {round: rounds, set: set.length, ms: qms, result: 'outside', goal: todo.slice(0, 60)}); continue }
      if (outside || breaks(params, post!)) {
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
        const pick = (fs: Form[]) => { let bestF: Form | undefined, score = -Infinity; for (const f of fs) { if (f.cells || f.cong || extras.includes(f) || blocked.has(textOf(f)) || holdsAt(f, pre) || !reached.every(p2 => holdsAt(f, p2))) continue; const sc = negs.reduce((k2, c) => k2 + (holdsAt(f, c) ? 0 : 1), 0) * 1000 - f.size; if (sc > score) (bestF = f, score = sc) } return bestF }
        const room = extras.length < joinExtras && tried < joinTries
        let next = room ? pick(pool) : undefined
        if (!next && room) { const made = fromCti(pre); pool.push(...made); next = pick(made) }
        if (next) tried++
        opts.progress?.('join', {round: rounds, set: set.length, ms: qms, target: next ? textOf(next).slice(0, 60) : 'none'})
        if (!next && !alone && cube()) continue
        if (!next) { why = 'target'; break }
        extras.push(next); continue
      }
      const after = post!, postP = pointOf(params, after)
      // (a model the interpreter reads otherwise, a quotient's term the kernel left free, say: nothing to join, and the
      // goal is set aside)
      if (!set.some(f => !holdsAt(f, postP))) { blocked.add(todo); opts.progress?.('join', {round: rounds, set: set.length, ms: qms, result: 'no violation', goal: todo.slice(0, 60)}); continue }
      const j0 = joins, d0 = dropped
      reach(postP)
      // short walks from the state joined: every state they reach is a successor of one the invariant holds at
      let walked = 0
      for (let t = 0, at = after, misses = 0; t < joinWalk && misses < 3; t++) {
        let inp: Request | undefined = randomInput(params, 4), next: State | undefined
        try { if (allowed(m, run, params, at, inp)) next = run.step(params, at, inp) } catch { next = undefined }
        if (!next && flagless) { inp = requestAt(params, at); try { if (inp) next = run.step(params, at, inp) } catch { next = undefined } }
        if (!next) { misses++; continue }
        if (breaks(params, next)) break
        reach(pointOf(params, next)); at = next; walked++
      }
      opts.progress?.('join', {round: rounds, set: set.length, ms: qms, goal: todo.slice(0, 60), joins: joins - j0, walked, dropped: dropped - d0})
    }
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
  for (let iter = 0; iter < 300 && now() < until && !stop(); iter++) {
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
    if (next) { chosen.push(next); continue }
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
  // Take out what the proof doesn't need, the last added first.
  for (const f of opts.minimize === false ? [] : [...chosen].reverse()) {
    if (now() > until || stop()) break
    const without = chosen.filter(g => g !== f), v = prove([...laws, ...without.map(lawFor)])
    if (v.proven && v.checked) (chosen = without, last = v)
  }
  const kept = chosen.flatMap(f => (f.mod ? [f.mod.k] : []))
  if (kept.length) rule?.dividesBy(...kept)
  trace('end', {proven: true, stopped: stop(), found: chosen.map(f => textOf(f)).join('; ')})
  return {...last, found: chosen.map(f => { const law = lawFor(f), text = law.name, source = sourceOf(f, text); return {law, text, ...(source ? {source} : {})} }), stats: stats(samples.length, forms.length, alive.length)}
}
