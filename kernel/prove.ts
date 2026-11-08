// An untrusted prover for the kernel: grows a split tree until every leaf's constraints are refuted by solve(), splitting
// on whatever atom the hypotheses leave open (an if's condition, a min's or ∸'s comparison, a disjunction's atoms, two
// reads of one map at keys not yet known equal or apart). Its trees go to kernel.check; nothing it says is trusted.
// What keeps it fast (research/perf/prover-bench.ts and prover-stress.ts measure each):
//   - the conclusion's atoms are split first: a case it never reads is often one no refutation needs;
//   - a node with a case still to split asks only "refuted or not": its Farkas rows first (solver.ts refuteFast), then
//     a bounded elimination; the full one, which a satisfiable system needs to the last variable, only at the leaves;
//   - a refutation of a split's yes side that never reads the split refutes its parent (lift), and the no side is skipped;
//   - a hypothesis' rows and open atoms, and every term inside them, are reused from an earlier path that decided the
//     same atoms they read (kernel.ts's reusing), so a new decision reads again only what it touches.
import {type C, type E, type Law, type Machine, cpair, evalC, evalE, walkOnce} from '../core/machine.ts'
import {type Lin, type Step, add, costs, env, k, refuteFast, scale, solve, sub, v, work} from '../core/solver.ts'
import {checkRefutation} from '../core/check.ts'
import {allowNode, allowTranslated, certCyclic, certOn, certSearch, stepCertFloor, translateMs, closingInsts, crossCyclic, type CyclicVerdict, cyclicOn, cycLog, hasQuantified, loopNodes, machineNodes, proveCyclic, reqTS, searchedStepNodes, skMachine, timedKind, withWitness, translatedProof, uncovered, uncoveredWhy} from '../core/cyclic.ts'
import type {TStats} from '../core/translate.ts'
import type {Cyclic} from './cyclic.ts'
import {proveSome, someLaws} from '../core/exists.ts'
import {REFUTED, growCdcl} from './cdcl.ts'
import {type Diagram, type Patterns, decide, eprMeter, pastEprCap, patternsOf, withEprCap} from './epr.ts'
import {projected, tupleParts} from './kernel.ts'
import {type Goal, type Instances, type Liveness, type Loop, type Path, type Seen, type StepLaw, type Tree, assumed, atomOf, boundOf, canon, canonFlip, cellParts, columnTerm, decided, factorsOf, isCell, isMonomial, stepZone, check, checkLaws, checkStepLaws, historyMachine, plainOf, substC, substE, leafConstraints, leafConstraintsReusing, reusing, linear, livenessHelpful, livenessParts, strongly, loopMachine, obligations, plainKey, progressObligations, stepLawObligations, trueC, truth, unreachable, witnessesOf, withProducts} from './kernel.ts'

// The atoms the path leaves open, in evaluation order: deciding any of them makes progress.
function openE(e: E, path: Path, out: Lin[]): void {
  switch (e.op) {
    case 'var': case 'const': return
    case 'mul': return openE(e.a, path, out)
    case 'prod': return (openE(e.a, path, out), openE(e.b, path, out))
    case 'get': return openE(e.key, path, out)
    case 'tup': return (openE(e.a, path, out), openE(e.b, path, out))
    case 'proj': return openE(e.a.op === 'tup' ? (e.k === 0 ? e.a.a : e.a.b) : e.a, path, out)
    case 'if': { const t = truth(e.c, path); if (t === undefined) openC(e.c, path, out); else openE(t ? e.then : e.else, path, out); return }
    case 'add': case 'sub': case 'min': case 'max': {
      openE(e.a, path, out), openE(e.b, path, out)
      const a = linear(e.a, path), b = linear(e.b, path)
      if (a && b && !decided(e, path)) out.push(e.op === 'sub' ? sub(b, a) : sub(a, b))
      return
    }
    default: return unreachable(e)
  }
}
function openC(c: C, path: Path, out: Lin[]): void {
  if (truth(c, path) !== undefined) return
  if (c.op === 'flag' || c.op === 'all') return
  if (c.op === 'not') return openC(c.x, path, out)
  if (c.op === 'and' || c.op === 'or') return c.xs.forEach(y => openC(y, path, out))
  // (two tuples equal: their parts' equalities, the kernel's reading)
  if (c.op === '=' && c.a.op === 'tup' && c.b.op === 'tup') return [c.a.a, c.a.b].forEach((x, i) => openC({op: '=', a: x, b: i ? (c.b as {b: E}).b : (c.b as {a: E}).a}, path, out))
  const a = linear(c.a, path), b = linear(c.b, path), own: Lin[] = []
  if (a && b) {
    const d = sub(a, b)
    if (c.op === '<=') own.push(d)
    else if (c.op === '<') own.push(add(d, k(1)))
    else own.push(d, scale(d, -1))
  }
  openE(c.a, path, out), openE(c.b, path, out)
  out.push(...own)
}
// A hypothesis is settled when it gives facts that are all its content: here, when its truth is decided, or it is a
// conjunction of settled parts / a linear comparison. A disjunction is settled only once one disjunct is left open and
// that one is settled: facts from its last disjunct are not all its content while a case inside it is still open.
function openH(c: C, path: Path, out: Lin[], positive = true): void {
  if (c.op === 'not') return openH(c.x, path, out, !positive)
  if ((c.op === 'and' && positive) || (c.op === 'or' && !positive)) return c.xs.forEach(y => openH(y, path, out, positive))
  if (c.op === 'and' || c.op === 'or') {
    if (truth(c, path) !== undefined) return
    const open = c.xs.filter(y => truth(y, path) !== !positive)
    if (open.length === 1) openH(open[0]!, path, out, positive)
    else openC(c, path, out)
    return
  }
  if (c.op === 'flag' || c.op === 'all') return
  if (c.op === '=' && c.a.op === 'tup' && c.b.op === 'tup') {
    const parts: C[] = [{op: '=', a: c.a.a, b: c.b.a}, {op: '=', a: c.a.b, b: c.b.b}]
    return openH(positive ? {op: 'and', xs: parts} : {op: 'or', xs: parts.map((x): C => ({op: 'not', x}))}, path, out, true)
  }
  const before = out.length
  openE(c.a, path, out), openE(c.b, path, out)
  if (out.length === before && !positive && c.op === '=' && truth(c, path) === undefined) openC(c, path, out)
}

// Pairs of reads of one map whose keys the path doesn't yet compare. With `pairedKeys.skip` (core/data.ts), reads at
// keys a pairing builds ((a + b)² + b, keys whose difference has monomials) are left uncompared: that encoding states
// their congruence as facts, and comparing their keys only brings products into leaves its linear rows decide.
export const pairedKeys = {skip: false}
// (each cell's map and key, and each pair's difference both ways, made once: the pairs are quadratic in the names, and
// the same forms at every node keep what is remembered per form)
// (by the first cell, then the second: no key text made per lookup, the search's nodes ask for every pair again)
const cellKeys = new Map<string, {map: string, key?: Lin, keys?: Lin[]}>(), cellPairs = new Map<string, Map<string, {d: Lin, neg: Lin, q0?: Lin, q1?: Lin}>>()
let cellPairsN = 0
export const cellPair = (a: string, b: string): {d: Lin, neg: Lin, q0?: Lin, q1?: Lin} => {
  let row = cellPairs.get(a)
  if (!row) cellPairs.set(a, (row = new Map()))
  let pair = row.get(b)
  if (!pair) {
    if (++cellPairsN > 200_000) { cellPairs.clear(); cellPairsN = 1; cellPairs.set(a, (row = new Map())) }
    const d = sub(cellKey(a).key ?? {}, cellKey(b).key ?? {})
    row.set(b, (pair = {d, neg: scale(d, -1)}))
  }
  return pair
}
const cellKey = (n: string) => { let c = cellKeys.get(n); if (!c) { if (cellKeys.size > 100_000) cellKeys.clear(); cellKeys.set(n, (c = cellParts(n))) } return c }
// Two tuple cells of one map: their parts compared one at a time, the first the path leaves open (each way), none
// once a part is decided apart. (Each part's difference made once per pair, as a plain key's.)
const tuplePairs = new Map<string, Lin[][]>()
// Two cells' parts as pairs of differences: [] for two keys of different shapes (never equal), undefined for plain keys.
export const tupleCellPairs = (a: string, b: string): Lin[][] | undefined => {
  const ka = cellKey(a).keys, kb = cellKey(b).keys
  if (!ka && !kb) return undefined
  if (!ka || !kb || ka.length !== kb.length) return []
  const id = `${a} ${b}`
  let ds = tuplePairs.get(id)
  if (!ds) { if (tuplePairs.size > 200_000) tuplePairs.clear(); tuplePairs.set(id, (ds = ka.map((k, i) => { const d = sub(k, kb[i]!); return [d, scale(d, -1)] }))) }
  return ds
}
const tupleOpen = (a: string, b: string, _ka: Lin[], _kb: Lin[], dec: (lin: Lin) => boolean | undefined): Lin | undefined => {
  for (const [d, neg] of tupleCellPairs(a, b)!) {
    const x = dec(d!), y = dec(neg!)
    if (x === undefined) return d
    if (x === true && y === undefined) return neg
    if (!(x && y)) return undefined
  }
  return undefined
}
function openCells(rows: {lin: Lin}[], path: Path): Lin[] {
  const seen = new Set<string>(), names: string[] = []
  for (const r of rows) for (const n in r.lin) if (!seen.has(n)) { seen.add(n); if (isCell(n)) names.push(n) }
  const out: Lin[] = []
  const cs = names.map(cellKey)
  const dec = (lin: Lin) => path.get(canon(lin))?.holds ?? (path.has(canonFlip(lin)) ? !path.get(canonFlip(lin))!.holds : undefined)
  for (let i = 0; i < names.length; i++) for (let j = i + 1; j < names.length; j++) {
    if (cs[i]!.map !== cs[j]!.map) continue
    if (cs[i]!.keys || cs[j]!.keys) { const t = cs[i]!.keys && cs[j]!.keys ? tupleOpen(names[i]!, names[j]!, cs[i]!.keys!, cs[j]!.keys!, dec) : undefined; if (t) out.push(t); continue }
    const pair = cellPair(names[i]!, names[j]!), d = pair.d
    if (pairedKeys.skip && Object.keys(d).some(isMonomial)) continue
    // Two cells of a run's map (core/cyclic.ts: time u and key k at u + k·Ω) at keys k·Ω and k'·Ω: k = k' first, a
    // linear atom; the keys' own difference only where k = k' (its other side then refuted by (k − k')·Ω = 0, a product).
    const q0 = cellProducts.on ? ('q0' in pair ? pair.q0 : (pair.q0 = quotient(d))) : undefined
    if (q0) {
      const q1 = (pair.q1 ??= scale(q0, -1))
      const qa = dec(q0), qb = dec(q1)
      if (qa === undefined) { out.push(q0); continue }
      if (qa === true && qb === undefined) { out.push(q1); continue }
      if (!(qa && qb)) continue
      cellDiffs.set(canon(d), q0); cellDiffs.set(canon(pair.neg), q1)
    }
    const a = dec(d), b = dec(pair.neg)
    if (a === undefined) out.push(d)
    else if (a === true && b === undefined) out.push(pair.neg)
  }
  return out
}
// A key difference q·F over monomials that share one factor F (Ω), with no other part: q, else undefined.
const quotient = (d: Lin): Lin | undefined => {
  const keys = Object.keys(d)
  if (!keys.length || keys.some(key => key === '1' || !isMonomial(key))) return undefined
  const shared = factorsOf(keys[0]!).find(f => keys.every(key => factorsOf(key).includes(f)))
  if (!shared) return undefined
  const out: Lin = {}
  for (const key of keys) { const fs = [...factorsOf(key)]; fs.splice(fs.indexOf(shared), 1); out[fs.join('*')] = (out[fs.join('*')] ?? 0) + d[key]! }
  return out
}
// The cells' key differences split at their quotient's equality, by canonical text: their quotient.
const cellDiffs = new Map<string, Lin>()
// A key's canonical text read back as its linear form.
export function parseKey(text: string): Lin {
  const out: Lin = {}
  let depth = 0, start = 0
  for (let i = 0; i <= text.length; i++) {
    const ch = text[i]
    if (ch === '[') depth++
    else if (ch === ']') depth--
    else if ((ch === ',' && depth === 0) || i === text.length) {
      if (i > start) { const part = text.slice(start, i), at = part.lastIndexOf(':'); out[part.slice(0, at)] = Number(part.slice(at + 1)) }
      start = i + 1
    }
  }
  return out
}

// Where a goal's time goes, when asked (research/perf/prover-bench.ts): each root goal's time, nodes, solver calls and
// the time in the solver and in building rows. Off unless `profile.on`; the counters cost nothing then.
export const profile: {on: boolean, goals: {name: string, ms: number, nodes: number, solves: number, solveMs: number, rowsMs: number, proven: boolean}[], solves: number, solveMs: number, rowsMs: number, nodes: number} =
  {on: false, goals: [], solves: 0, solveMs: 0, rowsMs: 0, nodes: 0}
const timed = <T>(f: () => T, add: (ms: number) => void): T => { if (!profile.on) return f(); const t = performance.now(); try { return f() } finally { add(performance.now() - t) } }
export const solveKinds: Record<string, {n: number, ms: number, rows: number}> = {}
const solveP = (rows: Parameters<typeof solve>[0], maxRows?: number): ReturnType<typeof solve> => {
  if (!profile.on) return solve(rows, maxRows)
  const t = performance.now(), out = solve(rows, maxRows), ms = performance.now() - t
  profile.solves++; profile.solveMs += ms
  const s = (solveKinds[out.kind] ??= {n: 0, ms: 0, rows: 0}); s.n++; s.ms += ms; s.rows += rows.length
  return out
}

// PROVE_TRACE=1 logs each goal grown from its root (hypotheses, nodes, time, outcome) to stderr.
// PROVE_DUMP: a hook research/perf/prof sets to read each root goal.
export let proveDump: ((goal: Goal) => void) | undefined
export const setProveDump = (f: ((goal: Goal) => void) | undefined) => { proveDump = f }
const proveTrace = !!env.PROVE_TRACE
// `why`, when the budget ran out: which limit, at what size, and what usually helps.
// Set while core/cyclic.ts grows its goals.
export const cellProducts = {on: false}
// (`diagram`: a model the EPR path found, as a structure: kernel/epr.ts's Diagram)
export type Outcome = {tree: Tree, nodes: number} | {stuck: 'sat' | 'unknown', witness?: Record<string, number>, diagram?: Diagram, path: Path, why?: string}

// The budget: 200,000 nodes and, by default, a second per hypothesis (at least 20 seconds) per goal, on the counted
// clock inside `counted` and in the cost model's work outside it (`withWork`); past either the goal is left `unknown`. A goal with many instances (a law about two keys at its pairs) has that many more rows per leaf.
// A deadline every goal grown inside `withDeadline` keeps, beside its own budget: a search that proves many things (core/
// infer.ts, core/discover.ts, the search proveRule falls back on) bounds them all; a goal past it is left `unknown`.
let deadline = Infinity, deadlineEpr = 0
// EPR has its own work counter. Debit it from a counted deadline, not from clock(): the protocol engine already
// accounts for EPR in its own clock. A scope's anchor charges all its queries, including nested and failed ones.
const eprTimeSince = (start: number): number => rate ? (eprMeter.n - start) / rate : 0
// The clock every budget here reads (grow's `until`, withDeadline's; core/cyclic.ts's and core/data.ts's searches): wall
// time, or within `counted` the work the prover has done (the solver's rows read and made, each node's rows), `perMs`
// units a millisecond, so that what a search's budget lets it try, and so its verdict, doesn't depend on the machine's
// speed. A counted search inside another reads the outer's clock.
// With `full`, the clock reads the cost model below in place of work.n.
let rate = 0, meter = (): number => work.n
export const clock = (): number => (rate ? meter() / rate : performance.now())
export function counted<T>(perMs: number, f: () => T, full = false): T {
  if (rate) return f()
  const outer = deadline
  rate = perMs; deadline = Infinity; meter = full ? fullWork : () => work.n
  try { return f() } finally { rate = 0; deadline = outer }
}
// The cost model: what a query does, by kind (core/solver.ts's costs), each weighed to the milliseconds a Modal 2-vCPU
// container takes for it, `fullRate` units a millisecond at the median query: elimination's pairs and the float
// simplex's cells, the plain search's rows a node (kernel.ts's reading, whole at each node), the values reader.ts finds
// again, the live rows' copies it keeps and the read edges a change walks, the candidates scanned, the pivots' rows,
// the root's rows for units, the unfolding's rows a leaf, the goal's nodes where a query starts. work.n counts the rows
// the solver and each node read, which the incremental search reads whole no more: on 7,027 root queries of 20 ms or
// more (research/query/fit.py on runs/query/cal2: the 332 step goals, CHC sat and unsat, ITS, the false step goals and
// the real-world corpus), work.n did 28 to 377 units a ms (p10, p90), the model 120 to 401.
const model: [keyof typeof costs, number][] = [['fm', 2.33], ['fcells', 0.0123], ['plainRows', 7.93], ['values', 0.672], ['copies', 0.735], ['edges', 0.0435],
  ['scan', 0.0765], ['pivotRows', 0.599], ['unitRows', 15.6], ['unfoldRows', 0.735], ['goalNodes', 0.492], ['translateRows', 7.93]]
export const fullRate = 250
export const fullWork = (): number => { let n = 0; for (const [k, w] of model) n += w * costs[k]; return n }
// A goal's own budget where its caller gives none, outside a counted search: the cost model's work, groundRate units a
// millisecond of the budget (below fullRate: the queries of 10 s or more did 163 to 271 units a ms at their median, by
// group of the run above, so a long goal's budget takes about the wall time it had), so a goal left unknown is left so
// on any machine; a deadline it is grown within stays.
const groundRate = 180
let workCap = Infinity
export const withWork = <T>(cap: number, f: () => T): T => { const outer = workCap; workCap = Math.min(outer, cap); try { return f() } finally { workCap = outer } }
// Past a budget's end on the clock, or past the work a goal's own budget allows.
// A wall-clock end beside the clock's (withWall: the search's own end, core/dsl.ts): work the counted clock doesn't count
// (the EPR path's propositional search, a node's propagation, building a large goal's rows) stops there too, and past it
// every goal is left unknown, whatever its own budget. Untrusted: it only stops a search.
let wallEnd = Infinity
export const pastWall = (): boolean => wallEnd !== Infinity && performance.now() > wallEnd
export function withWall<T>(end: number, f: () => T): T {
  const outer = wallEnd
  wallEnd = Math.min(outer, end)
  try { return f() } finally { wallEnd = outer }
}
// Past the wall or the deadline in force: a goal grown now is left unknown at once.
const ranOut = (): boolean => pastWall() || withinDeadline(Infinity) <= clock()
// (the wall's end in force, Infinity where none: a search inside that stops itself there)
export const wallAt = (): number => wallEnd
export const late = (until: number): boolean => clock() > until || (workCap !== Infinity && fullWork() > workCap) || pastWall()
// A budget's end, within the deadline (a translation's own bound, core/cyclic.ts's, kept by the export's GDP_CERT_MS).
export const withinDeadline = (until: number): number => Math.min(until, deadline - eprTimeSince(deadlineEpr))
export function withDeadline<T>(until: number, f: () => T): T {
  const outer = deadline, outerEpr = deadlineEpr
  deadline = withinDeadline(until); deadlineEpr = eprMeter.n
  try { return f() } finally { deadline = outer; deadlineEpr = outerEpr }
}
// `units: false`: the goal's own order, no units first (a caller after a model, not a proof: a run guided by the
// prover's witnesses, say, whose models units would steer).
export function grow(goal: Goal, path: Path = new Map(), budget?: {nodes: number, until?: number, units?: boolean}): Outcome {
  if (pastWall()) return {stuck: 'unknown', path, why: outOfBudget(goal, 'time', path.size)}
  if (!budget) {
    const ms = Math.max(20_000, 1_000 * goal.hyps.length)
    if (!rate) return withWork(fullWork() + groundRate * ms, () => grow(goal, path, {nodes: 0}))
    budget = {nodes: 0, until: clock() + ms}
  }
  const end = withinDeadline(budget.until ?? Infinity)
  if (end < (budget.until ?? Infinity)) budget.until = end
  if (budget.units === false && unitsNow) { unitsNow = false; try { return grow(goal, path, budget) } finally { unitsNow = true } }
  if (proveDump && !path.size && !budget.nodes) { proveDump(goal); }
  if (proveTrace && !path.size && !budget.nodes) {
    const t = performance.now(), out = growRoot(goal, path, budget)
    console.error(`[grow] ${goal.name}: ${goal.hyps.length} hyps, ${budget.nodes} nodes, ${Math.round(performance.now() - t)} ms, ${'tree' in out ? 'proven' : `${out.stuck}${out.why ? ` (${out.why})` : ''}`}`)
    return out
  }
  // (a root goal grown before within `withTrees`: its tree again; a tree is the kernel's to check wherever it goes)
  const key = treeCache.on && !path.size && !budget.nodes ? treeKey(goal) : undefined, had = key === undefined ? undefined : treeCache.trees.get(key)
  if (had) return {tree: had, nodes: 0}
  if (key !== undefined) { const out = growKept(goal, path, budget); if ('tree' in out) treeCache.keep(key, out.tree); return out }
  return growKept(goal, path, budget)
}
// Trees of root goals kept by their hypotheses (and the search's modes) while `withTrees` runs: core/infer.ts proves each
// law of a set alone (proveLaw) and then the set as a whole (proveRule), the same goals twice. At most 2,000 trees, and
// goals of at most 4 MB written out.
const treeCache = {on: 0, trees: new Map<string, Tree>(), keep(key: string, tree: Tree) { if (this.trees.size >= 2000) this.trees.clear(); this.trees.set(key, tree) }}
const treeKey = (goal: Goal): string | undefined => { const text = JSON.stringify(goal.hyps); return text.length > 4_000_000 ? undefined : `${cellProducts.on ? 1 : 0}${unitsNow ? 1 : 0}${text}` }
// GDP_TREES=0: no tree kept (each goal grown every time it is asked).
const keepTrees = env.GDP_TREES !== '0'
export function withTrees<T>(f: () => T): T {
  if (!keepTrees) return f()
  treeCache.on++
  try { return f() } finally { if (--treeCache.on === 0) treeCache.trees.clear() }
}
// Each root query as it ends, for research's logs (research/query/log.ts sets it; off otherwise): the kind, the goal,
// its wall time and counted work, its outcome, and how many queries it is inside.
export const queryHook: {on?: (q: {kind: string, goal: Goal, ms: number, work: number, out: Outcome, depth: number}) => void, depth: number} = {depth: 0}
export function logged(kind: string, goal: Goal, f: () => Outcome): Outcome {
  const t0 = performance.now(), w0 = work.n
  queryHook.depth++
  try { const out = f(); queryHook.on?.({kind, goal, ms: performance.now() - t0, work: work.n - w0, out, depth: queryHook.depth - 1}); return out } finally { queryHook.depth-- }
}
function growKept(goal: Goal, path: Path, budget: {nodes: number, until?: number, units?: boolean}): Outcome {
  if (queryHook.on && !path.size && !budget.nodes && !queryHook.depth) return logged('grow', goal, () => growKept0(goal, path, budget))
  return growKept0(goal, path, budget)
}
function growKept0(goal: Goal, path: Path, budget: {nodes: number, until?: number, units?: boolean}): Outcome {
  if (!profile.on || path.size || budget.nodes) return growRoot(goal, path, budget)
  const t = performance.now(), s0 = profile.solves, m0 = profile.solveMs, r0 = profile.rowsMs, n0 = profile.nodes
  const out = growRoot(goal, path, budget)
  profile.goals.push({name: goal.name, ms: performance.now() - t, nodes: profile.nodes - n0, solves: profile.solves - s0, solveMs: profile.solveMs - m0, rowsMs: profile.rowsMs - r0, proven: 'tree' in out})
  return out
}
// The share of a root goal's budget the CDCL search gets (GDP_CDCL_SHARE; 0 turns it off), and the quick search's nodes
// before it (GDP_QUICK_CAP; 64 where the CDCL search isn't tried, as before it): research/step's comparisons.
const cdclShare = Number(env.GDP_CDCL_SHARE ?? 0.75), quickCap = Number(env.GDP_QUICK_CAP ?? 16)
// The EPR path (kernel/epr.ts): a root goal of a rule with a composed key, its hypotheses EPR-shaped (keys tuples of
// their parts, cells few-valued, no counter, sum or product), decided first by its abstraction. A model of the goal (the
// abstraction's, judged on every hypothesis by the interpreter) is the goal's model; a refutation's core (a few
// hypotheses) is proven by the usual search, within half the goal's budget, and widened to the whole goal (`widen`), whose
// tree the kernel checks as any; anything else, the usual search. Untrusted. GDP_EPR=0 turns it off.
const eprOn = env.GDP_EPR !== '0'
export const eprScope: {patterns?: Patterns, busy?: boolean} = {}
const withPatterns = <T>(m: Machine, laws: Law[], f: () => T): T => {
  if (!eprOn || eprScope.patterns) return f()
  const p = patternsOf(plainOf(m), laws)
  if (!Object.values(p).some(c => c.length > 1)) return f()
  eprScope.patterns = p
  try { return f() } finally { eprScope.patterns = undefined }
}
// (`whole: false`: the core's tree alone, not widened to the goal, with the core (`part`); decideLaw's, whose caller's
// verdict rests on its own final proof: a refutation of some of a goal's hypotheses refutes the goal)
// (`refuted`: the last decision refuted the goal and its core's proof didn't finish: a model from fewer instances, asked
// before, is then no answer, as the abstraction refutes it at these)
const eprLast = {refuted: false}
function eprFirst(goal: Goal, budget: {nodes: number, until?: number}, whole = true, stop = (): boolean => pastWall() || pastEprCap()): (Outcome & {part?: Goal, core?: number[]}) | undefined {
  eprLast.refuted = false
  const start = eprMeter.n, until = budget.until ?? Infinity
  const d = decide(goal, eprScope.patterns!, {exact: true, late: () => stop() || late(withinDeadline(until - eprTimeSince(start)))})
  // The local goal's remaining allowance also reaches the core proof or fallback search.
  if (budget.until !== undefined) budget.until = until - eprTimeSince(start)
  if ('unknown' in d) return undefined
  if (d.sat) return {stuck: 'sat', witness: d.witness, diagram: d.diagram, path: new Map(), why: 'a model'}
  const last = goal.hyps.length - 1, core = d.core.includes(last) ? d.core : [...d.core, last], part: Goal = {name: goal.name, hyps: core.map(i => goal.hyps[i]!)}
  const now = clock(), end = withinDeadline(budget.until ?? Infinity), w = fullWork()
  eprScope.busy = true
  try {
    const share = whole ? 0.5 : 1
    const out = withWork(workCap === Infinity ? Infinity : w + share * (workCap - w), () => grow(part, new Map(), {nodes: 0, until: end === Infinity ? end : now + share * (end - now)}))
    if (!('tree' in out)) { eprLast.refuted = true; return undefined }
    if (!whole) return {...out, part, core}
    const tree = widen(part, goal, out.tree)
    return tree ? {tree, nodes: out.nodes} : undefined
  } finally { eprScope.busy = false }
}
// Wide goals (GDP_WIDE hypotheses or more, a law at every tuple of a goal's keys, a step's every write, and
// GDP_WIDE_TERMS terms): each node of the search reads every hypothesis' rows, so a goal of a thousand reaches neither a
// tree nor a model within its budget, though its refutation reads one or two and a model of a few is often a model of
// all. Grown first over a part: the conclusion, then the hypotheses a model of the part breaks (the model read as a
// state: each cell at its key's value, any other name 0), those sharing a cell with the part first, the part doubled a
// round. A model that breaks none is the goal's (every hypothesis holds at it); a tree is widened to the goal (`widen`),
// which the kernel checks as any; a model-only query's refutation is the part's, its core the part's hypotheses. Within
// a share of the goal's budget, each round within what the whole's search would spend on as many nodes; anything else
// leaves the goal as before. Untrusted.
const wideAt = Number(env.GDP_WIDE ?? 256), wideTerms = Number(env.GDP_WIDE_TERMS ?? 40_000), wideShare = Number(env.GDP_WIDE_SHARE ?? 0.25), wideTrace = !!env.GDP_WIDE_TRACE
let wideBusy = false
// (while a part is grown: whether a point holds every hypothesis of the part, read as a state; a node's point that does is
// the part's model, whatever atoms are still open, and the whole's if it breaks none of the rest)
export const wideScope: {judge?: (w: Record<string, number>) => boolean} = {}
export const wideStats = {goals: 0, trees: 0, models: 0, rounds: 0}
export const wideHook: {on?: (part: Goal, out: Outcome) => void} = {}
const cellsIn = (c: unknown): Set<string> => { const out = new Set<string>(); walkOnce(c, o => { const x = o as {op?: string, map?: string, key?: unknown}; if (x.op === 'get') out.add(`${x.map}${JSON.stringify(x.key)}`) }); return out }
// (the hypotheses a model breaks among `ids` (all where none are given), the model read as a state, the conclusion first;
// `first`: the first one broken alone)
// (`defaults`: a map's cells the model leaves out read at that value, not the map's start)
export const brokenOf = (goal: Goal): ((w: Record<string, number>, ids?: number[], first?: boolean, defaults?: Record<string, number>) => number[]) => {
  const maps = new Set<string>()
  walkOnce(goal.hyps, o => { const x = o as {op?: string, map?: unknown}; if (x.op === 'get' && typeof x.map === 'string') maps.add(x.map) })
  const mm = {maps: Object.fromEntries([...maps].map(mp => [mp, 0]))} as unknown as Machine
  return (w0, ids = goal.hyps.map((_, i) => i), first = false, defaults) => {
    // (a term column's value is its term's at the point, not the point's own where its choice is open: each cell is put
    // at its key's value with the columns so read, twice, as a column's term may read a cell)
    const w = {...w0}, at = new Proxy(w, {get: (t, q: string) => t[q] ?? 0}) as Record<string, number>, out: number[] = []
    let st = {scalars: {}, maps: {} as Record<string, Map<number, number>>, ...(defaults ? {defaults} : {})}
    for (let pass = 0; pass < 3; pass++) {
      if (pass) for (const n in w) { const e = n.startsWith('⟦') ? columnTerm(n) : undefined; if (e) try { w[n] = evalE(e, at, st, mm) } catch { /* left */ } }
      st = {scalars: {}, maps: Object.fromEntries([...maps].map(mp => [mp, new Map<number, number>()])), ...(defaults ? {defaults} : {})}
      for (const [cell, value] of Object.entries(w)) {
        const br = cell.indexOf('['), key = br > 0 && cell.endsWith(']') && st.maps[cell.slice(0, br)] ? keyValue(cell, w) : undefined
        if (key !== undefined) st.maps[cell.slice(0, br)]!.set(key, value)
      }
    }
    for (let q = ids.length - 1; q >= 0 && !(first && out.length); q--) {
      const i = ids[q]!
      let ok = false
      try { ok = evalC(goal.hyps[i]!, at, st, mm) } catch { /* broken */ }
      if (!ok) out.push(i)
    }
    return out.reverse()
  }
}
// (`ask`: how a part is asked, a tree wanted by default; kernel/cdcl.ts's model-only queries ask for a model or a
// refutation, whose core is the part's hypotheses, the whole's by index)
// (and its terms, each shared part once, past GDP_WIDE_TERMS: what each node of the whole goal's search reads, where the
// search is costly; under it the whole is asked as before, its model the search's own, which the engine's join reads)
const termsSeen = new WeakMap<Goal, number>()
const termsOf = (goal: Goal): number => { let n = termsSeen.get(goal); if (n === undefined) { n = 0; walkOnce(goal.hyps, () => { n!++ }); termsSeen.set(goal, n) } return n }
export const wideFor = (goal: Goal): boolean => !wideBusy && goal.hyps.length >= wideAt && termsOf(goal) >= wideTerms
// (`keep`: a part's tree kept as the part's, with the part and its hypotheses' indices in the whole as its core, not
// widened: settle's, whose final proof is made over the instances its proofs read)
export function growWide(goal: Goal, budget: {nodes: number, until?: number}, ask = (g: Goal, until: number): Outcome & {core?: number[]} => grow(g, new Map(), {nodes: 0, until}), keep = false): (Outcome & {core?: number[], part?: Goal}) | undefined {
  const hyps = goal.hyps, last = hyps.length - 1, broken = brokenOf(goal), now = clock(), w = fullWork()
  const end = withinDeadline(budget.until ?? Infinity), span = wideShare * (end - now), room = wideShare * (workCap - w), until = now + span
  const part = new Set<number>([last]), near = new Set(cellsIn(hyps[last])), cells = new Map<number, Set<string>>()
  const cellsAt = (i: number) => { let c = cells.get(i); if (!c) cells.set(i, (c = cellsIn(hyps[i]))); return c }
  const take = (i: number) => { part.add(i); for (const x of cellsAt(i)) near.add(x) }
  wideBusy = true
  wideStats.goals++
  try {
    while (!late(until)) {
      wideStats.rounds++
      // (a part's own budget: what the whole's search spends on as many nodes, four times over (a node of the part reads
      // that much less), at least a sixteenth of the share: a part that a small budget doesn't settle leaves the goal)
      const ids = [...part].sort((a, b) => a - b), g: Goal = {name: goal.name, hyps: ids.map(i => hyps[i]!)}, f = Math.max(1 / 16, Math.min(1, 4 * part.size / hyps.length))
      const t0 = performance.now(), at = clock()
      wideScope.judge = w => !broken(w, ids, true).length
      let out: Outcome & {core?: number[]}
      try { out = withWork(Math.min(w + room, fullWork() + f * room), () => ask(g, Math.min(until, at + f * span))) } finally { wideScope.judge = undefined }
      wideHook.on?.(g, out)
      if (wideTrace) console.error(`[wide] ${goal.name.slice(0, 40)}: part ${g.hyps.length} of ${hyps.length}, ${'tree' in out ? 'tree' : out.stuck} in ${Math.round(performance.now() - t0)} ms${'tree' in out ? '' : ` ${out.why?.slice(0, 50) ?? ''}`}`)
      if ('tree' in out && keep) { wideStats.trees++; return {tree: out.tree, nodes: out.nodes, part: g, core: ids} }
      if ('tree' in out) { const tree = withWork(w + room, () => withDeadline(until, () => widen(g, goal, out.tree))); if (tree) wideStats.trees++; return tree && {tree, nodes: out.nodes} }
      if (out.why === REFUTED) return {...out, ...(out.core ? {core: out.core.map(i => ids[i]!)} : {})}
      if (out.stuck !== 'sat' || !out.witness) return undefined
      const bad = broken(out.witness)
      if (wideTrace) console.error(`[wide]   breaks ${bad.length}${bad.length ? `: ${bad.slice(0, 12).join(' ')}` : ''}`)
      if (!bad.length) { wideStats.models++; return {...out, path: new Map()} }
      const more = bad.filter(i => !part.has(i)), size = part.size
      if (!more.length || 2 * size > hyps.length) return undefined
      // (what the model breaks, those sharing a cell with the part first; then, to twice the part, the hypotheses that share
      // one, then any, in the goal's order: the rounds are as many as the doublings to the part that settles the goal)
      const shared = (i: number) => [...cellsAt(i)].some(x => near.has(x))
      more.sort((a, b) => Number(shared(b)) - Number(shared(a)))
      for (const i of more.slice(0, Math.max(16, size))) take(i)
      for (const any of [false, true]) for (let i = 0; i < last && part.size < 2 * size; i++) if (!part.has(i) && (any || shared(i))) take(i)
    }
    return undefined
  } finally { wideBusy = false }
}
// (the abstraction of a whole wide goal, quadratic in its cells, within GDP_WIDE_EPR units: i4's learning switch's
// largest decision otherwise 0.47M, its engine set's step goal of 7,590 hypotheses 19M, past its caller's end, in 10 GB)
const wideEprUnits = Number(env.GDP_WIDE_EPR ?? 2_000_000), wideParts = env.GDP_WIDE_PARTS !== '0'
// (only where the rule has tuple keys, its patterns n zeros: radix-keyed rules keep main's path, consensus_wo_decide's
// and ring_leader_election's proofs among them, lost to it at 60 s)
const tupledScope = (): boolean => !!eprScope.patterns && Object.values(eprScope.patterns).some(c => c.length > 1 && c[0] === 0)
// (a part of a wide goal by the EPR path first, its core widened to the part, else the usual search)
const eprPart = (gp: Goal, until: number): Outcome => eprFirst(gp, {nodes: 0, until}) ?? grow(gp, new Map(), {nodes: 0, until})
function growRoot(goal: Goal, path: Path, budget: {nodes: number, until?: number}): Outcome {
  const wide = !path.size && !budget.nodes && wideFor(goal), epr = !!eprScope.patterns && !eprScope.busy
  // (a wide goal's parts by the EPR path too, where the goal is EPR-shaped)
  if (wide) { const out = epr && wideParts && tupledScope() ? growWide(goal, budget, eprPart) : growWide(goal, budget); if (out) return out }
  // (not for a wide goal's part: its abstraction's search reads no judge, and the whole goal is decided by it after)
  if (epr && !wideBusy && !path.size && !budget.nodes) { const out = wide && tupledScope() ? withEprCap(wideEprUnits, () => eprFirst(goal, budget)) : eprFirst(goal, budget); if (out) return out }
  // Past a few cases, CDCL over the atoms (kernel/cdcl.ts), with most of the budget: a linear goal's refutation there
  // is a resolution of short clauses, which the tree search would find again in every case that reaches one. Unknown
  // there, the plain search, the cuts and the plain search again have the rest. Not for a law over k steps in a row
  // (kernel.ts names its goals `@k steps`): the cuts make its tree a chain of one step's refutations, which the CDCL
  // search's tree, unfolded, repeats (research/step: four times the Lean text of examples/steps.ts). Nor for products.
  // (past the wall, not even the root's rows: a large goal's take a second)
  if (pastWall()) return {stuck: 'unknown', path, why: outOfBudget(goal, 'time', path.size)}
  const root = path.size === 0 && budget.nodes === 0 ? leafConstraints(goal, path) : undefined
  const cdcl = !!root && cdclShare > 0 && !cellProducts.on && Number(/@(\d+) steps/.exec(goal.name)?.[1] ?? 1) <= 1 && !root.some(r => Object.keys(r.lin).some(isMonomial))
  // At the root: plainly first; where the cases multiply past a budget, through cuts. The plain budget halves with each
  // two open choices (what a plain search's cases grow by), so a long run's steps reach the cuts early.
  if (root && unitFirst && unitsNow && !(eprScope.busy && tupledScope())) {
    // A goal that a few cases settle needs no units (finding them costs a Farkas check per atom); the rest get them.
    unitsNow = false
    try {
      const quick = growPlain(goal, path, {nodes: 0, until: budget.until, cap: cdcl ? quickCap : 64})
      if ('tree' in quick || quick.stuck === 'sat' || quick.why === undefined) return quick
    } finally { unitsNow = true }
  }
  if (root) {
    if (cdcl) {
      const now = clock(), end = withinDeadline(budget.until ?? Infinity), w = fullWork()
      const out = withWork(workCap === Infinity ? Infinity : w + cdclShare * (workCap - w), () => growCdcl(goal, path, {nodes: 0, until: end === Infinity ? end : now + cdclShare * (end - now)}))
      // (with `realModels.on`, a model whose products don't multiply out is no model: the CDCL search reads a product as
      // a name of its own, where the plain search below multiplies rows; a goal whose products only its cases bring,
      // core/nonterm.ts's x' := x·y)
      if ('tree' in out || (out.stuck === 'sat' && !(realModels.on && fakeProducts(out.witness)))) return out
    }
    const open = new Set(root.flatMap(r => Object.keys(r.lin)).filter(n => n.startsWith('⟦') && columnTerm(n)?.op === 'if')).size
    const plain = growPlain(goal, path, {nodes: 0, until: budget.until, cap: Math.max(32, Math.round(4_000 / 2 ** (open / 2)))})
    if ('tree' in plain || plain.stuck === 'sat' || plain.why === undefined) return plain
    const cut = withCuts(goal, path, budget)
    if (cut) return cut
  }
  return growPlain(goal, path, budget)
}
// A CDCL model whose products don't multiply out is no model (GDP_REAL_MODELS=0: taken as one, as before): its
// monomials are names of their own there, so x' = (t − last)·rate may read 0 with rate = 1 and t − last = 1, where
// the plain search multiplies the factors' rows (x/time/rate's refill, a rank-0 step goal).
export const realModels = {on: env.GDP_REAL_MODELS !== '0'}
const fakeProducts = (w: Record<string, number> | undefined): boolean => !!w && Object.keys(w).some(key => isMonomial(key) && (w[key] ?? 0) !== factorsOf(key).reduce((acc, f) => acc * (w[f] ?? 0), 1))
function growPlain(goal: Goal, path: Path, budget: {nodes: number, until?: number, cap?: number}): Outcome {
  if (budget.cap !== undefined && budget.nodes >= budget.cap) return {stuck: 'unknown', path, why: 'cap'}
  if (profile.on) profile.nodes++
  if (++budget.nodes > 200_000 || late(budget.until ?? Infinity)) return {stuck: 'unknown', path, why: outOfBudget(goal, budget.nodes > 200_000 ? 'nodes' : 'time', path.size)}
  // Rows that read a term column only once a cut has put one on the path; before, the rows a choice-free search uses
  // (what it saw before term columns), renumbered to the whole leaf's when a leaf is found.
  const full = timed(() => rowsAt(goal, path), ms => { profile.rowsMs += ms })
  work.n += 1 + full.length
  costs.plainNodes++; costs.plainRows += full.length
  const columns = [...path.values()].some(a => Object.keys(a.lin).some(key => key.startsWith('⟦')))
  const idx = full.flatMap((r, i) => (columns || !Object.keys(r.lin).some(key => key.startsWith('⟦')) ? [i] : []))
  const rows = idx.map(i => full[i]!), at = (i: number) => (i < rows.length ? idx[i]! : full.length + i - rows.length)
  const leafOf = (steps0: Step[], products0?: [number, number][], squares0?: Lin[]): Tree => {
    const {steps, products, squares} = products0 || squares0 ? trimmed(rows.length, steps0, products0 ?? [], squares0 ?? []) : {steps: steps0, products: undefined, squares: undefined}
    return {leaf: steps.map(st => (st.kind === 'input' ? {...st, index: at(st.index)} : st)), ...(products?.length ? {products: products.map(([i, j]) => [at(i), at(j)] as [number, number])} : {}), ...(squares?.length ? {squares} : {})}
  }
  const next = openAt(goal, path, rows).find(lin => Object.keys(lin).some(key => key !== '1') && !path.has(canon(lin)) && !path.has(canonFlip(lin)))
  // With a case still to split, only "refuted or not" matters (a witness here goes unused): a large system is tried by
  // its Farkas rows alone, and left to the split if they don't refute it. Elimination to the last variable, which a
  // satisfiable system needs to say so, is kept for small systems and for the leaves, where its answer is the outcome.
  // Past the Farkas rows, elimination still runs, bounded (a refutation the rationals miss is an integer one, which
  // elimination's cuts find early; a satisfiable system grows past the bound and is left to the split).
  if (next && rows.length > 60) {
    const fast = timed(() => refuteFast(rows), ms => { profile.solves++; profile.solveMs += ms })
    if (fast?.kind === 'refuted') return {tree: leafOf(fast.steps), nodes: budget.nodes}
  }
  const verdict: ReturnType<typeof solve> = next && rows.length > 60 ? solveP(rows, 2 * rows.length) : solveP(rows)
  if (verdict.kind === 'refuted') return {tree: leafOf(verdict.steps), nodes: budget.nodes}
  if (next && wideScope.judge && verdict.kind === 'sat' && wideScope.judge(verdict.witness)) return {stuck: 'sat', witness: verdict.witness, path}
  // Before a split, the rows the plain search sets aside (those reading a term column) by their Farkas rows: an open
  // choice's bounds (min(a, c) ≤ c) often refute the case whichever way the choice goes, so its cases need no split.
  if (next && !columns && full.length > rows.length) {
    const fast = timed(() => refuteFast(full), ms => { profile.solves++; profile.solveMs += ms })
    if (fast?.kind === 'refuted') return {tree: {leaf: fast.steps}, nodes: budget.nodes}
  }
  let split = next ?? (verdict.kind === 'unknown' ? bisect(rows, path) ?? fractional(verdict.point, path) : undefined)
  // A cell difference's failing side (k = k' on the path, the keys apart): (k − k')·Ω = 0 refutes it, a product of each
  // of the path's two atoms k − k' <= 0 and k' − k <= 0 with Ω >= 0.
  if (cellProducts.on && path.size) {
    const [id, last] = [...path].at(-1)!, q0 = !last.holds ? cellDiffs.get(id) : undefined
    if (q0) {
      const at = (lin: Lin) => rows.findIndex(r => canon(r.lin) === canon(lin))
      const d = last.lin, f = factorsOf(Object.keys(d)[0]!).find(x => !Object.keys(q0).includes(x) && Object.keys(d).every(key => factorsOf(key).includes(x)))
      const e1 = at(q0), e2 = at(scale(q0, -1)), sign = f === undefined ? -1 : at({[f]: -1})
      if (e1 >= 0 && e2 >= 0 && sign >= 0) {
        const pairs: [number, number][] = [[e1, sign], [e2, sign]], out = solve(withProducts(rows, pairs))
        if (out.kind === 'refuted') return {tree: leafOf(out.steps, pairs), nodes: budget.nodes}
      }
    }
  }
  // Products: with monomials about, try every pair of rows multiplied; failing that, split a factor at zero.
  const monomials = rows.some(r => Object.keys(r.lin).some(isMonomial))
  // A witness that multiplies out (each monomial's value is its factors' product) is a real model: nothing to refute.
  if (!split && monomials && verdict.kind === 'sat') {
    const w = verdict.witness, value = (key: string) => w[key] ?? 0
    const real = rows.every(r => Object.keys(r.lin).every(key => !isMonomial(key) || value(key) === factorsOf(key).reduce((acc, f) => acc * value(f), 1)))
    if (real) return {stuck: 'sat', witness: w, path}
  }
  // An equation about a factor (x' = x + 1, a run's next state as a cell) times each factor's sign: e·f = 0 for every
  // factor f, so a monomial of x' is one of x (x'·x' = (x + 1)²). Whatever the number of rows: there are few such pairs.
  // Only for cyclic proofs (core/cyclic.ts, whose runs keep each next state as a cell): the usual rules substitute it.
  if (!split && monomials && cellProducts.on) {
    const factorSet = new Set(rows.flatMap(r => Object.keys(r.lin).filter(isMonomial).flatMap(factorsOf)))
    const byCanon = new Map(rows.map((r, i) => [canon(r.lin), i]))
    const eqs = rows.flatMap((r, i) => (Object.keys(r.lin).some(key => key !== '1' && factorSet.has(key)) && byCanon.has(canon(scale(r.lin, -1))) ? [i] : []))
    const signs = rows.flatMap((r, i) => { const keys = Object.keys(r.lin); return keys.length === 1 && factorSet.has(keys[0]!) && r.lin[keys[0]!]! < 0 ? [i] : [] })
    const pairs = eqs.flatMap(i => signs.map(j => [i, j] as [number, number])).slice(0, 200)
    if (pairs.length) {
      const sub = solve(withProducts(rows, pairs))
      if (sub.kind === 'refuted') return {tree: leafOf(sub.steps, pairs), nodes: budget.nodes}
      // Then every linear row about a factor (n >= x: (n − x)·d >= 0) times each sign, past the forty rows the pairs
      // below are kept to.
      const about = rows.flatMap((r, i) => (!eqs.includes(i) && Object.keys(r.lin).some(key => key !== '1' && factorSet.has(key)) && !Object.keys(r.lin).some(isMonomial) ? [i] : []))
      const more = [...pairs, ...about.flatMap(i => signs.map(j => [i, j] as [number, number]))].slice(0, 400)
      if (more.length > pairs.length) {
        const ineq = solve(withProducts(rows, more))
        if (ineq.kind === 'refuted') return {tree: leafOf(ineq.steps, more), nodes: budget.nodes}
      }
    }
  }
  // Past forty rows, every pair is too many: each monomial x·y's factors' bounds (rows of x alone, of y alone)
  // multiplied pairwise, McCormick's envelope of the product (interval·blockedUntil >= blockedUntil from interval >= 1
  // and blockedUntil >= 0), each pair once, at most 300.
  if (!split && monomials && rows.length > 40) {
    const alone = new Map<string, number[]>()
    rows.forEach((r, i) => { const ks = Object.keys(r.lin).filter(key => key !== '1'); if (ks.length === 1 && !isMonomial(ks[0]!)) alone.set(ks[0]!, [...(alone.get(ks[0]!) ?? []), i]) })
    const seenP = new Set<string>(), pairs: [number, number][] = []
    for (const m of new Set(rows.flatMap(r => Object.keys(r.lin).filter(isMonomial)))) {
      const fs = factorsOf(m)
      if (fs.length !== 2) continue
      for (const i of alone.get(fs[0]!) ?? []) for (const j of alone.get(fs[1]!) ?? []) { const key2 = i < j ? `${i},${j}` : `${j},${i}`; if (!seenP.has(key2) && pairs.length < 300) { seenP.add(key2); pairs.push(i < j ? [i, j] : [j, i]) } }
    }
    if (pairs.length) {
      const mc = solve(withProducts(rows, pairs))
      if (mc.kind === 'refuted') return {tree: leafOf(mc.steps, pairs), nodes: budget.nodes}
    }
  }
  if (!split && monomials && rows.length <= 40) {
    // Only rows about the factors (no other map cells), each pair once: elimination over hundreds of products blows up.
    const factorSet = new Set(rows.flatMap(r => Object.keys(r.lin).filter(isMonomial).flatMap(factorsOf)))
    const relevant = rows.flatMap((r, i) => (Object.keys(r.lin).every(key => key === '1' || factorsOf(key).every(f => factorSet.has(f))) ? [i] : []))
    const pairs: [number, number][] = []
    for (const [a, i] of relevant.entries()) for (const j of relevant.slice(a)) pairs.push([i, j])
    pairs.splice(300)
    const product = solve(withProducts(rows, pairs))
    if (product.kind === 'refuted') return {tree: leafOf(product.steps, pairs), nodes: budget.nodes}
    // Degree three: each row times each product of two variables (x·y >= 0 is the pair of -x <= 0 and -y <= 0).
    const degree = Math.max(...rows.flatMap(r => Object.keys(r.lin).map(key => (key === '1' ? 0 : factorsOf(key).length))))
    if (degree >= 3) {
      const signs = rows.flatMap((r, i) => { const key = Object.keys(r.lin)[0]!; return Object.keys(r.lin).length === 1 && Object.values(r.lin)[0]! < 0 && !isMonomial(key) && (!isCell(key) || factorSet.has(key)) ? [i] : [] })
      const sq: [number, number][] = signs.flatMap((i, a) => signs.slice(a).map(j => [i, j] as [number, number])), cubes: [number, number][] = []
      for (let s = 0; s < sq.length; s++) for (let i = 0; i < rows.length; i++) cubes.push([rows.length + s, i])
      const third = solve(withProducts(rows, [...sq, ...cubes, ...pairs]))
      if (third.kind === 'refuted') return {tree: leafOf(third.steps, [...sq, ...cubes, ...pairs]), nodes: budget.nodes}
    }
    // Sums of squares: each product the hypotheses multiply, x·y, gives (x − y)² >= 0, its factors as the path reads them
    // (4·a'·b' <= (a' + b')² after a step that moves one from b to a is (a − b + 2)²); and each monomial written as u·w,
    // u and w of half its degree (one factor set aside when the degree is odd), gives (u − w)² >= 0. With the pairs above,
    // one solve finds a certificate of degree two in those forms (Cauchy–Schwarz's (ad − bc)²); past degree two, each
    // square times each factor's sign too (a³ + b³ + c³ − 3abc is a sum of a·(b − c)² and the like).
    const squares = [...new Map([...productForms(goal, path), ...squareForms(rows)].map(t => [canon(t), t])).values()].slice(0, 64)
    if (squares.length) {
      // The squares alone first (a small system), then with the pairs.
      const alone = solve(withProducts(rows, [], squares))
      if (alone.kind === 'refuted') return {tree: leafOf(alone.steps, [], squares), nodes: budget.nodes}
      const sos = solve(withProducts(rows, pairs, squares))
      if (sos.kind === 'refuted') return {tree: leafOf(sos.steps, pairs, squares), nodes: budget.nodes}
      if (degree >= 3) {
        const signs = rows.flatMap((r, i) => { const key = Object.keys(r.lin)[0]!; return Object.keys(r.lin).length === 1 && Object.values(r.lin)[0]! < 0 && factorSet.has(key) ? [i] : [] })
        const weighted: [number, number][] = [...pairs, ...signs.flatMap(i => squares.map((_, s) => [i, rows.length + s] as [number, number]))].slice(0, 600)
        const third = solve(withProducts(rows, weighted, squares))
        if (third.kind === 'refuted') return {tree: leafOf(third.steps, weighted, squares), nodes: budget.nodes}
      }
    }
    // A multiplier: every row times a factor the path has at least 1 (the row 1 − x <= 0), with the squares (x·a − b)
    // and (x·b − a) of each product a·b the rows read: a certificate that multiplies the goal by x first ((Σv)² <= n·Σv²
    // over running samples is n times the goal, closed by (n·v − s)²).
    const ones = rows.flatMap((r, i) => { const ks = Object.keys(r.lin); return ks.length === 2 && r.lin['1'] === 1 && ks.some(key => key !== '1' && r.lin[key] === -1 && factorSet.has(key)) ? [i] : [] })
    for (const xi of ones.slice(0, 3)) {
      const x = Object.keys(rows[xi]!.lin).find(key => key !== '1')!, name = (fs: string[]) => [...fs].sort().join('*')
      const forms = new Map<string, Lin>()
      for (const m of new Set(rows.flatMap(r => Object.keys(r.lin).filter(isMonomial)))) {
        const [a, b, ...more] = factorsOf(m)
        if (!a || !b || more.length) continue
        for (const [u, w] of [[a, b], [b, a]] as const) { const t: Lin = {[name([x, u])]: 1, [w]: -1}; forms.set(canon(t), t) }
      }
      const times: [number, number][] = relevant.map(i => [i, xi]), sq = [...forms.values()].slice(0, 32)
      const multiplied = solve(withProducts(rows, times, sq))
      if (multiplied.kind === 'refuted') return {tree: leafOf(multiplied.steps, times, sq), nodes: budget.nodes}
    }
    const factors = [...new Set(rows.flatMap(r => Object.keys(r.lin).filter(isMonomial).flatMap(factorsOf)))]
    const fresh = (lin: Lin) => !path.has(canon(lin)) && !path.has(canonFlip(lin))
    // Split a factor at zero, else two factors against each other (so (x - y)² >= 0 becomes a product of rows).
    const zero = factors.find(f => fresh({[f]: 1}))
    const apart = factors.flatMap((f, i) => factors.slice(i + 1).map(g => ({[f]: 1, [g]: -1}) as Lin)).find(fresh)
    if (zero) split = {[zero]: 1}
    else if (apart) split = apart
  }
  if (!split) return {stuck: verdict.kind === 'sat' ? 'sat' : 'unknown', ...(verdict.kind === 'sat' ? {witness: verdict.witness} : {}), path}
  const id = canon(split)
  const yes = growPlain(goal, new Map(path).set(id, {lin: split, holds: true}), budget)
  if (!('tree' in yes)) return yes
  // A refutation of the yes side that never reads the split refutes the case as it stands: the other side is skipped.
  const lifted = lift(goal, yes.tree, new Map(path).set(id, {lin: split, holds: true}), path)
  if (lifted) return {tree: lifted, nodes: budget.nodes}
  const no = growPlain(goal, new Map(path).set(id, {lin: split, holds: false}), budget)
  if (!('tree' in no)) return no
  return {tree: {split, yes: yes.tree, no: no.tree}, nodes: budget.nodes}
}

// A leaf's squares and products without those its derivation never reads (directly, or through a product that does),
// the rest renumbered: the same derivation over the same rows, so a smaller certificate (and a smaller Lean term).
function trimmed(n0: number, steps: Step[], pairs: [number, number][], squares: Lin[]): {steps: Step[], products: [number, number][], squares: Lin[]} {
  const used = new Set(steps.flatMap(st => (st.kind === 'input' && st.index >= n0 ? [st.index] : [])))
  for (let j = pairs.length - 1; j >= 0; j--) if (used.has(n0 + squares.length + j)) for (const i of pairs[j]!) if (i >= n0) used.add(i)
  const keepS = squares.flatMap((_, s) => (used.has(n0 + s) ? [s] : [])), keepP = pairs.flatMap((_, j) => (used.has(n0 + squares.length + j) ? [j] : []))
  const to = new Map<number, number>()
  keepS.forEach((s, r) => to.set(n0 + s, n0 + r))
  keepP.forEach((j, r) => to.set(n0 + squares.length + j, n0 + keepS.length + r))
  const re = (i: number) => (i < n0 ? i : to.get(i)!)
  return {
    steps: steps.map(st => (st.kind === 'input' ? {...st, index: re(st.index)} : st)),
    products: keepP.map(j => [re(pairs[j]![0]), re(pairs[j]![1])] as [number, number]),
    squares: keepS.map(s => squares[s]!),
  }
}

// The difference of each product's two factors in the goal's hypotheses, as the path reads them (a factor with an open
// choice in it is left out: a product of one isn't a monomial).
const productMemo = new WeakMap<Goal, E[]>()
function productForms(goal: Goal, path: Path): Lin[] {
  let prods = productMemo.get(goal)
  if (!prods) {
    const found: E[] = [], seen = new WeakSet<object>()
    const walk = (t: E | C): void => {
      if (seen.has(t)) return
      seen.add(t)
      if (t.op === 'prod') found.push(t)
      for (const val of Object.values(t)) if (Array.isArray(val)) val.forEach(x => walk(x as E | C)); else if (typeof val === 'object' && val !== null) walk(val as E | C)
    }
    goal.hyps.forEach(walk)
    productMemo.set(goal, (prods = found))
  }
  const out: Lin[] = []
  for (const e of prods) {
    if (e.op !== 'prod') continue
    const a = linear(e.a, path), b = linear(e.b, path)
    if (!a || !b) continue
    const t = sub(a, b)
    if (Object.keys(t).some(key => key.includes('⟦')) || Object.entries(t).every(([key, c]) => key === '1' || c === 0)) continue
    out.push(Object.fromEntries(Object.entries(t).filter(([, c]) => c !== 0)))
  }
  return out
}

// The forms whose squares a leaf may try: for each monomial, (u − w) for every way to split its factors (all of them,
// or all but one when there is an odd number) into two halves u and w that differ (u = w is a square already, a
// natural monomial). At most 64, from the smallest monomials up.
function squareForms(rows: {lin: Lin}[]): Lin[] {
  const monos = [...new Set(rows.flatMap(r => Object.keys(r.lin).filter(isMonomial)))].sort((a, b) => factorsOf(a).length - factorsOf(b).length)
  const out = new Map<string, Lin>()
  const name = (fs: string[]) => [...fs].sort().join('*')
  const halves = (fs: string[]) => {
    const pick = (from: number, chosen: number[]): void => {
      if (chosen.length === fs.length / 2) {
        const u = name(chosen.map(i => fs[i]!)), w = name(fs.filter((_, i) => !chosen.includes(i)))
        if (u < w) { const t: Lin = {[u]: 1, [w]: -1}; out.set(canon(t), t) }
        return
      }
      for (let i = from; i < fs.length; i++) pick(i + 1, [...chosen, i])
    }
    pick(0, [])
  }
  for (const m of monos) {
    const fs = factorsOf(m)
    if (fs.length > 6) continue
    if (fs.length % 2 === 0) halves(fs)
    else for (let i = 0; i < fs.length; i++) halves(fs.filter((_, j) => j !== i))
    if (out.size >= 64) break
  }
  return [...out.values()].slice(0, 64)
}

// A tree found under one more decision (`from`, the path with it) as a tree under the path without it (`to`), if no
// leaf reads the decision: each leaf's rows found again among the rows the shorter path gives (the same rows, renumbered:
// the decision's own row, and any row only it makes, are not there), every split kept. The derivations are the same
// arithmetic over the same rows, and the kernel checks the whole tree in the end. Undefined at the first leaf that
// needs the decision.
// A leaf's rows, by its path's decisions in order (what they are a function of): a lift reads every leaf of a subtree
// at its own path, found when it was grown, and at the path without the split, which the next lift up reads again.
const rowsSeen = new WeakMap<Goal, Map<string, ReturnType<typeof leafConstraintsReusing>>>()
export function rowsAt(goal: Goal, path: Path): ReturnType<typeof leafConstraintsReusing> {
  let byPath = rowsSeen.get(goal)
  if (!byPath) rowsSeen.set(goal, (byPath = new Map()))
  let id = ''
  for (const [key, a] of path) id += `${a.holds ? '+' : '-'}${key}|`
  let rows = byPath.get(id)
  if (!rows) { if (byPath.size >= 4096) byPath.clear(); byPath.set(id, (rows = leafConstraintsReusing(goal, path))) }
  return rows
}
function lift(goal: Goal, tree: Tree, from: Path, to: Path): Tree | undefined {
  const own = to.size // the decision's row: the last of `from`'s path rows, below every later split's
  const reads = (t: Tree): boolean => ('leaf' in t ? t.leaf.some(st => st.kind === 'input' && st.index === own) || (t.products ?? []).some(([i, j]) => i === own || j === own) : reads(t.yes) || reads(t.no))
  if (reads(tree)) return undefined
  const go = (t: Tree, a: Path, b: Path): Tree | undefined => {
    if (!('leaf' in t)) {
      const sid = canon(t.split)
      if (b.has(sid) || b.has(canonFlip(t.split))) return undefined
      const yes = go(t.yes, new Map(a).set(sid, {lin: t.split, holds: true}), new Map(b).set(sid, {lin: t.split, holds: true}))
      const no = yes && go(t.no, new Map(a).set(sid, {lin: t.split, holds: false}), new Map(b).set(sid, {lin: t.split, holds: false}))
      return yes && no ? {split: t.split, yes, no} : undefined
    }
    const ra = rowsAt(goal, a), rb = rowsAt(goal, b), at = new Map<string, number>()
    rb.forEach((r, i) => { const key = canon(r.lin); if (!at.has(key)) at.set(key, i) })
    const map = (i: number) => (i < ra.length ? at.get(canon(ra[i]!.lin)) : undefined)
    const leaf: Step[] = []
    for (const st of t.leaf) {
      if (st.kind !== 'input') { leaf.push(st); continue }
      const j = map(st.index)
      if (j === undefined) return undefined
      leaf.push({...st, index: j})
    }
    const products: [number, number][] = []
    for (const [i, j] of t.products ?? []) { const pi = map(i), pj = map(j); if (pi === undefined || pj === undefined) return undefined; products.push([pi, pj]) }
    return {leaf, ...(t.products ? {products} : {}), ...(t.squares ? {squares: t.squares} : {})}
  }
  return go(tree, from, to)
}

import {rememberProofRows} from '../core/lemma-cuts.ts'

// A tree for a weaker goal (some hypotheses left out, some conjuncts of one left out) made a tree for the whole: at any
// path a leaf's rows are among the whole goal's (each hypothesis' facts are a hypothesis' own, the cells, terms and
// naturals they read a subset), so each input is renumbered to the same row there, a square or product past the rows
// moved by the difference. Where a dropped conjunct makes the whole hypothesis false under the path, its row 1 <= 0
// refutes the leaf alone; a leaf neither maps is grown again on the whole goal.
// `opaque`: variables the weaker goal has for terms of the whole (a step's value, read the same in two hypotheses), each
// read as the term's linear form at the whole goal's path; a split the whole's path already decides is followed, not
// made again.
export function widen(part: Goal, whole: Goal, tree: Tree, opaque: Record<string, E> = {}, pp: Path = new Map(), wp: Path = pp): Tree | undefined {
  if (pastWall()) return undefined
  const names = Object.keys(opaque)
  const rename = (lin: Lin): Lin | undefined => {
    if (!names.length) return lin
    let out: Lin = {}
    for (const [key, c] of Object.entries(lin)) {
      const e = opaque[key]
      if (e) { const l = linear(e, wp); if (!l) return undefined; out = add(out, scale(l, c)) } else if (names.some(n => key.includes(n))) return undefined
      else out = add(out, {[key]: c})
    }
    return out
  }
  if (!('leaf' in tree)) {
    const id = canon(tree.split), wl = rename(tree.split)
    if (!wl) { const o = grow(whole, wp); return 'tree' in o ? o.tree : undefined }
    const wid = canon(wl), known = Object.keys(wl).every(key => key === '1') ? (wl['1'] ?? 0) <= 0 : wp.has(wid) ? wp.get(wid)!.holds : wp.has(canonFlip(wl)) ? !wp.get(canonFlip(wl))!.holds : undefined
    if (known !== undefined) return widen(part, whole, known ? tree.yes : tree.no, opaque, new Map(pp).set(id, {lin: tree.split, holds: known}), wp)
    const yes = widen(part, whole, tree.yes, opaque, new Map(pp).set(id, {lin: tree.split, holds: true}), new Map(wp).set(wid, {lin: wl, holds: true}))
    const no = yes && widen(part, whole, tree.no, opaque, new Map(pp).set(id, {lin: tree.split, holds: false}), new Map(wp).set(wid, {lin: wl, holds: false}))
    return yes && no ? {split: wl, yes, no} : undefined
  }
  const rp = rowsAt(part, pp)
  if (pastWall()) return undefined
  const rw = rowsAt(whole, wp), at = new Map<string, number>()
  const remember = (out: Tree): Tree => { rememberProofRows(out, whole, wp, rw); return out }
  rw.forEach((r, i) => { const key = canon(r.lin); if (!at.has(key)) at.set(key, i) })
  const map = (i: number) => { if (i >= rp.length) return i - rp.length + rw.length; const l = rename(rp[i]!.lin); return l && at.get(canon(l)) }
  const leaf: Step[] = [], products: [number, number][] = [], squares = (tree.squares ?? []).map(rename)
  let ok = squares.every(Boolean)
  for (const st of ok ? tree.leaf : []) { if (st.kind !== 'input') { leaf.push(st); continue } const j = map(st.index); if (j === undefined) { ok = false; break } leaf.push({...st, index: j}) }
  for (const [i, j] of ok ? tree.products ?? [] : []) { const pi = map(i), pj = map(j); if (pi === undefined || pj === undefined) { ok = false; break } products.push([pi, pj]) }
  // (renamed, a derivation through products or cuts is replayed: a cut's divisor may not divide the terms' coefficients)
  if (ok && names.length && !checkRefutation(withProducts(rw, products, squares as Lin[]), leaf)) ok = false
  if (ok) return remember({leaf, ...(tree.products ? {products} : {}), ...(tree.squares ? {squares: squares as Lin[]} : {})})
  const absurd = rw.findIndex(r => Object.keys(r.lin).every(key => key === '1') && (r.lin['1'] ?? 0) > 0)
  if (absurd >= 0) return remember({leaf: [{kind: 'input', index: absurd}]})
  const out = grow(whole, wp)
  return 'tree' in out ? out.tree : undefined
}

// Whether each hypothesis reads only names the goal's conclusion (its last hypothesis) reads.
const nearSeen = new WeakMap<Goal, boolean[]>()
// (the names a term reads, its shared parts walked once: a witness read at each of its uses is one object)
const namesOf = (t: unknown): Set<string> => {
  const out = new Set<string>()
  walkOnce(t, o => { costs.goalNodes++; for (const [key, v] of Object.entries(o)) if ((key === 'name' || key === 'map') && typeof v === 'string') out.add(v) })
  return out
}
export function nearOf(goal: Goal): boolean[] {
  let out = nearSeen.get(goal)
  if (!out) {
    const theirs = new Set(namesOf(goal.hyps.at(-1)))
    nearSeen.set(goal, (out = goal.hyps.map(h => [...namesOf(h)].every(n => theirs.has(n)))))
  }
  return out
}
// Units first: an atom some hypothesis splits on whose value the root's rows already force (a guard `?f = 0` where
// `?f = 1` holds, `k < len` where it is given). Split at the top, its forced side refutes at once; split late, under
// every other case, it is split again in each.
// GDP_UNITS=0 leaves them in the goal's order (for comparing).
const unitFirst = env.GDP_UNITS !== '0'
let unitsNow = true
// The units growPlain splits first, where it does (kernel/cdcl.ts reads them too).
export const unitAtoms = (goal: Goal): Lin[] => (unitFirst && unitsNow ? unitsOf(goal) : [])
const unitSeen = new WeakMap<Goal, Lin[]>()
function unitsOf(goal: Goal): Lin[] {
  let out = unitSeen.get(goal)
  if (out) return out
  // Forced by the root's rows without a solver: a row the atom is (or is the negation of), or the bounds the rows give
  // single variables (x <= c, x >= c) deciding it whichever way its variables go.
  const root: Path = new Map(), rows = leafConstraints(goal, root), seen = new Set<string>(), given = new Set<string>()
  costs.unitRows += rows.length
  const lo = new Map<string, number>(), hi = new Map<string, number>()
  for (const r of rows) {
    given.add(canon(r.lin))
    const vs = Object.keys(r.lin).filter(key => key !== '1')
    if (vs.length !== 1) continue
    const x = vs[0]!, c = r.lin[x]!, k = r.lin['1'] ?? 0, bound = -k / c
    if (c > 0) hi.set(x, Math.min(hi.get(x) ?? Infinity, Math.floor(bound)))
    else lo.set(x, Math.max(lo.get(x) ?? -Infinity, Math.ceil(bound)))
  }
  const range = (lin: Lin): [number, number] => Object.entries(lin).reduce(([a, b], [x, c]) => x === '1' ? [a + c, b + c]
    : c > 0 ? [a + c * (lo.get(x) ?? -Infinity), b + c * (hi.get(x) ?? Infinity)] : [a + c * (hi.get(x) ?? Infinity), b + c * (lo.get(x) ?? -Infinity)], [0, 0])
  out = []
  for (const h of goal.hyps.slice(0, -1)) {
    const atoms: Lin[] = []
    openH(h, root, atoms)
    for (const lin of atoms) {
      const id = canon(lin)
      if (seen.has(id) || seen.has(canonFlip(lin)) || !Object.keys(lin).some(key => key !== '1')) continue
      seen.add(id)
      const [a, b] = range(lin)
      if (given.has(id) || given.has(canon(atomOf(lin, false).lin)) || b <= 0 || a >= 1) out.push(lin)
    }
  }
  unitSeen.set(goal, out)
  return out
}
// Each hypothesis' open atoms, as at an earlier path that decided the same atoms it reads (kernel.ts's reusing).
const openSeen = new WeakMap<Goal, Map<C, Seen<Lin[]>>>()
// The atoms a split may take at the path, in the order growPlain tries them (some may be decided already). The
// conclusion's own atoms first (the goal's last hypothesis is the law refuted): a case it doesn't read is often one no
// refutation needs, and splitting it first multiplies every case after it. Then the hypotheses about only the names
// the conclusion reads (an assumption about another key, a witness, can wait: a refutation seldom needs it), then the
// rest, each group in the goal's order, then pairs of cells.
export function openAt(goal: Goal, path: Path, rows: {lin: Lin}[]): Lin[] {
  const open: Lin[] = []
  const hyps = goal.hyps, last = hyps.length - 1
  let byHyp = openSeen.get(goal)
  if (!byHyp) openSeen.set(goal, (byHyp = new Map()))
  const openOf = (h: C) => { let seen = byHyp.get(h); if (!seen) byHyp.set(h, (seen = {})); return reusing(seen, path, p => { const out: Lin[] = []; openH(h, p, out); return out }) }
  // (pushed one by one: a k-step unrolling's lists outgrow a spread's argument limit)
  const put = (xs: Lin[]) => { for (const x of xs) open.push(x) }
  if (unitFirst && unitsNow) put(unitsOf(goal))
  if (last >= 0) put(openOf(hyps[last]!))
  const near = nearOf(goal)
  for (const [i, h] of hyps.entries()) if (i !== last && near[i]) put(openOf(h))
  for (const [i, h] of hyps.entries()) if (i !== last && !near[i]) put(openOf(h))
  put(openCells(rows, path))
  return open
}

// What ran out, for a goal left unknown: its size, how deep the case splits went, and the two shapes that usually cause it.
function outOfBudget(goal: Goal, limit: 'nodes' | 'time', depth: number): string {
  const steps = Number(/@(\d+) steps/.exec(goal.name)?.[1] ?? 1)
  return `the prover's ${limit === 'nodes' ? '200,000-node' : 'time'} budget ran out at ${goal.hyps.length} hypotheses, ${depth} case splits deep. ` +
    `Each case a step decides multiplies the cases to refute, so ${steps > 1 ? `a law over ${steps} steps` : 'many interacting cases'} can outgrow it: ` +
    'state the law over fewer steps (a one-step law and an invariant often give the same), or split it into laws about fewer conditions'
}

// Cuts: where each of many choices (a step's case, over a run of k steps) multiplies the cases, a fact about each
// choice's value that holds whichever way it goes is split on first: its failing side is refuted by deciding that
// choice alone, and the rest of the proof assumes it, so the tree is a chain of small refutations instead of every
// combination. For a term column t = if c then A else B the candidates are t ≤ A, t ≤ B, t ≥ A and t ≥ B, innermost
// choices first; a cut is only a split, so the kernel checks it like any other.
function withCuts(goal: Goal, path: Path, budget: {nodes: number, until?: number}): Outcome | undefined {
  const rows = leafConstraints(goal, path)
  const columns = [...new Set(rows.flatMap(r => Object.keys(r.lin)).filter(n => n.startsWith('⟦')))]
    .map(n => ({n, e: columnTerm(n)!})).filter(x => x.e.op === 'if' && !decided(x.e, path))
    .sort((a, b) => Number(a.n.slice(1, -1)) - Number(b.n.slice(1, -1))) // a term's parts get their ids before it: innermost first
  const chain: {split: Lin, no: Tree}[] = []
  let at: Path = new Map(path)
  for (const {n, e} of columns) {
    if (late(budget.until ?? Infinity)) return undefined
    if (e.op !== 'if') continue
    const a = linear(e.then, at), b = linear(e.else, at), focus = topAtoms(e.c, at)
    if (!a || !b || !focus.length) continue
    for (const lemma of [sub(v(n), a), sub(v(n), b), sub(a, v(n)), sub(b, v(n))]) {
      const id = canon(lemma)
      if (at.has(id) || Object.keys(lemma).every(key => key === '1')) continue
      const no = growFocused(goal, new Map(at).set(id, {lin: lemma, holds: false}), focus, {nodes: 0, until: budget.until})
      if ('tree' in no) { chain.push({split: lemma, no: no.tree}); at = new Map(at).set(id, {lin: lemma, holds: true}) }
    }
  }
  if (!chain.length) return undefined
  const rest = growPlain(goal, at, budget)
  if (!('tree' in rest)) return rest
  return {tree: chain.reduceRight<Tree>((acc, c) => ({split: c.split, yes: acc, no: c.no}), rest.tree), nodes: budget.nodes}
}
// A condition's own comparisons, each a split atom, read with term columns for whatever choices are inside it.
function topAtoms(c: C, path: Path): Lin[] {
  if (c.op === 'not') return topAtoms(c.x, path)
  if (c.op === 'and' || c.op === 'or') return c.xs.flatMap(y => topAtoms(y, path))
  if (c.op === 'flag' || c.op === 'all') return []
  const a = linear(c.a, path), b = linear(c.b, path)
  if (!a || !b) return []
  const atoms = c.op === '<=' ? [sub(a, b)] : c.op === '<' ? [add(sub(a, b), k(1))] : [sub(a, b), sub(b, a)]
  return atoms.filter(l => Object.keys(l).some(key => key !== '1') && !path.has(canon(l)) && !path.has(canonFlip(l)))
}
// A refutation that splits only on these atoms (a cut's failing side), within a small budget and the goal's end (past
// it the goal is left unknown whatever the cuts find: the search after them stops at its first node).
function growFocused(goal: Goal, path: Path, focus: Lin[], budget: {nodes: number, until?: number}, near: Lin[] = focus): Outcome {
  if (++budget.nodes > 64 || late(budget.until ?? Infinity)) return {stuck: 'unknown', path}
  // (each node reads its whole leaf, counted as growPlain counts a node's rows)
  const leaf = leafConstraints(goal, path)
  work.n += 1 + leaf.length; costs.plainRows += leaf.length
  const verdict = solveNear(leaf, [...near, ...[...path.values()].slice(-1).map(a => a.lin)])
  if (verdict.kind === 'refuted') return {tree: {leaf: verdict.steps}, nodes: budget.nodes}
  const split = focus.find(l => !path.has(canon(l)) && !path.has(canonFlip(l)))
  if (!split) return {stuck: verdict.kind === 'sat' ? 'sat' : 'unknown', path}
  const id = canon(split)
  const yes = growFocused(goal, new Map(path).set(id, {lin: split, holds: true}), focus, budget, near)
  if (!('tree' in yes)) return yes
  const no = growFocused(goal, new Map(path).set(id, {lin: split, holds: false}), focus, budget, near)
  if (!('tree' in no)) return no
  return {tree: {split, yes: yes.tree, no: no.tree}, nodes: budget.nodes}
}

// A refutation from the rows near some facts (the rows reachable from their variables in two hops, each row joining the
// variables it reads), its inputs renumbered to the whole leaf's. A cut about one step of a long run needs that step's
// rows, not the run's; a cut it misses is only a cut not made (the plain search still follows). A variable most rows
// read (a param every step reads) joins no rows: through it every step is near every other.
function solveNear(rows: {lin: Lin, label: string}[], seeds: Lin[]): ReturnType<typeof solve> {
  const uses = new Map<string, number>()
  for (const r of rows) for (const key in r.lin) if (key !== '1') uses.set(key, (uses.get(key) ?? 0) + 1)
  const hub = (key: string) => (uses.get(key) ?? 0) > Math.max(16, rows.length / 8)
  const reach = new Set(seeds.flatMap(l => Object.keys(l).filter(key => key !== '1')))
  for (let hop = 0; hop < 2; hop++) {
    // One hop: the rows reading what was reached before it (not what this hop adds, or one pass runs along the run).
    const from = new Set(reach)
    for (const r of rows) { const keys = Object.keys(r.lin).filter(key => key !== '1'); if (keys.some(key => from.has(key) && !hub(key))) keys.forEach(key => reach.add(key)) }
  }
  const picked = rows.flatMap((r, i) => (Object.keys(r.lin).every(key => key === '1' || reach.has(key)) ? [i] : []))
  const near = solve(picked.map(i => rows[i]!))
  return near.kind === 'refuted' ? {kind: 'refuted', steps: near.steps.map(st => (st.kind === 'input' ? {...st, index: picked[st.index]!} : st))} : near
}

// Integer completeness for bounded systems: when elimination is inexact and finds no witness, halve a variable's range
// (x <= mid or x >= mid + 1). Each half is a split like any other, so the kernel checks it the same way; a variable
// pinned to one value becomes an equality, which the solver substitutes exactly.
function bisect(rows: {lin: Lin, label: string}[], path: Path): Lin | undefined {
  const refutes = (extra: Lin) => solve([...rows, {lin: extra, label: ''}]).kind === 'refuted'
  const names = [...new Set(rows.flatMap(r => Object.keys(r.lin).filter(key => key !== '1')))]
  for (const x of names) {
    let hi = 1
    while (hi < 1 << 20 && !refutes({1: hi + 1, [x]: -1})) hi *= 2 // x >= hi + 1 is impossible
    if (hi >= 1 << 20) continue
    // The least lo with x <= lo possible, by halving (x <= c is impossible exactly for the c below it).
    let lo = 0, top = hi
    while (lo < top) { const c = Math.floor((lo + top) / 2); if (refutes({[x]: 1, 1: -c})) lo = c + 1; else top = c }
    const mid = Math.floor((lo + hi) / 2)
    for (const c of lo === hi ? [lo, lo - 1] : [mid]) {
      const lin: Lin = c === 0 ? {[x]: 1} : {[x]: 1, 1: -c}
      if (!path.has(canon(lin)) && !path.has(canonFlip(lin))) return lin
    }
  }
  return undefined
}

// Branch and bound for unbounded systems: split on a variable the rational solution puts between two integers.
function fractional(point: Record<string, number> | undefined, path: Path): Lin | undefined {
  for (const [x, value] of Object.entries(point ?? {})) {
    if (Math.abs(value - Math.round(value)) < 1e-9 || isMonomial(x)) continue
    const c = Math.floor(value), lin: Lin = c === 0 ? {[x]: 1} : {[x]: 1, 1: -c}
    if (!path.has(canon(lin)) && !path.has(canonFlip(lin))) return lin
  }
  return undefined
}

// The keys a proof assumes the every-key laws at: every key the step and the laws read, and the fresh key of the goal.
// Each map read of a term (inE) or a condition (inC) given to f, outermost first, a quantified flag's body included.
const eachRead = (f: (e: Extract<E, {op: 'get'}>) => void) => {
  const inE = (e: E): void => { if (e.op === 'get') { f(e); inE(e.key) } else if (e.op === 'if') (inC(e.c), inE(e.then), inE(e.else)); else if (e.op === 'mul' || e.op === 'proj') inE(e.a); else if ('b' in e) (inE(e.a), inE(e.b)) }
  const inC = (c: C): void => (c.op === 'flag' ? undefined : c.op === 'all' ? inC(c.c) : c.op === 'not' ? inC(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.forEach(inC) : (inE(c.a), inE(c.b)))
  return {inE, inC}
}
// A key bound by a quantified flag or a write at every key isn't one: those reads are at every key already.
function readKeys(m: Machine, laws: Law[]): E[] {
  const out = new Map<string, E>()
  const bound = new Set<string>([...Object.values(m.step.flags ?? {}).flatMap(c => (c.op === 'all' ? boundOf(c) : [])), ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [w.each] : []))])
  const free = (e: E) => !JSON.stringify(e).match(/"name":"([^"]+)"/g)?.some(n => bound.has(n.slice(8, -1)))
  // (a tuple key's parts are the keys: a law about every tuple of keys is assumed at them)
  const put = (key: E) => { for (const p of tupleParts(key)) if (free(p)) out.set(JSON.stringify(p), p) }
  const {inE, inC} = eachRead(e => put(e.key))
  Object.values(m.step.state ?? {}).forEach(inE)
  Object.values(m.step.flags ?? {}).forEach(inC)
  for (const w of Object.values(m.step.maps ?? {})) { if (!('each' in w)) { for (const p of tupleParts(w.key)) out.set(JSON.stringify(p), p); inE(w.key) } inE(w.value) }
  for (const l of laws.filter(l => !l.forall)) inC(l.holds)
  return keysInlined(m, [...out.values()])
}
// Keys as the kernel's goals read them: a key that reads a flag (a map read at `when(flag, a, b)` in the step) with the
// flag's condition in its place (kernel.ts's updateOf inlines them so), since an instance is a term over the frame and
// names no flag. A quantified flag reads as its 0/1 variable ?f, as the goals read it.
function keysInlined(m: Machine, keys: E[]): E[] {
  if (!keys.some(e => JSON.stringify(e).includes('"op":"flag"'))) return keys
  const flags: Record<string, C> = {}
  for (const [f, c] of Object.entries(m.step.flags ?? {})) flags[f] = c.op === 'all' ? {op: '=', a: {op: 'var', name: `?${f}`}, b: {op: 'const', value: 1}} : substC(c, {vars: {}, maps: {}, flags})
  return [...new Map(keys.map(e => substE(e, {vars: {}, maps: {}, flags})).map(e => [JSON.stringify(e), e])).values()]
}
const shifts = (m: Machine) => Object.values(m.step.maps ?? {}).some(w => 'each' in w && !plainKey(w.value, w.each))
// The keys some goals read a map at, and at each map, in one walk.
function mapReads(goals: Goal[]): {keys: E[], byMap: Map<string, E[]>} {
  const all = new Map<string, E>(), out = new Map<string, Map<string, E>>()
  // (a tuple key: its parts are the keys, each part read back from a tuple as the part; the map's key the tuple of them)
  const {inC} = eachRead(e0 => {
    const key = e0.key.op === 'tup' || e0.key.op === 'proj' ? projected(e0.key) : e0.key, id = JSON.stringify(key)
    for (const p of tupleParts(key)) all.set(JSON.stringify(p), p)
    if (!out.has(e0.map)) out.set(e0.map, new Map()); out.get(e0.map)!.set(id, key)
  })
  for (const g of goals) g.hyps.forEach(inC)
  return {keys: [...all.values()], byMap: new Map([...out].map(([mp, ks]) => [mp, [...ks.values()]]))}
}
// A cell's key as the kernel names it (kernel.ts keyOf): `name:coef` parts joined by ',', '1' the constant; its value
// where the names have these (a name left out is 0, as a model leaves it).
export const keyValue = (cell: string, w: Record<string, number>): number | undefined => {
  const inner = cell.slice(cell.indexOf('[') + 1, -1)
  // (a tuple's parts each valued so, the key their pairing)
  if (inner.startsWith('⟨')) {
    const parts = cellParts(cell).keys!.map(k => keyValue(`_[${canon(k)}]`, w))
    if (parts.some(x => x === undefined)) return undefined
    try { return parts.slice(0, -1).reduceRight((b: number, a) => cpair(a!, b), parts.at(-1)!) } catch { return undefined }
  }
  // (its parts split at the commas outside brackets: a part may be a cell itself, Pending[idn[n:1]:64,n:1], valued as the
  // model values it)
  const parts: string[] = []
  let depth = 0, from = 0
  for (let i = 0; i < inner.length; i++) { const ch = inner[i]; if (ch === '[') depth++; else if (ch === ']') depth--; else if (ch === ',' && depth === 0) { parts.push(inner.slice(from, i)); from = i + 1 } }
  parts.push(inner.slice(from))
  let value = 0
  for (const part of parts.filter(Boolean)) {
    const at = part.lastIndexOf(':'), name = part.slice(0, at), coef = Number(part.slice(at + 1))
    if (name === '1') value += coef
    else if (name in w) value += coef * w[name]!
    else if (name.includes('[')) return undefined
  }
  return value
}
// Instances a model asks for (model-based instantiation, as SMT solvers' MBQI and Ivy's EPR checks read a model): a
// model of a goal whose laws about keys (and quantified flags) were assumed at some tuples only can break one at a tuple
// of the goal's own keys it was never assumed at. That model is no counterexample: on the goal's keys (all the keys an
// EPR-like goal has), the laws hold everywhere in a real one. Here: the model read as a state (its cells at the values
// of their keys, a function read as a map), each law and each quantified flag the model sets evaluated at every tuple of
// the values the goal's keys take, and each tuple where one fails added, as the goal's terms with those values, to its
// instances. None found: the model is one on every tuple of the goal's keys. Untrusted: it chooses instances only.
export const modelRounds = 4
// A condition as the disjuncts it is the or of (¬(a ∧ b) as ¬a, ¬b).
// (GDP_MODEL_CUTS=0: every tuple evaluated whole, for comparing)
const modelCuts = env.GDP_MODEL_CUTS !== '0'
const disjuncts = (c: C): C[] => (c.op === 'or' ? c.xs.flatMap(disjuncts) : c.op === 'not' && c.x.op === 'and' ? c.x.xs.flatMap(y => disjuncts({op: 'not', x: y})) : c.op === 'not' && c.x.op === 'not' ? disjuncts(c.x.x) : [c])
export function modelInstances(m: Machine, laws: Law[], inst: Instances, goal: Goal, w: Record<string, number>, most = 64, sorted = false): Instances | undefined {
  const pm = plainOf(m), qs = Object.entries(pm.step.flags ?? {}).filter((e): e is [string, Extract<C, {op: 'all'}>] => e[1].op === 'all' && w[`?${e[0]}`] === 1)
  const keyed = laws.filter(l => l.forall)
  if (!keyed.length && !qs.length) return undefined
  // (the maps a request carries read as maps too: a quantified flag over one, wo's ∀k. Q has k → Votes[src, k])
  const fns = Object.keys(pm.fns ?? {}), mm: Machine = {...pm, fns: undefined, maps: {...(pm.maps ?? {}), ...Object.fromEntries([...fns, ...(pm.inputMaps ?? []), ...Object.keys(pm.counts ?? {})].map(f => [f, 0]))}}
  const maps: Record<string, Map<number, number>> = Object.fromEntries(Object.keys(mm.maps!).map(mp => [mp, new Map<number, number>()]))
  for (const [cell, value] of Object.entries(w)) {
    const br = cell.indexOf('[')
    if (br < 0 || !cell.endsWith(']') || !maps[cell.slice(0, br)]) continue
    const key = keyValue(cell, w)
    if (key !== undefined) maps[cell.slice(0, br)]!.set(key, value)
  }
  const st = {scalars: {}, maps}, read = (at: Record<string, number>) => new Proxy(at, {get: (t, p: string) => (p in t ? t[p] : w[p] ?? 0), has: (t, p: string) => p in t || p in w}) as Record<string, number>
  // (a count's cell the model has not: its definition, its body summed over the model's cells below its bound, so a law
  // reading it is read as the model's state reads it, not at 0)
  for (const [c, d] of Object.entries(pm.counts ?? {})) {
    const had = maps[c]!, sum = (x: number): number => {
      const e1 = read(d.base ? {[d.j]: Math.floor(x / d.base), [d.lo!]: x % d.base} : {[d.j]: x}), n = Math.min(256, evalE(d.below, e1, st, mm))
      let t = 0
      for (let k = 0; k < n; k++) t += evalE(d.body, read({...e1, [d.key]: k}), st, mm)
      return t
    }
    maps[c] = new (class extends Map<number, number> { override get(x: number) { if (!super.has(x)) super.set(x, 0), super.set(x, sum(x)); return super.get(x) } })(had)
  }
  const ev = (f: () => boolean): boolean | undefined => { try { return f() } catch { return undefined } }
  const valueOf = (e: E): number | undefined => { try { return evalE(e, read({}), st, mm) } catch { return undefined } }
  // Each bound key over its own sort as the model fills it: the terms its body's map reads bind matched against the
  // goal's keys (M[x·N + y] against M[a·N + b] binds x to a), one term a value; a key no read binds (or only a
  // function's), every key of the goal.
  const {keys, byMap} = mapReads([goal]), all = new Map<number, E>()
  // (a law's key read at a tuple's place is matched against that map's tuples: its sort is the place's)
  const tupled = [...byMap.values()].some(ks => ks.some(k => k.op === 'tup'))
  for (const e of keys) { const v2 = valueOf(e); if (v2 !== undefined && !all.has(v2)) all.set(v2, e) }
  if (!all.size) return undefined
  // (each sort's witnesses first: an ∃ law's ghost, a quantified flag's witness, the terms a model most often breaks a
  // law at and no read's matching orders well)
  const witnessFirst = (p: Map<number, E>): Map<number, E> => {
    const isW = (e: E) => /"name":"(some\$|w\?)/.test(JSON.stringify(e))
    return new Map([...[...p].filter(([, e]) => isW(e)), ...[...p].filter(([, e]) => !isW(e))])
  }
  // (`atoms`: each sort over the goal's own names alone, its skolems, the request's inputs, witnesses and ghosts, the
  // elements an EPR model names: a composed term in a part's place is an instance at a key of the wrong sort)
  // (a key no read binds is a value, an epoch say, over the naturals: 0, their least, is one of its terms too, as Ivy's
  // ordered sorts have their zero; a law before the start, nothing above 0, is assumed there)
  const zero: E = {op: 'const', value: 0}
  const accepts = instanceSortGuard(m, laws)
  const sortsOf = (body: C, names: string[], atoms: boolean): Map<number, E>[] => sortTerms(body, names, fns, mp => (tupled ? [...keys, ...(byMap.get(mp) ?? [])] : keys)).map(ts => {
    const p = new Map<number, E>()
    for (const e of ts ?? []) { const v2 = valueOf(e); if (v2 !== undefined && !p.has(v2) && (!atoms || e.op === 'var')) p.set(v2, e) }
    const fallback = new Map([...all].filter(([, e]) => !atoms || e.op === 'var'))
    const q = p.size ? p : fallback, r = witnessFirst(q)
    return ts || r.has(0) ? r : r.set(0, zero)
  })
  const out: Instances = {...inst}
  // (the 20,000 evaluations shared: each law and flag at most an even share of what is left, so the laws about five keys
  // first don't leave none to those after: sharded KV's "a key in transfer has no owner", broken at the goal's own keys)
  let added = 0, evals = 0, left = 0, ineligible = false
  const each = (id: string, names: string[], body: C, atoms: boolean) => {
    if (pastWall()) return
    const until = evals + Math.max(256, Math.floor((20_000 - evals) / Math.max(1, left--)))
    const have = new Set<string>(), had = out[id] ?? [], n = names.length, sorts = sortsOf(body, names, atoms)
    // (a law at one key assumed at a term of every value its sort takes already: nothing to add)
    if (n === 1) { const covered = new Set(had.map(valueOf)); if ([...sorts[0]!.keys()].every(v2 => covered.has(v2))) return }
    for (let t = 0; t + n <= had.length; t += n) have.add(JSON.stringify(had.slice(t, t + n)))
    // (the body's disjuncts, each checked as soon as the keys it reads are bound: one that holds there holds the body at
    // every tuple below, so transitivity's T(t, x, y) false cuts its z; a law about four keys over ten values each, 10,000
    // tuples, took the whole share before, its broken tuples never reached)
    const ready: C[][] = Array.from({length: n + 1}, () => [])
    if (modelCuts) for (const d of disjuncts(body)) { const t = JSON.stringify(d); ready[names.reduce((a, x, j) => (t.includes(`"name":${JSON.stringify(x)}`) ? j + 1 : a), 0)]!.push(d) }
    const go = (i: number, at: Record<string, number>, terms: E[]): void => {
      if (added >= most || evals > until || (evals % 512 === 0 && pastWall())) return
      for (const d of ready[i]!) { evals++; if (ev(() => evalC(d, read(at), st, mm)) === true) return }
      if (i === n) {
        evals++
        if (ev(() => evalC(body, read(at), st, mm)) !== false) return
        const id2 = JSON.stringify(terms)
        if (have.has(id2)) return
        // Sort-aware consumers must not count tuples they would discard after this pass.
        if (sorted && terms.some((e,j) => !accepts(id,j,e))) { ineligible = true; return }
        have.add(id2); out[id] = [...(out[id] ?? []), ...terms]; added++
        return
      }
      for (const [v2, e] of sorts[i]!) go(i + 1, {...at, [names[i]!]: v2}, [...terms, e])
    }
    go(0, {}, [])
    if (modelsTrace) console.error(`[models]   ${atoms ? 'atoms' : 'all'} ${id.slice(0, 30)}: sorts ${sorts.map(x => x.size).join('x')}, evals ${evals} of ${until}, added ${added}`)
  }
  // the goal's own names first; every key it reads where they show nothing
  for (const atoms of [true, false]) {
    if (atoms === false && added) break
    evals = 0; left = keyed.length + qs.length
    for (const l of keyed) each(l.name, [l.forall!, ...(l.keys ?? [])], l.holds, atoms)
    for (const [f, q] of qs) each(`?${f}`, boundOf(q), q.c, atoms)
  }
  // A rejected-only refinement is not evidence that the model satisfies every assumed law.
  return added || ineligible ? out : undefined
}
// A goal (or a law's goals) asked at some instances, and again at those its model asks for (modelInstances), up to
// modelRounds times. `ask` is the caller's own question; `modelOf` reads a model from its answer, `settled` says it is
// one (a proof, a model: not out of budget). The later rounds together get modelShare times the cost model's work the
// first took (at least a second of it), so a model's tuples that make the goal one the prover can't finish cost that,
// not the goal's usual budget again; a later round left unsettled gives back the first round's answer, so the verdict is
// never one the model's tuples made worse. Untrusted.
export const modelShare = 3
// (GDP_MODELS_TRACE=1: each model round, its goal and the tuples a model adds, on stderr)
const modelsTrace = !!env.GDP_MODELS_TRACE, modelFloor = Number(env.GDP_MODEL_FLOOR ?? 1_000)
const costNow = (): number => (rate ? clock() : fullWork() / groundRate)
const within = <T>(ms: number, f: () => T): T => (rate ? withDeadline(clock() + ms, f) : withWork(fullWork() + groundRate * ms, f))
export function withModels<T>(m: Machine, laws: Law[], inst: Instances, goalOf: (i: Instances) => Goal[], ask: (gs: Goal[]) => T,
  modelOf: (t: T) => {goal: Goal, w: Record<string, number>} | undefined, settled: (t: T) => boolean): {result: T, inst: Instances} {
  return withPatterns(m, laws, () => modelsLoop(m, laws, inst, goalOf, ask, modelOf, settled))
}
function modelsLoop<T>(m: Machine, laws: Law[], inst: Instances, goalOf: (i: Instances) => Goal[], ask: (gs: Goal[]) => T,
  modelOf: (t: T) => {goal: Goal, w: Record<string, number>} | undefined, settled: (t: T) => boolean): {result: T, inst: Instances} {
  let at = inst, first: {result: T, inst: Instances} | undefined, cap = 0
  for (let round = 0; ; round++) {
    const c0 = costNow(), result = round ? within(Math.max(0, cap), () => ask(goalOf(at))) : ask(goalOf(at))
    if (round) cap -= costNow() - c0; else cap = Math.max(modelFloor, modelShare * (costNow() - c0))
    if (round && !settled(result)) { if (modelsTrace) console.error(`[models] round ${round} unsettled in ${Math.round(costNow() - c0)} cost`); return first! }
    if (pastWall()) return first ?? {result, inst: at}
    first ??= {result, inst: at}
    const mw = modelOf(result), more = mw && round < modelRounds && cap > 0 ? modelInstances(m, laws, at, mw.goal, mw.w) : undefined
    if (modelsTrace) console.error(`[models] round ${round} ${mw ? `model at ${mw.goal.name} (${mw.goal.hyps.length} hyps)` : settled(result) ? 'settled' : 'unsettled'} ${Math.round(costNow() - c0)} cost, cap ${Math.round(cap)}; ${more ? `+${Object.entries(more).map(([n, ks]) => `${n.slice(0, 24)}:${ks.length - (at[n]?.length ?? 0)}`).filter(x => !x.endsWith(':0')).join(' ')}` : 'no more'}`)
    if (!more) return {result, inst: at}
    at = more
  }
}
// Instances with each every-key law also at these keys. A law about two keys or more goes at tuples that relate the
// goal's own keys (`focus`: the skolems of the law it proves, or a step law's keys) to each other and to the keys that
// read none of them: at the i-th place, a key that reads the i-th focus alone (the first, past the focus there is), and
// at most one place a key that reads no focus.
// (a law about several keys at most relatedMost tuples each way, and with many such laws a share of relatedBudget: wo's
// caller goal with 81 of them, 950 tuples each, held 34,881 hypotheses; the model's tuples add the rest)
const withReads = (laws: Law[], inst: Instances, keys: E[], focus: string[], byMap?: Map<string, E[]>, fns: string[] = []): Instances => {
  const most = Math.min(relatedMost, Math.max(64, Math.floor(relatedBudget / Math.max(1, laws.filter(l => l.forall && l.keys?.length).length))))
  return {...inst, ...Object.fromEntries(laws.filter(l => l.forall).map(l => {
  const had = inst[l.name] ?? []
  if (l.keys?.length) {
    const n = l.keys.length + 1, out = new Map<string, E[]>()
    for (let i = 0; i + n <= had.length; i += n) out.set(JSON.stringify(had.slice(i, i + n)), had.slice(i, i + n))
    // (a key the law's hypothesis fixes by an equation, x + c = t: the tuples of the others, x at t ∸ c in each)
    const {law: lr, back} = fixedOut(l), m2 = lr.keys?.length ?? 0, sorted = byMap ? keySorted(lr, byMap, fns) : undefined
    const tuples = m2 ? [...related(keys, focus, m2 + 1, sorted, most), ...matched(lr, keys, most)] : related(keys, focus, 1, sorted, most)
    for (const t0 of tuples) if (!sorted || sorted(t0)) { const tuple = back(t0); out.set(JSON.stringify(tuple), tuple) }
    return [l.name, [...out.values()].flat()]
  }
  const seen = new Set(had.map(e => JSON.stringify(e)))
  return [l.name, [...had, ...keys.filter(e => { const id = JSON.stringify(e); return seen.has(id) ? false : (seen.add(id), true) })]]
  }))}
}
// A law's keys that its hypothesis fixes by an equation (x + c = t, or t = x, t reading no fixed key): the law without
// them (each read at t ∸ c, c ≤ t a further hypothesis: the same law over the naturals), and `back`, a tuple of its keys
// made a tuple of the law's (each fixed key at its t). A law with five keys of which two a cell fixes (Table[a·N + k] =
// v + 1) has its instances over three. Untrusted: it chooses instances only.
const fixedMemo = new WeakMap<Law, {law: Law, back: (t: E[]) => E[]}>()
function fixedOut(l: Law): {law: Law, back: (t: E[]) => E[]} {
  let out = fixedMemo.get(l)
  if (!out) fixedMemo.set(l, (out = fixedOut0(l)))
  return out
}
function fixedOut0(l: Law): {law: Law, back: (t: E[]) => E[]} {
  const all = [l.forall!, ...(l.keys ?? [])], same = {law: l, back: (t: E[]) => t}
  const hyps = l.holds.op === 'or' ? l.holds.xs.flatMap(d => (d.op === 'not' ? (d.x.op === 'and' ? d.x.xs : [d.x]) : [])) : []
  const named = (e: E, x: string) => JSON.stringify(e).includes(`"name":${JSON.stringify(x)}`)
  const offset = (e: E): [string, number] | undefined => (e.op === 'var' && all.includes(e.name) ? [e.name, 0] : e.op === 'add' && e.a.op === 'var' && all.includes(e.a.name) && e.b.op === 'const' ? [e.a.name, e.b.value] : undefined)
  const fixed = new Map<string, {t: E, c: number}>()
  for (const h of hyps) {
    if (h.op !== '=') continue
    for (const [x, t] of [[h.a, h.b], [h.b, h.a]] as const) {
      const o = offset(x)
      if (!o || o[0] === l.forall || fixed.has(o[0]) || named(t, o[0]) || [...fixed.keys()].some(f => named(t, f)) || [...fixed.values()].some(f => named(f.t, o[0]))) continue
      fixed.set(o[0], {t, c: o[1]}); break
    }
  }
  if (!fixed.size) return same
  const at = (x: string): E => { const {t, c} = fixed.get(x)!; return c ? {op: 'sub', a: t, b: {op: 'const', value: c}} : t }
  const sub0 = {vars: Object.fromEntries([...fixed.keys()].map(x => [x, at(x)])), maps: {}, flags: {}}
  const guards: C[] = [...fixed.values()].flatMap(({t, c}) => (c ? [{op: '<=', a: {op: 'const', value: c}, b: t} as C] : []))
  const kept = all.filter(x => !fixed.has(x)), holds = substC(guards.length ? {op: 'or', xs: [{op: 'not', x: {op: 'and', xs: guards}}, l.holds]} : l.holds, sub0)
  const law: Law = {...l, holds, keys: kept.slice(1)}
  return {law, back: t => { const s2 = {vars: Object.fromEntries(kept.map((x, i) => [x, t[i]!])), maps: {}, flags: {}}; return all.map(x => (fixed.has(x) ? substE(at(x), s2) : t[kept.indexOf(x)]!)) }}
}
// A tuple of the key's sort: each of a law's keys read at a map (M[x], M[x·N + y]) takes only the terms its read matches
// against the keys the goals read that map at (the key's sort, as the goal holds it: Link[c1·N + s] against
// Link[a·N + b] gives c1 a and s b); a key no read binds, or a read no goal key matches, takes any. A function's
// argument is no sort (a function is read at any key). Untrusted: it chooses instances only.
// (per place too: `at(i, e)`, whether e is of the i-th key's sort, each key's text read once)
function keySorted(l: Law, byMap: Map<string, E[]>, fns: string[]): ((tuple: E[]) => boolean) & {at: (i: number, e: E) => boolean} {
  const allowed = sortTerms(l.holds, [l.forall!, ...(l.keys ?? [])], fns, mp => byMap.get(mp) ?? []).map(ts => ts && new Set(ts.map(t => JSON.stringify(t))))
  const text = new WeakMap<E, string>(), id = (e: E) => { let t = text.get(e); if (t === undefined) text.set(e, (t = JSON.stringify(e))); return t }
  const at = (i: number, e: E) => !allowed[i] || allowed[i]!.has(id(e))
  return Object.assign((tuple: E[]) => tuple.every((t, i) => at(i, t)), {at})
}
// The terms `body`'s reads (not a function's) bind each of `vars` to, matched against the keys `at` gives their map.
function sortTerms(body: C, vars: string[], fns: string[], at: (map: string) => E[]): (E[] | undefined)[] {
  const out: (E[] | undefined)[] = vars.map(() => undefined)
  eachRead(e => {
    if (fns.includes(e.map) || !vars.some(x => JSON.stringify(e.key).includes(`"name":${JSON.stringify(x)}`))) return
    for (const t of at(e.map)) { const b = matchMany(e.key, t, vars); if (b) vars.forEach((x, i) => { if (x in b) (out[i] ??= []).push(b[x]!) }) }
  }).inC(body)
  return out
}
// A law about several keys where its body reads a map at a key naming every one of them (Link[x·N + y]): the tuple
// that makes that key one the goals read (Link[a·N + b] gives (a, b)), as a fact about several keys is matched
// (withFacts). A key of one bound name alone matches every key, so it binds no tuple here.
// Where no one key names every bound name (a relation read at two pairs, Link[c1·N + s] and Link[c2·N + s]), two reads'
// matches together bind them, as a fact's do (withFacts): at a name both bind, each one's value in turn.
// (at most relatedMost tuples a law, from each way: where a law about many keys has more, sharded KV's five keys at
// 24,608 tuples each, 112,587 hypotheses before any search, the model's tuples, modelInstances, add those a proof misses)
export const relatedMost = 512, relatedBudget = 8_192
const matched = (l: Law, keys: E[], most = relatedMost): E[][] => {
  const vars = [l.forall!, ...(l.keys ?? [])], names = (e: E) => vars.filter(x => JSON.stringify(e).includes(`"name":${JSON.stringify(x)}`))
  const pats = new Map<string, E>()
  eachRead(e => { const ns = names(e.key); if (ns.length === vars.length || ns.length > 1) pats.set(JSON.stringify(e.key), e.key) }).inC(l.holds)
  const partial: Record<string, E>[] = []
  for (const p of pats.values()) for (const key of keys) { const b = matchMany(p, key, vars); if (b) partial.push(b) }
  const whole = (b: Record<string, E>) => vars.every(x => x in b), isWhole = partial.map(whole), out = partial.filter((_, i) => isWhole[i])
  // (two partial matches together: at most `most` of them, as related's)
  for (let i = 0; i < partial.length && out.length < most; i++) {
    if (isWhole[i]) continue
    for (let j = i + 1; j < partial.length && out.length < most; j++) {
      const a = partial[i]!, b = partial[j]!
      if (isWhole[j] || !vars.every(x => x in a || x in b)) continue
      out.push({...b, ...a}, {...a, ...b})
    }
  }
  return out.map(b => vars.map(x => b[x]!))
}
// The n-tuples of the keys that relate the focus (withReads): those `keep` keeps, the first `most` of them in this order
// (each place's own focus key before the rest).
// (`keep` at each place, `keep.at`, as the tuple is made: a sort no key of keeps no tuple, and none is made of it)
const related = (keys: E[], focus: string[], n: number, keep?: {at: (i: number, e: E) => boolean}, most = Infinity): E[][] => {
  const reads = (e: E, x?: string) => x !== undefined && JSON.stringify(e).includes(`"name":${JSON.stringify(x)}`)
  const own = (i: number) => { const f = focus[i] ?? focus[0]; return keys.filter(e => reads(e, f) && focus.every(g => g === f || !reads(e, g))) }
  const R0 = keys.filter(e => !focus.some(f => reads(e, f))), out: E[][] = []
  const owns = Array.from({length: n}, (_, i) => own(i).filter(e => !keep || keep.at(i, e))), R = Array.from({length: n}, (_, i) => R0.filter(e => !keep || keep.at(i, e)))
  let made = 0
  const go = (i: number, tuple: E[], rest: boolean): void => {
    if (out.length >= most || (++made % 4096 === 0 && pastWall())) return
    if (i === n) { out.push(tuple); return }
    for (const e of owns[i]!) go(i + 1, [...tuple, e], rest)
    if (!rest) for (const e of R[i]!) go(i + 1, [...tuple, e], true)
  }
  go(0, [], false)
  return out
}
// A law about every n keys at every n-tuple of the keys (flattened, as Instances keeps tuples).
const tuples = (keys: E[], n: number): E[] => (n === 0 ? [] : n === 1 ? keys : keys.flatMap(a => { const rest = tuples(keys, n - 1); return Array.from({length: rest.length / (n - 1)}, (_, t) => [a, ...rest.slice(t * (n - 1), (t + 1) * (n - 1))]).flat() }))
// The keys some goals read a function at.
function fnKeys(m: Machine, goals: Goal[]): E[] {
  const fns = Object.keys(m.fns ?? {}), out = new Map<string, E>(), {inC} = eachRead(e => { if (fns.includes(e.map)) out.set(JSON.stringify(e.key), e.key) })
  for (const g of goals) g.hyps.forEach(inC)
  return [...out.values()]
}
// Instances with each fact about every key assumed where it reads a function at one of these keys: its key at each
// value that makes one of its reads one of these (by matching: a function of several arguments reads a paired key), and
// at the keys themselves.
const withFacts = (m: Machine, inst: Instances, keys: E[]): Instances => ({...inst, ...Object.fromEntries((m.facts ?? []).filter(f => f.forall).map(f => {
  if (f.keys?.length) {
    // A fact about several keys reads a function of several arguments (at a paired key): each read matched against the
    // keys the goals read binds some of the fact's keys; one match, or two that agree, binding every key is an instance.
    const vars = [f.forall!, ...f.keys], reads = fnKeys(m, [{name: '', hyps: [f.holds]}])
    if (!reads.length) return [f.name, tuples(keys, vars.length)]
    const partial = reads.flatMap(pattern => keys.flatMap(key => { const b = matchMany(pattern, key, vars); return b ? [b] : [] }))
    const whole = (b: Record<string, E>) => vars.every(x => x in b)
    const agree = (a: Record<string, E>, b: Record<string, E>) => Object.entries(b).every(([x, e]) => !(x in a) || JSON.stringify(a[x]) === JSON.stringify(e))
    const found = [...partial.filter(whole), ...partial.flatMap((a, i) => partial.slice(i + 1).filter(b => agree(a, b)).map(b => ({...a, ...b})).filter(whole))]
    const had = inst[f.name] ?? [], out = [...had], seen = new Set<string>()
    for (let t = 0; t < had.length / vars.length; t++) seen.add(JSON.stringify(had.slice(t * vars.length, (t + 1) * vars.length)))
    for (const b of found) { const tuple = vars.map(x => b[x]!), id = JSON.stringify(tuple); if (!seen.has(id)) { seen.add(id); out.push(...tuple) } }
    return [f.name, out]
  }
  const had = inst[f.name] ?? [], seen = new Set(had.map(e => JSON.stringify(e)))
  const reads = fnKeys(m, [{name: '', hyps: [f.holds]}])
  const at = [...keys, ...reads.flatMap(pattern => keys.flatMap(key => { const b = match(pattern, key, f.forall!); return b ? [b] : [] }))]
  return [f.name, [...had, ...at.filter(e => { const id = JSON.stringify(e); return seen.has(id) ? false : (seen.add(id), true) })]]
}))})
// The values of the names in xs that make pattern the term, for those it reads, if some do (structurally).
function matchMany(pattern: E, term: E, xs: string[]): Record<string, E> | undefined {
  const bound: Record<string, E> = {}
  const go = (p: E | C, t: E | C): boolean => {
    if (p.op === 'var' && xs.includes(p.name)) { if (p.name in bound) return JSON.stringify(bound[p.name]) === JSON.stringify(t); bound[p.name] = t as E; return true }
    if (p.op !== t.op) return false
    const pe = Object.entries(p), te = t as Record<string, unknown>
    return pe.every(([k, val]) => k === 'op' || (typeof val === 'object' && val !== null ? (Array.isArray(val) ? Array.isArray(te[k]) && (te[k] as unknown[]).length === val.length && val.every((y, i) => go(y as E, (te[k] as E[])[i]!)) : go(val as E, te[k] as E)) : val === te[k]))
  }
  if (go(pattern, term)) return bound
  // (else as radix sums: a key written 64·(64·z + x) + w is 4096·n + 64·k + v's sort, each part bound to the part of
  // its coefficient)
  const p = radix(pattern), t = p && radix(term)
  if (!p || !t || p.length !== t.length || p.some(([, c], i) => c !== t[i]![1])) return undefined
  const out: Record<string, E> = {}
  for (const [i, [e]] of p.entries()) {
    const u = t[i]![0]
    if (e.op === 'var' && xs.includes(e.name)) { if (e.name in out && JSON.stringify(out[e.name]) !== JSON.stringify(u)) return undefined; out[e.name] = u }
    else if (JSON.stringify(e) !== JSON.stringify(u)) return undefined
  }
  return out
}
// A key as a radix sum Σ c·part, its parts by coefficient, highest first (distinct coefficients, no constant), else
// undefined. A part is a name or a read of one (a function's).
const radix = (e: E): [E, number][] | undefined => {
  const out: [E, number][] = []
  const go = (x: E, k: number): boolean => x.op === 'add' ? go(x.a, k) && go(x.b, k) : x.op === 'mul' ? go(x.a, k * x.k) : x.op === 'var' || x.op === 'get' ? (out.push([x, k]), true) : false
  if (!go(e, 1) || out.length < 2) return undefined
  out.sort((a, b) => b[1] - a[1])
  return out.every(([, c], i) => i === 0 || c !== out[i - 1]![1]) ? out : undefined
}
// The value of x that makes pattern the term, if one does (structurally).
function match(pattern: E, term: E, x: string): E | undefined {
  let bound: E | undefined
  const go = (p: E | C, t: E | C): boolean => {
    if (p.op === 'var' && p.name === x) { if (bound) return JSON.stringify(bound) === JSON.stringify(t); bound = t as E; return true }
    if (p.op !== t.op) return false
    const pe = Object.entries(p), te = t as Record<string, unknown>
    return pe.every(([k, v]) => k === 'op' || (typeof v === 'object' && v !== null ? (Array.isArray(v) ? Array.isArray(te[k]) && (te[k] as unknown[]).length === v.length && v.every((y, i) => go(y as E, (te[k] as E[])[i]!)) : go(v as E, te[k] as E)) : v === te[k]))
  }
  return go(pattern, term) ? bound : undefined
}
// Each quantified flag's witness w?f (one per key, over several): a key where its condition fails, when it does;
// every-key facts are wanted there too.
const witnesses = (m: Machine): E[] => Object.entries(m.step.flags ?? {}).flatMap(([f, c]) => (c.op === 'all' ? witnessesOf(f, c).map((name): E => ({op: 'var', name})) : []))
// The keys each quantified flag is assumed at (instances under ?f): over several keys, the tuples that relate the
// goals' own keys as a law about several keys takes them (every tuple, without them).
const flagInstances = (m: Machine, keys: E[], focus: string[] = []): Instances => Object.fromEntries(Object.entries(m.step.flags ?? {}).flatMap(([f, c]) => {
  if (c.op !== 'all') return []
  const n = boundOf(c).length
  return [[`?${f}`, n === 1 ? keys : focus.length ? related(keys, focus, n).flat() : tuples(keys, n)]]
}))
// A k-step law whose steps keep a condition (a flag that holds at one step and is read again at the next) fails at a
// later step's witness only where the condition held before: so, per quantified flag over one key, the instances at the
// law's own keys and that flag's witness at every step (a later step's input or witness is a key an earlier frame may
// name, as a flag holds at every key: kernel.ts's checkStepLaws). Few instances, where the shared ones are many and
// mostly idle.
const keptAcross = (m: Machine, laws: Law[], inst: Instances, own: E[], k: number): Instances[] => k < 2 ? [] : Object.entries(m.step.flags ?? {}).flatMap(([f, c]) => {
  if (c.op !== 'all' || c.keys?.length) return []
  const ws = Array.from({length: k}, (_, i): E => ({op: 'var', name: i ? `w?${f}@${i + 1}` : `w?${f}`})), keys = [...own, ...ws.slice(0, 1)]
  const keep = new Set(keys.map(e => JSON.stringify(e)))
  return [Object.fromEntries(Object.entries(inst).map(([n, ks]) => [n, n === `?${f}` ? [...keys, ...ws.slice(1)].filter((e, i, all) => all.findIndex(o => JSON.stringify(o) === JSON.stringify(e)) === i) : arity(m, laws, n) === 1 ? ks.filter(e => keep.has(JSON.stringify(e))) : ks]))]
})
const pairFlags = (m: Machine) => Object.values(m.step.flags ?? {}).some(c => c.op === 'all' && !!c.keys?.length)
// How many keys each instance of a name takes: a law's, or a quantified flag's (?f).
const arity = (m: Machine | undefined, laws: Law[], n: string): number => {
  const q = n.startsWith('?') ? m?.step.flags?.[n.slice(1)] : undefined
  return q?.op === 'all' ? boundOf(q).length : (laws.find(l => l.name === n)?.keys?.length ?? 0) + 1
}
// The instances some goals need, for every entry point: the every-key laws and the quantified flags at `seed` (the keys
// the step and the laws read, when known before any goal is built), then twice round: the facts at every key the goals
// built so far read a function at, and, where the seed doesn't cover them (no seed, positions that shift, a law about
// several keys), the every-key laws and flags at every key they read a map at (a law about several keys at tuples
// relating `focus`, the goals' own keys).
function instancesFor(m: Machine, laws: Law[], build: (inst: Instances) => Goal[], opts: {seed?: E[], focus?: string[], start?: Instances, reads?: boolean} = {}): Instances {
  const seed = opts.seed && [...new Map(opts.seed.map(e => [JSON.stringify(e), e])).values()]
  let inst: Instances = opts.start ?? (seed ? {...Object.fromEntries(laws.filter(l => l.forall).map(l => [l.name, l.keys?.length ? [] : seed!])), ...flagInstances(m, seed, opts.focus)} : {})
  const reads = opts.reads ?? (!opts.seed || shifts(m) || laws.some(l => l.keys?.length) || pairFlags(m))
  for (let round = 0; round < 2 && !pastWall(); round++) {
    if (m.facts?.length) inst = withFacts(m, inst, fnKeys(m, build(inst)))
    if (reads) { const {keys, byMap} = mapReads(build(inst)); inst = union(withReads(laws, inst, keys, opts.focus ?? [], byMap, Object.keys(m.fns ?? {})), flagInstances(m, keys, opts.focus), m) }
  }
  return inst
}
// Instances worth their rows: a quantified flag or a law about every key, at a key where the goals read a map the way
// its condition reads one at its own key (M[k] read as M[t], M[k + b] as M[t + b]). An instance anywhere else gives each
// leaf rows about cells nothing else mentions, and a split for each (a flag over grant numbers at a path's positions,
// say); a tuple, where each of its keys is so read. Found as a fixpoint from the goals with none of these instances, as
// an instance's rows read cells that make others worth it; a name whose condition reads no map at its keys, and the
// focus keys, are kept as they are.
// Untrusted: fewer instances still make a checked proof, and where they don't prove a goal the full set is tried.
const triggers = (body: C, key: string): {map: string, at: E}[] => {
  const out: {map: string, at: E}[] = [], mentions = (e: E): boolean => JSON.stringify(e).includes(`"name":${JSON.stringify(key)}`)
  eachRead(e => { if (mentions(e.key)) out.push({map: e.map, at: e.key}) }).inC(body)
  return out
}
const substKey = (e: E, key: string, by: E): E => JSON.parse(JSON.stringify(e).replaceAll(`{"op":"var","name":${JSON.stringify(key)}}`, JSON.stringify(by))) as E
// GDP_TRIGGER=0 keeps every instance (for comparing).
const triggerOn = env.GDP_TRIGGER !== '0'
export function triggered(m: Machine, laws: Law[], inst: Instances, build: (inst: Instances) => Goal[], focus: string[] = []): Instances {
  if (!triggerOn) return inst
  // Per name: its bound keys, and for each the triggers that read it alone (a key with none takes any value).
  // Tuple-keyed function images (including generated witnesses) introduce key
  // terms outside relational reads. Keep legacy focus seeds for that shape.
  const tupleFunctions = Object.entries(m.step.maps ?? {}).some(([name, w]) => !m.relations?.[name] && !('each' in w) && w.key.op === 'tup')
  const tupled = !!Object.keys(m.relations ?? {}).length && !tupleFunctions
  const bodies = new Map<string, {keys: string[], per: {map: string, at: E}[][]}>()
  for (const [n, ks] of Object.entries(inst)) {
    if (!ks.length) continue
    const q = n.startsWith('?') ? m.step.flags?.[n.slice(1)] : undefined, l = q ? undefined : laws.find(x => x.name === n)
    const body = q?.op === 'all' ? q.c : l?.forall ? l.holds : undefined, keys = q?.op === 'all' ? boundOf(q) : l?.forall ? [l.forall, ...(l.keys ?? [])] : []
    if (!body) continue
    const per = keys.map(key => {
      const ts = triggers(body, key).filter(t => tupled || keys.every(o => o === key || !JSON.stringify(t.at).includes(`"name":${JSON.stringify(o)}`)))
      // A joint read constrains the tuple; independent field reads would admit
      // its Cartesian product again. Missing useful tuples can still enter by MBQI.
      const joint = tupled ? ts.filter(t => keys.filter(k => JSON.stringify(t.at).includes(`"name":${JSON.stringify(k)}`)).length > 1) : []
      return joint.length ? joint : ts
    })
    if (per.some(t => t.length)) bodies.set(n, {keys, per})
  }
  if (!bodies.size) return inst
  const tuplesOf = (n: string, ks: E[]) => { const a = bodies.get(n)!.keys.length; return Array.from({length: Math.floor(ks.length / a)}, (_, t) => ks.slice(t * a, (t + 1) * a)) }
  const kept = (tuple: E[]) => !tupled && tuple.some(e => e.op === 'var' && focus.includes(e.name))
  const out: Instances = Object.fromEntries(Object.entries(inst).map(([n, ks]) => [n, bodies.has(n) ? tuplesOf(n, ks).filter(kept).flat() : ks]))
  // Tuple substitution is independent of the growing read set. Cache each
  // candidate's trigger text once, rather than rebuilding it every round.
  const candidates = new Map<string, {tuple: E[], id: string, tests: (string[] | undefined)[]}[]>()
  for (const n of bodies.keys()) candidates.set(n, tuplesOf(n, inst[n]!).map(tuple => ({tuple, id: JSON.stringify(tuple), tests: []})))
  for (let round = 0; round < 8 && !pastWall(); round++) {
    const reads = new Set<string>()
    const {inC} = eachRead(e => { reads.add(`${e.map}|${JSON.stringify(e.key)}`) })
    for (const g of build(out)) g.hyps.forEach(inC)
    let grew = false
    for (const [n, {keys, per}] of bodies) {
      const have = new Set(tuplesOf(n, out[n]!).map(t => JSON.stringify(t)))
      for (const {tuple, id, tests} of candidates.get(n)!) {
        if (have.has(id) || !keys.every((key, i) => {
          const at = tests[i] ??= per[i]!.map(({map, at}) => `${map}|${JSON.stringify(tupled ? substE(at, {vars: Object.fromEntries(keys.map((k, j) => [k, tuple[j]!])), maps: {}, flags: {}}) : substKey(at, key, tuple[i]!))}`)
          return !at.length || at.some(t => reads.has(t))
        })) continue
        out[n]!.push(...tuple); have.add(id); grew = true
      }
    }
    if (!grew) break
  }
  return out
}
// For a certificate others check again (the Lean export sets `minimal.on`): the instances of quantified flags a proof
// found that its leaves refute with, the proof grown again with those alone. The checked goal is then built from far
// fewer hypotheses (a law about pairs of items with 900 instance hypotheses and 30 leaves using a few of them, say).
export const minimal = {on: false}
// The rows a tree's leaf reads, where the search that made it knew them (kernel/cdcl.ts's unfolding: reader.ts's rows,
// kernel.ts's at the leaf's path): how many the path gives, and each one its derivation reads, with its form and source
// (a hypothesis' index, the pair of cells it equates, else -1). A large tree is then walked without its leaves' rows
// read again (usedHyps, core/translate.ts): ledger/tigerbeetle/transfers' 21,108 leaves took 22.6 s here.
export type LeafRows = {n: number, at: Map<number, {lin: Lin, src: number | [string, string]}>}
export const leafRowsOf = new WeakMap<object, LeafRows>()
// The hypotheses a tree's leaves read: each leaf's input rows, and the rows its products multiply.
export function usedHyps(goal: Goal, tree: Tree, path: Path = new Map(), out = new Set<number>()): Set<number> {
  const known = 'leaf' in tree && !tree.products && !tree.squares ? leafRowsOf.get(tree) : undefined
  if (known && 'leaf' in tree) {
    for (const st of tree.leaf) if (st.kind === 'input') { const s = known.at.get(st.index)?.src; if (typeof s === 'number' && s >= 0) out.add(s) }
    return out
  }
  if ('leaf' in tree) {
    const rows = rowsAt(goal, path), n = rows.length, sq = tree.squares?.length ?? 0
    const mark = (i: number): void => {
      if (i < n) { const s = rows[i]!.src; if (s && 'fact' in s) out.add(s.fact) } else if (i >= n + sq) { const pq = tree.products?.[i - n - sq]; if (pq) { mark(pq[0]); mark(pq[1]) } }
    }
    for (const st of tree.leaf) if (st.kind === 'input') mark(st.index)
    return out
  }
  const id = canon(tree.split)
  usedHyps(goal, tree.yes, new Map(path).set(id, {lin: tree.split, holds: true}), out)
  return usedHyps(goal, tree.no, new Map(path).set(id, {lin: tree.split, holds: false}), out)
}
// The tuples of each quantified flag whose hypotheses `used` names: a flag's instance hypotheses follow its ?f <= 1 in
// the goal, in the instances' order (kernel.ts's closing).
function usedInstances(m: Machine, goal: Goal, inst: Instances, used: Set<number>, focus: string[]): Instances {
  const out: Instances = {...inst}
  for (const [f, q] of Object.entries(m.step.flags ?? {})) {
    if (q.op !== 'all' || !inst[`?${f}`]?.length) continue
    const at = goal.hyps.findIndex(h => h.op === '<=' && h.a.op === 'var' && h.a.name === `?${f}` && h.b.op === 'const' && h.b.value === 1)
    if (at < 0) continue
    const a = boundOf(q).length, ks = inst[`?${f}`]!
    out[`?${f}`] = Array.from({length: Math.floor(ks.length / a)}, (_, t) => ks.slice(t * a, (t + 1) * a))
      .filter((tuple, t) => used.has(at + 1 + t) || tuple.some(e => e.op === 'var' && focus.includes(e.name))).flat()
  }
  return out
}
const sameInstances = (a: Instances, b: Instances) => Object.keys(b).every(n => (a[n]?.length ?? 0) === b[n]!.length)
// Instances without the keys that read any of these names (a law about several keys loses each tuple that does).
const avoiding = (inst: Instances, names: string[], laws: Law[], m?: Machine): Instances => {
  const bad = (e: E) => names.some(n => JSON.stringify(e).includes(`"name":${JSON.stringify(n)}`))
  return Object.fromEntries(Object.entries(inst).map(([n, keys]) => {
    const a = arity(m, laws, n), groups = Array.from({length: Math.floor(keys.length / a)}, (_, t) => keys.slice(t * a, (t + 1) * a))
    return [n, groups.filter(tuple => !tuple.some(bad)).flat()]
  }))
}
// Two sets of instances together: each name at the keys (or tuples) of both.
const union = (a: Instances, b: Instances, m?: Machine): Instances => {
  const out: Instances = {...a}
  for (const [n, keys] of Object.entries(b)) {
    const k = arity(m, [], n), groups = (ks: E[]) => Array.from({length: Math.floor(ks.length / k)}, (_, t) => ks.slice(t * k, (t + 1) * k))
    const seen = new Set(groups(out[n] ?? []).map(g => JSON.stringify(g)))
    out[n] = [...(out[n] ?? []), ...groups(keys).filter(g => !seen.has(JSON.stringify(g)) && !!seen.add(JSON.stringify(g))).flat()]
  }
  return out
}

export type Report = {proven: boolean, nodes: number, leaves: number, failed?: {goal: string, stuck: string, witness?: Record<string, number>, why?: string}, checked: boolean}

// --- some key: laws with a witness ---------------------------------------------------------------------------------------

// A quantifier at a negative place of a law (some key where a condition holds: ¬∀k. ¬c) is proven through a witness, a
// term naming the key: the law proven is the stronger one, c at the witness, and `stated` keeps the law as written. The
// witness is the law's own (someKey's second argument) or the first of a few candidates under which the laws prove: 0,
// the params, the state, the law's key (and for a step law, the request and the state after), and each map read at
// those. Nothing here is trusted: the kernel sees laws with the witness in place.
type Some = Extract<C, {op: 'all'}>
const someKeys = (c: C, positive = true): Some[] => c.op === 'all' ? [...(positive ? [] : [c]), ...someKeys(c.c, positive)] : c.op === 'not' ? someKeys(c.x, !positive) : c.op === 'and' || c.op === 'or' ? c.xs.flatMap(y => someKeys(y, positive)) : []
function atWitness(c: C, picks: Record<string, E>, positive = true): C {
  switch (c.op) {
    case 'all': return !positive && picks[c.key] ? atWitness(substVar(c.c, c.key, picks[c.key]!), picks, positive) : {...c, c: atWitness(c.c, picks, positive)}
    case 'not': return {op: 'not', x: atWitness(c.x, picks, !positive)}
    case 'and': case 'or': return {op: c.op, xs: c.xs.map(y => atWitness(y, picks, positive))}
    case 'flag': case '<': case '<=': case '=': return c
  }
}
function substVar(c: C, name: string, by: E): C {
  const e = (t: E): E => {
    switch (t.op) {
      case 'var': return t.name === name ? by : t
      case 'const': return t
      case 'mul': return {...t, a: e(t.a)}
      case 'if': return {op: 'if', c: substVar(t.c, name, by), then: e(t.then), else: e(t.else)}
      case 'get': return {...t, key: e(t.key)}
      case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup': return {...t, a: e(t.a), b: e(t.b)}
      case 'proj': return {...t, a: e(t.a)}
    }
  }
  return c.op === 'flag' ? c : c.op === 'all' ? {...c, c: substVar(c.c, name, by)} : c.op === 'not' ? {op: 'not', x: substVar(c.x, name, by)} : c.op === 'and' || c.op === 'or' ? {op: c.op, xs: c.xs.map(y => substVar(y, name, by))} : {...c, a: e(c.a), b: e(c.b)}
}
const candidates = (m: Machine, names: string[]): E[] => {
  const vars = [...new Set([...names, ...m.params, ...Object.keys(m.state)])]
  return [{op: 'const', value: 0}, ...vars.map((name): E => ({op: 'var', name})), ...Object.keys(m.maps ?? {}).flatMap(map => vars.map((name): E => ({op: 'get', map, key: {op: 'var', name}})))]
}
// Witnesses for every some-key in `items`, chosen in order: each the first candidate under which `proves` accepts the
// items whose some-keys are all named so far. Undefined, with the some-key's law, if none does.
function chooseWitnesses<T extends {name: string}>(items: T[], body: (t: T) => C, names: (t: T) => string[], m: Machine, proves: (resolved: T[]) => boolean, rebuild: (t: T, c: C) => T): {items: T[]} | {stuck: string} {
  const picks: Record<string, E> = {}
  for (const t of items) for (const q of someKeys(body(t))) if (q.witness) picks[q.key] = q.witness
  const resolved = (all: boolean) => items.filter(t => all || someKeys(body(t)).every(q => q.key in picks)).map(t => (someKeys(body(t)).length ? rebuild(t, atWitness(body(t), picks)) : t))
  for (const t of items) for (const q of someKeys(body(t))) {
    if (q.key in picks) continue
    const found = candidates(m, names(t)).find(w => { picks[q.key] = w; return proves(resolved(false)) })
    if (!found) { delete picks[q.key]; return {stuck: `no witness found for some key in ${t.name}: name one (someKey(f, witness))`} }
  }
  return {items: resolved(true)}
}

export function proveLaws(m: Machine, laws: Law[]): Report & {laws?: Law[], machine?: Machine, ghosts?: string[], witnesses?: Record<string, string>, proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}} {
  // Laws with "there exists" (core/exists.ts): proven through witnesses, as plain laws of the machine with its ghosts.
  if (someLaws(laws)) return proveSome(m, laws) as ReturnType<typeof proveLaws>
  if (!laws.some(l => someKeys(l.holds).length)) return proveLawsAsGiven(m, laws)
  const out = chooseWitnesses(laws, l => l.holds, l => (l.forall ? [l.forall] : []), m, ls => { const r = proveLawsAsGiven(m, ls); return r.proven && r.checked }, (l, holds) => ({...l, holds, stated: l.stated ?? l.holds}))
  if ('stuck' in out) return {proven: false, nodes: 0, leaves: 0, failed: {goal: 'witnesses', stuck: out.stuck}, checked: false}
  return {...proveLawsAsGiven(m, out.items), laws: out.items}
}
// One law's two goals, every law assumed (core/infer.ts adds laws one at a time and reproves only what isn't proven
// yet); not a proof of the set, which proveLaws gives. Laws with some key go through proveLaws.
// Decisions at the simplex's point (kernel/cdcl.ts's phaseAtPoint, as its model search decides) in the goals of a law set
// with a law about several keys, on the proof path (proveLaw, proveThinned): those goals' first rounds are often models
// a tuple short (withModels asks again at the model's tuples), and the search deciding by its saved phases wanders before
// it finds one (toy consensus's safety law: 108 s and 181k nodes for a model the point finds in 663; research/protocols/
// COST.md). Untrusted: the order of the cases only.
export const atPoint = {on: false}
const pointed = <T>(laws: Law[], f: () => T): T => {
  if (atPoint.on || !laws.some(l => l.keys?.length)) return f()
  atPoint.on = true
  try { return f() } finally { atPoint.on = false }
}
// A law's goals decided by the EPR path alone, for a caller that asks many (the enumeration's Houdini rounds): each goal
// decided, a refutation's core proven (each core's search within two seconds of its decision, the wall first), not
// widened; a model's tuples added where it breaks a law at the goal's keys (modelInstances), at most `rounds` times, the
// goals asked again; a model left is one on every tuple of the goal's keys, returned with its diagram. undefined: a goal
// not EPR-shaped, a core not proven or a budget run out (the caller's proveLaw next). What was settled before is kept
// (`settledOf`). Untrusted: a caller's verdict rests on its final proof.
type Decided = {proven: true, uses: string[]} | {proven: false, goal: string, stuck: 'sat', witness: Record<string, number>, diagram?: Diagram} | undefined
// (a probe's hook: each decision with its machine, set, index and ms)
export const decideLawHook: {on?: (m: Machine, laws: Law[], i: number, out: Decided, ms: number) => void} = {}
export function decideLaw(m: Machine, laws: Law[], i: number, rounds = modelRounds): Decided {
  if (!decideLawHook.on) return decideLaw0(m, laws, i, rounds)
  const t0 = performance.now(), out = decideLaw0(m, laws, i, rounds)
  decideLawHook.on(m, laws, i, out, performance.now() - t0)
  return out
}
// (why decideLaw last answered nothing: `refuted`, the abstraction refuted a goal whose core's proof didn't finish, a
// goal the CDCL search after it would find no quicker)
export const decideNote: {refuted: boolean, hint?: {goal: string, witness: Record<string,number>}} = {refuted: false}
function decideLaw0(m: Machine, laws: Law[], i: number, rounds: number): Decided {
  decideNote.refuted = false; delete decideNote.hint
  if (!fastShape(m, laws)) return undefined
  return withPatterns(m, laws, () => {
    if (!eprScope.patterns) return undefined
    const out = settled(m, laws, i, rounds, false)
    // (a proof's support: the laws its goals' proofs read)
    return !out ? undefined : 'proofs' in out ? {proven: true, uses: [...new Set(Object.values(out.proofs).flatMap(p => [...p.uses.keys()]))]} : out.stuck === 'sat' ? {proven: false, goal: out.goal, stuck: 'sat', witness: out.witness!, ...(out.diagram ? {diagram: out.diagram} : {})} : undefined
  })
}

// The decisions of a machine's laws, kept across calls (decideLaw's and proveSetFast's), by the machine's text and each
// law's name:
// - a law's proven goals: the instances they were decided at, and each goal's proof (a core's tree with the core, or the
//   whole goal's tree) with the laws it reads, each by its text (its support). A proof stays one while its support is in
//   the set: another law dropped or added only takes away or adds hypotheses it doesn't read.
// - a law's model, with the set it was found in: a model of every smaller set's goal too, whose hypotheses are fewer.
// Untrusted: proveSetFast's proof is made and checked whole at its end.
type Proof1 = {part: Goal, tree: Tree, uses: Map<string, string>, tuples?: Map<string, Set<string>>}
type Settled = {text: string, inst: Instances, proofs: Record<string, Proof1>}
type Unsettled = {goal: string, stuck: string, witness?: Record<string, number>, diagram?: Diagram, why?: string}
type Memo = {proven: Map<string, Settled>, models: Map<string, {text: string, model: Unsettled, strict: boolean, set: Map<string, string>}>}
// (GDP_MEMO_CAP: how many machines' decisions are kept, 4 by default; the hits and misses counted for the engine's trace)
const memoCap = Number(env.GDP_MEMO_CAP ?? 4)
export const memoHits = {n: 0, miss: 0, setKey: '', setJson: ''}
export const machineKey = (m: Machine): string => { const s = JSON.stringify(m); let h = 0; for (let i = 0; i < s.length; i++) h = (h * 31 + s.charCodeAt(i)) | 0; return `${s.length}:${h}` }
const memos = new Map<string, Memo>(), machineText = new WeakMap<Machine, string>(), lawText = new WeakMap<C, string>()
// (texts up to a renaming of fresh names, x$12: a rule's machine and kinds' laws are made again with
// fresh binders, so the same machine had another text each time and no decision was found again; GDP_MEMO_ALPHA=0 off)
const alpha = env.GDP_MEMO_ALPHA !== '0'
const alphaText = (s: string): string => { if (!alpha) return s; const to = new Map<string, string>(); return s.replace(/([A-Za-z_?]+)\$(\d+)/g, (w, p: string) => { let r = to.get(w); if (!r) to.set(w, (r = `${p}$_${to.size}`)); return r }) }
const textOfLaw = (l: Law): string => { let t = lawText.get(l.holds); if (t === undefined) lawText.set(l.holds, (t = alphaText(JSON.stringify([l.holds, l.forall ?? null, l.keys ?? null])))); return t }
function memoOf(m: Machine): Memo {
  let key = machineText.get(m)
  if (key === undefined) machineText.set(m, (key = alphaText(JSON.stringify(m))))
  let memo = memos.get(key)
  if (!memo) { if (memos.size >= memoCap) memos.clear(); memos.set(key, (memo = {proven: new Map(), models: new Map()})) }
  return memo
}
const stands = (p: Proof1, byName: Map<string, Law>): boolean => [...p.uses].every(([n, t]) => { const l = byName.get(n); return !!l && textOfLaw(l) === t })
// Law i settled, from what was kept where it still stands (a proof whose support is in the set, a model of a set holding
// this one): else its goals settled again, those whose proofs stand kept.
function settled(m: Machine, laws: Law[], i: number, rounds: number, usual: boolean): Settled | Unsettled | undefined {
  const law = laws[i]!, memo = memoOf(m), byName = new Map(laws.map(l => [l.name, l])), text = textOfLaw(law)
  const was = memo.proven.get(law.name), prev = was?.text === text ? was : undefined
  if (prev && Object.values(prev.proofs).every(p => stands(p, byName))) { memoHits.n++; return prev }
  memoHits.miss++
  const mo = rounds === modelRounds ? memo.models.get(law.name) : undefined
  if (mo && (!strict(usual) || mo.strict) && mo.text === text && laws.every(l => mo.set.get(l.name) === textOfLaw(l))) return mo.model
  const out = settle(m, laws, i, rounds, usual, prev)
  const cap = <T>(x: Map<string, T>) => { if (x.size >= 4096) x.clear(); return x }
  if (out && 'proofs' in out) cap(memo.proven).set(law.name, out)
  else if (out?.stuck === 'sat' && rounds === modelRounds) cap(memo.models).set(law.name, {text, model: out, strict: strict(usual), set: new Map(laws.map(l => [l.name, textOfLaw(l)]))})
  return out
}
// The fast path's machines: no history, sums or "there exists" (their goals are other machines' or need witnesses).
const fastShape = (m: Machine, laws: Law[]): boolean => !m.history && !(m.sums && Object.keys(m.sums).length) && !someLaws(laws) && !laws.some(l => someKeys(l.holds).length)
// How many hypotheses a law (or fact) is at these instances (kernel.ts's assumed), and its tuples' width.
const widthOf = (l: Law): number => (l.keys?.length ? 1 + l.keys.length : 1)
const countOf = (l: Law, inst: Instances): number => (l.forall ? Math.floor((inst[l.name]?.length ?? 0) / widthOf(l)) : 1)
// The laws a step goal's hypotheses `used` are instances of, each with the tuples (by text) it is at. kernel.ts's
// obligations lays a step goal out as: the facts at their instances, the precondition, the assumption, each law at its
// instances in order, the quantified flags' closing, the conclusion. Each such hypothesis is checked against its law's
// instance; one that isn't what the layout says leaves the sources unread (undefined). A start goal assumes no law.
function sourcesOf(m: Machine, laws: Law[], inst: Instances, goal: Goal, used: Iterable<number>): Map<string, Set<string>> | undefined {
  const out = new Map<string, Set<string>>()
  if (goal.name.endsWith(' @start')) return out
  let h = (m.facts ?? []).reduce((n, f) => n + countOf(f, inst), 0) + (m.pre ? 1 : 0) + (m.assume ? 1 : 0)
  const starts = laws.map(l => { const at = h; h += countOf(l, inst); return at })
  for (const u of used) {
    if (!laws.length || u < starts[0]! || u >= h) continue
    let k = 0
    while (k + 1 < laws.length && starts[k + 1]! <= u) k++
    const l = laws[k]!, t = u - starts[k]!, n = widthOf(l), tuple = l.forall ? (inst[l.name] ?? []).slice(t * n, (t + 1) * n) : []
    const want = assumed([l], l.forall ? {[l.name]: tuple} : {})[0]
    if (!want || JSON.stringify(want) !== JSON.stringify(goal.hyps[u])) return undefined
    if (!out.has(l.name)) out.set(l.name, new Set())
    out.get(l.name)!.add(JSON.stringify(tuple))
  }
  return out
}
// Law i's goals settled: each decided by the EPR path (a refutation's core proven), else (`usual`) by the usual search;
// a model's broken tuples added (modelInstances) `rounds` times, and on while the caller's deadline allows (four times
// as many at most: each round's model breaks a law at a tuple or two, sharded KV's caller goal from its enumerated cubes
// is proven in its sixth), a goal proven in an earlier round not asked
// again (the instances only grow). From `prev`, its instances (unless a law about keys is new since) and the proofs that
// still stand. The proofs with their support, or the goal not proven (a model with its diagram, or unknown), or
// undefined where the EPR path alone can't say (not `usual`).
function settle(m: Machine, laws: Law[], i: number, rounds: number, usual: boolean, prev?: Settled): Settled | Unsettled | undefined {
  const law = laws[i]!, byName = new Map(laws.map(l => [l.name, l]))
  // (decideLaw's and the fast set proof's: each law's keys of its sort alone, `bySort`; proveLaw's and the join's as they
  // were. The fast set proof is checked over the tuples its proofs read, and the usual proof follows where it fails)
  const reuse = prev && laws.every(l => !l.forall || l.name in prev.inst)
  let inst = reuse ? prev.inst : bySort(m, laws, lawInstances(m, laws, i))
  // (GDP_DLTRIG=1: decideLaw's first instances only those a goal's reads trigger (proveOne's `triggered`), the model
  // rounds adding the instances a model breaks (MBQI's))
  if (!reuse && (Object.keys(m.relations ?? {}).length ? env.GDP_DLTRIG !== '0' : !usual && env.GDP_DLTRIG === '1')) inst = triggered(plainOf(m), laws, inst, i2 => obligations(m, laws, {[law.name]: i2}, i), law.forall ? [`${law.forall}#`] : [])
  const proofs: Record<string, Proof1> = Object.fromEntries(Object.entries(prev?.proofs ?? {}).filter(([, p]) => stands(p, byName)))
  const unknown = (g: Goal, why = 'past the search\'s end'): Unsettled | undefined => (usual ? {goal: g.name, stuck: 'unknown', why} : undefined)
  // (past the `rounds` model rounds, each round within the caller's deadline, its model the answer where the round can't
  // finish: a model of fewer instances is still one of the goal as it was asked)
  const end = withinDeadline(Infinity)
  let last: Unsettled | undefined
  for (let round = 0; ; round++) {
    let more: Instances | undefined
    const late = round > rounds ? () => pastWall() || pastEprCap() || clock() > end : () => pastWall() || pastEprCap()
    for (const g of obligations(m, laws, {[law.name]: inst}, i)) {
      if (proofs[g.name]) continue
      if (late()) return strict(usual) ? unknown(g) : last ?? unknown(g)
      // (a wide goal decided over parts (growWide), each part by the EPR path: the abstraction of the whole is quadratic in
      // its cells, i4's engine set's step goal of 7,590 hypotheses ran 19M units past its caller's end and 10 GB)
      let o: (Outcome & {part?: Goal, core?: number[]}) | undefined = !eprScope.patterns ? undefined : wideFor(g) && tupledScope() ? eprWide(g, late) ?? withEprCap(wideEprUnits, () => eprFirst(g, {nodes: 0, until: clock() + 4_000}, false, late)) : eprFirst(g, {nodes: 0, until: clock() + 4_000}, false, late)
      // Initial states often erase every map read, leaving a small arithmetic goal
      // outside EPR. Do not require a whole-set proof just to seed its start tree.
      if (!o && g.name.endsWith(' @start') && !late()) o = grow(g, new Map(), {nodes: 0, until: end})
      // (a refutation whose core's proof didn't finish: a model from fewer instances, which these refute, is no answer;
      // decideLaw's unknown, the usual search's next)
      if (!o && eprLast.refuted) { if (!usual) { decideNote.refuted = true; return undefined } } else if (!o && (last || !usual)) return strict(usual) ? undefined : last
      // (the usual search, the EPR path not asked again)
      if (!o) { const busy = eprScope.busy; eprScope.busy = true; try { o = grow(g) } finally { eprScope.busy = busy } }
      if ('tree' in o) {
        // (a proof whose hypotheses' sources aren't read: its support every law of the set)
        const src = sourcesOf(m, laws, inst, g, o.core ?? usedHyps(g, o.tree))
        proofs[g.name] = {part: o.part ?? g, tree: o.tree, uses: new Map((src ? [...src.keys()] : laws.map(l => l.name)).map(n => [n, textOfLaw(byName.get(n)!)])), ...(src ? {tuples: src} : {})}
        continue
      }
      if (o.stuck !== 'sat' || !o.witness) return strict(usual) ? unknown(g, o.why) : last ?? unknown(g, o.why)
      last = {goal: g.name, stuck: 'sat', witness: o.witness, ...(o.diagram ? {diagram: o.diagram} : {}), why: 'a model'}
      // (strict, decideLaw's: a model is returned only where confirmed, no assumed law broken at it over its own domain;
      // one that breaks only instances of another sort, or that the rounds or the wall cut off, is no answer)
      const capped = !(round < rounds || (round < 4 * rounds && end !== Infinity && clock() < end)), raw = capped ? undefined : modelInstances(m, laws, inst, g, o.witness, undefined, true)
      if (!capped && !raw) return last
      more = raw && bySort(m, laws, raw)
      const count = (x: Instances) => Object.values(x).reduce((s2, ks) => s2 + ks.length, 0)
      if (strict(usual) && (capped || pastWall() || !more || count(more) <= count(inst))) { decideNote.hint = {goal: g.name, witness: o.witness}; return undefined }
      // (the model's only broken instances another sort's: the next round would find it again; decideLaw's no answer)
      if (more && count(more) <= count(inst)) return usual ? last : undefined
      if (!more || pastWall()) return last
      break
    }
    if (!more) return {text: textOfLaw(law), inst, proofs}
    inst = more
  }
}

// A wide goal over parts, each asked by the EPR path (its core widened to the part) or else the usual search: a tree is
// the part's, a model one of the whole. Parts for four times eprFirst's window (growWide's share of it), each part
// within that window.
function eprWide(g: Goal, late: () => boolean): (Outcome & {part?: Goal, core?: number[]}) | undefined {
  const out = growWide(g, {nodes: 0, until: clock() + 16_000}, (gp, until) => { const u = Math.max(until, clock() + 4_000); return eprFirst(gp, {nodes: 0, until: u}, true, late) ?? grow(gp, new Map(), {nodes: 0, until: u}) }, true)
  eprLast.refuted = false
  return out && ('tree' in out || (out.stuck === 'sat' && out.witness)) ? out : undefined
}
// A set of laws proven as proveLaws proves it, for a search that drops a law the proof fails at and asks again (the
// enumeration's set proof): each law's goals settled in order (kept from this call or decideLaw's where they stand), the
// first law not proven returned with its goal's model; when every law is, the proof made once: each law's instances only
// the tuples its proofs read, each proof widened to its goal there (else the goal grown), and the whole checked by
// kernel.ts (checkLaws). Machines with a history, sums or "there exists": proveLaws. A search's trial proof: no cyclic
// certificate is made.
export function proveSetFast(m: Machine, laws: Law[]): Report & {proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}, failed?: Report['failed'] & {diagram?: Diagram}} {
  if (env.GDP_MEMO_TRACE) { memoHits.setKey = machineKey(m); memoHits.setJson = JSON.stringify(m) }
  // (laws with "there exists": proveSome's witnesses, its whole set this fast proof over the ghosted machine)
  if (!fastShape(m, laws)) return someLaws(laws) && fastShape(m, laws.map(l => ({name: l.name, holds: l.holds}))) ? proveSome(m, laws, {whole: proveSetFast}) as ReturnType<typeof proveSetFast> : proveLaws(m, laws)
  return withPatterns(m, laws, () => pointed(laws, () => {
    const at: Settled[] = []
    for (let i = 0; i < laws.length; i++) {
      const out = settled(m, laws, i, modelRounds, true)!
      if (!('proofs' in out)) return {proven: false, nodes: 0, leaves: 0, checked: false, failed: {goal: out.goal, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {}), ...(out.why ? {why: out.why} : {}), ...(out.diagram ? {diagram: out.diagram} : {})}}
      at.push(out)
    }
    const instances: Record<string, Instances> = {}, trees: Record<string, Tree> = {}, byName = new Map(laws.map(l => [l.name, l]))
    let nodes = 0, leaves = 0
    for (const [i, law] of laws.entries()) {
      // (each law about keys at the tuples the proofs read; all of them where a proof's sources weren't read)
      const s = at[i]!, ps = Object.values(s.proofs), all = ps.some(p => !p.tuples)
      const inst: Instances = all ? s.inst : Object.fromEntries(Object.entries(s.inst).map(([n, ks]) => {
        const l = byName.get(n), k = l ? widthOf(l) : 1
        return [n, !l ? ks : ks.filter((_, j) => ps.some(p => p.tuples!.get(n)?.has(JSON.stringify(ks.slice(j - (j % k), j - (j % k) + k)))))]
      }))
      instances[law.name] = inst
      for (const g of obligations(m, laws, {[law.name]: inst}, i)) {
        const p = s.proofs[g.name]
        let tree = p && widen(p.part, g, p.tree)
        if (!tree) { const o = grow(g); if (!('tree' in o)) return stuckAt(g, o, nodes, leaves); tree = o.tree; nodes += o.nodes }
        trees[g.name] = tree
        leaves += countLeaves(tree)
      }
    }
    const proof = {instances, trees}
    return {proven: true, nodes, leaves, checked: checkLaws(m, laws, proof), proof}
  }))
}
export function proveLaw(m: Machine, laws: Law[], i: number): {proven: true} | {proven: false, goal: string, stuck: string, witness?: Record<string, number>, diagram?: Diagram} {
  if (laws.some(l => someKeys(l.holds).length) || someLaws(laws)) {
    const r = proveLaws(m, laws)
    return r.proven ? {proven: true} : {proven: false, goal: r.failed!.goal, stuck: r.failed!.stuck, ...(r.failed!.witness ? {witness: r.failed!.witness} : {})}
  }
  // (the thinned goals too by the EPR path where the rule's keys are composed: withModels' scope, entered here; first
  // the law settled by the EPR path as decideLaw settles it, kept where it stands: a caller's verdict rests on its final
  // proof, which widens and checks; wo's "a leader has the voting quorum's votes" from its 40-law set, 0.45 s there
  // against 25 s to unknown here)
  return withPatterns(m, laws, () => {
    const out = eprScope.patterns && fastShape(m, laws) ? settled(m, laws, i, modelRounds, false) : undefined
    if (out && 'proofs' in out) return {proven: true}
    if (out?.stuck === 'sat') return {proven: false, goal: out.goal, stuck: 'sat', ...(out.witness ? {witness: out.witness} : {}), ...(out.diagram ? {diagram: out.diagram} : {})}
    return pointed(laws, () => proveOne(m, laws, i))
  })
}
function proveOne(m: Machine, laws: Law[], i: number): {proven: true} | {proven: false, goal: string, stuck: string, witness?: Record<string, number>, diagram?: Diagram} {
  const law = laws[i]!, pm = plainOf(m), inst = lawInstances(m, laws, i)
  // Keep the ordinary fallback's actual trees too. A local proof can use a
  // ghost value as a key where EPR's sorted instances were insufficient. The
  // complete-set path widens these trees and checks every obligation afresh.
  const remember = (at: Instances, trees: Record<string, Tree>) => {
    if (!Object.values(m.step.maps ?? {}).some(w => !('each' in w) && w.key.op === 'tup') || !fastShape(m, laws)) return
    const byName = new Map(laws.map(l => [l.name, l])), proofs: Record<string, Proof1> = {}
    for (const g of obligations(m, laws, {[law.name]: at}, i)) {
      const tree = trees[g.name]
      if (!tree) return
      const src = sourcesOf(m, laws, at, g, usedHyps(g, tree))
      proofs[g.name] = {part: g, tree, uses: new Map((src ? [...src.keys()] : laws.map(l => l.name)).map(n => [n, textOfLaw(byName.get(n)!)])), ...(src ? {tuples: src} : {})}
    }
    const memo = memoOf(m)
    if (memo.proven.size >= 4096) memo.proven.clear()
    memo.proven.set(law.name, {text: textOfLaw(law), inst: at, proofs})
  }
  const few = triggered(pm, laws, inst, i2 => obligations(m, laws, {[law.name]: i2}, i), law.forall ? [`${law.forall}#`] : [])
  if (!sameInstances(few, inst)) {
    let proven = true
    const done: Record<string, Tree> = {}
    for (const goal of obligations(m, laws, {[law.name]: few}, i)) {
      const o = grow(goal)
      if ('tree' in o) { done[goal.name] = o.tree; continue }
      proven = false
      // (a goal that ran out past the deadline: the next instances can't be tried, and it is the verdict's goal)
      if (o.stuck === 'unknown' && ranOut()) return {proven: false, goal: goal.name, stuck: 'unknown'}
      break
    }
    if (proven) { remember(few, done); return {proven: true} }
  }
  // (a model breaking a law at a tuple of the goal's keys: those added, the law asked again)
  const {result: a, inst: at} = withModels(m, laws, inst, i2 => obligations(m, laws, {[law.name]: i2}, i), growAll, grownModel, grownSettled)
  if (!a.out) remember(at, a.done)
  return a.out ? {proven: false, goal: a.goal!.name, stuck: a.out.stuck, ...(a.out.witness ? {witness: a.out.witness} : {}), ...(a.out.diagram ? {diagram: a.out.diagram} : {})} : {proven: true}
}
// Goals grown in turn up to the first one unproven (withModels' question in proveLaw and proveThinned): the trees, their
// nodes and leaves, and the goal it stopped at with its outcome, whose model asks for more instances.
type Grown = {done: Record<string, Tree>, n: number, lv: number, goal?: Goal, out?: Extract<Outcome, {stuck: unknown}>}
function growAll(gs: Goal[]): Grown {
  const done: Record<string, Tree> = {}
  let n = 0, lv = 0
  for (const goal of gs) {
    const out = grow(goal)
    if (!('tree' in out)) return {done, n, lv, goal, out}
    done[goal.name] = out.tree; n += out.nodes; lv += countLeaves(out.tree)
  }
  return {done, n, lv}
}
const grownModel = (x: Grown) => (x.out?.stuck === 'sat' && x.out.witness ? {goal: x.goal!, w: x.out.witness} : undefined)
const grownSettled = (x: Grown) => !x.out || x.out.stuck === 'sat'
// Each law's keys only at keys of their sort (Ivy's sorts; untrusted: an instance left out only weakens a goal, and a
// set's proof is checked over its own instances). A sort is a class of a union-find over places: each part of a map's
// key (by its pattern, `M:map:i`), a map's whole key where a law's key is the whole key (`K:map`), a function's
// argument and value (`A:f`, `F:f`), and every name, a law's keys its own (`L:law:k`), a quantified flag's its own
// (`Q:f:k`). Names one comparison relates are one sort; a part that is a function's value is that function's value's.
// A key term whose sort is anchored (a map's part or key, a function's argument or value) and differs from the law key's
// anchored sort is left out of the law's tuples there; a composed term is a whole key, of the map whose pattern its
// factors are. GDP_SORTED=0 keeps every instance.
const sortedOn = env.GDP_SORTED !== '0'
// decideLaw's models confirmed only (GDP_STRICT=1; off by default: decentralized lock's rounds then lean on the proof
// path where an unconfirmed model used to answer, 27-36 s against 13-17 s): a model is returned where no assumed law is
// broken at it over its own domain, else nothing (research/protocols/engine/DESIGN.md, gen/ring)
let strictOn = false
// (decideLaw's models are confirmed ones only, always: an unconfirmed one, at the deadline or past the model rounds, was
// wrong against Z3 on 43 of wo's 143 top-down goals; GDP_STRICT=0 gives the old answer)
const strict = (usual: boolean) => !usual && (strictOn || env.GDP_STRICT !== '0')
// (strict models for a caller's own decisions: the engine's top-down phase, whose drops an unconfirmed model would make wrong)
export const withStrict = <T>(f: () => T): T => { const o = strictOn; strictOn = true; try { return f() } finally { strictOn = o } }
// (by machine and by the law set's names: one machine is asked with many sets)
const sortsMemo = new WeakMap<Machine, Map<string, {key: (law: string, k: string) => string, of: (e: E) => string | undefined, find: (a: string) => string, anchored: (a: string) => boolean}>>()
const sortPlacesOn = env.GDP_SORT_PLACES !== '0'
function sortsOf(m: Machine, laws: Law[]) {
  const par = new Map<string, string>(), find = (a: string): string => { const q = par.get(a); if (q === undefined || q === a) return a; const r = find(q); par.set(a, r); return r }
  const named = new Set<string>(), union = (a: string, b: string) => { named.add(a); named.add(b); const ra = find(a), rb = find(b); if (ra !== rb) par.set(ra, rb) }
  const pats = patternsOf(m, laws), whole = new Map<string, string>()
  // (only on machines with tuple keys, whose patterns are n zeros: elsewhere the sorts are as before, distributed_lock's
  // instances among them)
  const sortPlaces = sortPlacesOn && Object.values(pats).some(c => c.length > 1 && c[0] === 0)
  // (a map of one part read at a name, Src[p]: its value a sort too, F:Src, as a function's, what it is compared with and
  // the places it is read at: Src[Src[p]] is no key of Src where Src's values are nodes and its keys packets)
  // (GDP_SORT_PLACES=0: neither, for comparing)
  const valued = (e: Extract<E, {op: 'get'}>): boolean => sortPlaces && !((pats[e.map]?.length ?? 0) > 1) && e.key.op !== 'tup' && (e.key.op === 'var' || e.key.op === 'get')
  const leaves = (e: E, k: number, out: [E, number][]): void => { if (e.op === 'add') { leaves(e.a, k, out); leaves(e.b, k, out) } else if (e.op === 'mul') leaves(e.a, k * e.k, out); else if (e.op !== 'const') out.push([e, k]) }
  const walkC = (c: C, name: (v: string) => string): void => {
    const node = (e: E): string | undefined => (e.op === 'var' ? name(e.name) : e.op === 'get' && (m.fns?.[e.map] || valued(e)) ? `F:${e.map}` : undefined)
    const visit = (o: unknown): void => {
      if (!o || typeof o !== 'object') return
      const x = o as {op?: string, map?: string, key?: E, a?: E, b?: E}
      if (x.op === 'get' && x.key) {
        if (m.fns?.[x.map!]) { const n = node(x.key); if (n) union(n, `A:${x.map}`) }
        // (a tuple key: each part of its place's sort, M:map:i)
        else if (x.key.op === 'tup' && sortPlaces) tupleParts(x.key).forEach((e, i) => { const n = node(e); if (n) union(n, `M:${x.map}:${i}`) })
        else {
          const ls: [E, number][] = []; leaves(x.key, 1, ls)
          const pat = pats[x.map!] ?? [1]
          if (pat.length > 1 && ls.length === 1 && ls[0]![1] === 1) { const n = node(ls[0]![0]); if (n) union(n, `K:${x.map}`) }
          else { if (pat.length > 1) whole.set(JSON.stringify(x.key), `K:${x.map}`); for (const [e, k] of ls) { const idx = pat.indexOf(k), n = node(e); if (n && idx >= 0) union(n, `M:${x.map}:${idx}`) } }
        }
      }
      if ((x.op === '<' || x.op === '<=' || x.op === '=') && x.a && x.b) {
        const la: [E, number][] = [], lb: [E, number][] = []; leaves(x.a, 1, la); leaves(x.b, 1, lb)
        if (la.length === 1 && lb.length === 1 && Math.abs(la[0]![1]) === 1 && Math.abs(lb[0]![1]) === 1) { const p = node(la[0]![0]), q = node(lb[0]![0]); if (p && q) union(p, q) }
      }
      for (const y of Object.values(o)) visit(y)
    }
    visit(c)
  }
  const plain = (v: string) => `V:${v}`
  walkC(m.step as unknown as C, plain); if (m.assume) walkC(m.assume, plain); if (m.pre) walkC(m.pre, plain)
  for (const [f, c] of Object.entries(m.step.flags ?? {})) if (c.op === 'all') { const bs = new Set(boundOf(c)); walkC(c, v => (bs.has(v) ? `Q:${f}:${v}` : `V:${v}`)); witnessesOf(f, c).forEach((w, j) => union(`V:${w}`, `Q:${f}:${boundOf(c)[j]}`)) }
  // (a write at a key: the key read there; a write at every key, its binder the map's whole key)
  for (const [mp, w] of Object.entries(m.step.maps ?? {})) if (!('each' in w)) walkC({op: 'get', map: mp, key: w.key} as unknown as C, plain)
  for (const [mp, w] of Object.entries(m.step.maps ?? {})) if ('each' in w) union(`V:${w.each}`, (pats[mp] ?? [1]).length > 1 ? `K:${mp}` : `M:${mp}:0`)
  for (const l of laws) { const own = new Set([l.forall, ...(l.keys ?? [])].filter(Boolean)); walkC(l.holds, v => (own.has(v) ? `L:${l.name}:${v}` : `V:${v}`)) }
  // (two maps of one pattern whose parts are of the same sorts have their whole keys of one sort: wo's Votes, VoteMsg and
  // VoteRequestMsg, node × node, so a composed term read at one is an instance of a law about another's whole key)
  const multi = Object.keys(pats).filter(mp => pats[mp]!.length > 1)
  for (let grew = true; grew;) {
    grew = false
    for (const a of multi) for (const b of multi) if (a < b && find(`K:${a}`) !== find(`K:${b}`) && pats[a]!.join() === pats[b]!.join() && pats[a]!.every((_, i) => named.has(`M:${a}:${i}`) && named.has(`M:${b}:${i}`) && find(`M:${a}:${i}`) === find(`M:${b}:${i}`))) { union(`K:${a}`, `K:${b}`); grew = true }
  }
  const anchorOf = new Map<string, boolean>()
  for (const a of par.keys()) if (/^(M|K|A|F):/.test(a)) anchorOf.set(find(a), true)
  for (const a of [...par.values()]) if (/^(M|K|A|F):/.test(a)) anchorOf.set(find(a), true)
  const of = (e: E): string | undefined => {
    const w = whole.get(JSON.stringify(e)); if (w) return w
    const ls: [E, number][] = []; leaves(e, 1, ls)
    // (a composed term, several parts or a part under a factor, is a whole key: of the map whose pattern its factors are,
    // never a part's sort)
    if (ls.length !== 1 || ls[0]![1] !== 1) { const cs = ls.map(([, c]) => c).sort((a, b) => b - a).join(','); const mp = Object.keys(pats).find(k2 => pats[k2]!.length > 1 && [...pats[k2]!].sort((a, b) => b - a).join(',') === cs); return mp ? `K:${mp}` : `K:?${cs}` }
    const x = ls[0]![0]
    return x.op === 'var' ? (x.name.endsWith('#') ? undefined : `V:${x.name}`) : x.op === 'get' && (m.fns?.[x.map] || valued(x)) ? `F:${x.map}` : undefined
  }
  return {key: (law: string, k: string) => `L:${law}:${k}`, of, find, anchored: (a: string) => /^K:/.test(a) || !!anchorOf.get(find(a))}
}
function instanceSortGuard(m: Machine, laws: Law[]): (name: string, index: number, e: E) => boolean {
  if (!sortedOn) return () => true
  let byLaws = sortsMemo.get(m)
  if (!byLaws) sortsMemo.set(m, (byLaws = new Map()))
  const lk = laws.map(l => l.name).join('\u0001')
  let s = byLaws.get(lk)
  if (!s) { if (byLaws.size >= 64) byLaws.clear(); byLaws.set(lk, (s = sortsOf(m, laws))) }
  const S = s
  const keysOf = (n: string): string[] | undefined => {
    if (n.startsWith('?')) { const c = m.step.flags?.[n.slice(1)]; return c?.op === 'all' ? boundOf(c).map(k => `Q:${n.slice(1)}:${k}`) : undefined }
    const l = laws.find(x => x.name === n); return l?.forall ? [l.forall, ...(l.keys ?? [])].map(k => S.key(n, k)) : undefined
  }
  const wanted = new Map<string, string[] | undefined>()
  return (n, j, e) => {
    if (!wanted.has(n)) wanted.set(n, keysOf(n))
    const want = wanted.get(n)?.[j], se = S.of(e)
    return !want || !se || !S.anchored(se) || !S.anchored(want) || S.find(se) === S.find(want)
  }
}
function bySort(m: Machine, laws: Law[], inst: Instances): Instances {
  if (!sortedOn) return inst
  const accepts = instanceSortGuard(m, laws)
  return Object.fromEntries(Object.entries(inst).map(([n, ks]) => {
    const q = n.startsWith('?') ? m.step.flags?.[n.slice(1)] : undefined
    const l = laws.find(l => l.name === n)
    const want = q?.op === 'all' ? boundOf(q) : l?.forall ? [l.forall, ...(l.keys ?? [])] : undefined
    if (!want || !ks.length) return [n, ks]
    const a = want.length, out: E[] = []
    for (let t = 0; t + a <= ks.length; t += a) {
      const tuple = ks.slice(t, t + a)
      const ok = tuple.every((e, j) => accepts(n, j, e))
      if (ok) out.push(...tuple)
    }
    return [n, out]
  }))
}
// The instances law i's goals are read at (proveLaw's; core/infer.ts's join asks one goal at a time).
export function lawInstances(m: Machine, laws: Law[], i: number): Instances {
  // (a machine with sums: its plain machine's instances, as proveLawsAsGiven's)
  const law = laws[i]!, pm = plainOf(m), keys = [...readKeys(pm, laws), ...witnesses(pm)]
  return instancesFor(pm, laws, inst => obligations(m, laws, {[law.name]: inst}, i), {
    seed: [...keys, ...(law.forall ? [{op: 'var', name: `${law.forall}#`} as E] : []), ...(law.keys ?? []).map((name): E => ({op: 'var', name}))],
    focus: [...(law.forall ? [`${law.forall}#`] : []), ...(law.keys ?? [])],
  })
}
// (GDP_SET_FIRST=0: the usual way alone, for comparing)
const setFirstOn = env.GDP_SET_FIRST !== '0'
const setFirst = (m: Machine, laws: Law[]): ReturnType<typeof proveSetFast> | undefined => {
  // (machines with tuple keys alone, patterns of zeros: on radix keys the usual way is the one tuned, and a set proof
  // first cost sharded KV's no-lost-keys, whose witness passes ask the whole set again and again, 2.8M of work to 45M)
  if (!eprOn || !setFirstOn || pastWall() || !fastShape(m, laws) || !Object.values(patternsOf(plainOf(m), laws)).some(c => c.length > 1 && c.every(x => x === 0))) return undefined
  const out = proveSetFast(m, laws)
  if (modelsTrace) console.error(`[models] the set first: ${out.proven ? out.checked ? 'proven' : 'proven, not checked' : `not proven at ${out.failed?.goal}`}`)
  return out.proven && out.checked && out.proof ? out : undefined
}
// `defer`: the usual trees now, their certificate and check given to it as `finish`, which proveStepLaws runs once every
// step law is proven too: a verdict that fails needs neither (TigerBeetle's laws spent 50 s of 67 on the laws' certificate
// and check before a step law failed). Deferred, a certificate not made leaves the check to checkStepLaws, which reads
// these trees again.
function proveLawsAsGiven(m: Machine, laws: Law[], defer?: (finish: () => void) => void): Report & {proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}} {
  // Each law's two goals (start and step) get their own instances, seeded with its own keys.
  // (a machine with sums: its instances are its plain machine's, whose flags hold each sum's facts at every key)
  const pm = plainOf(m), keys = [...readKeys(pm, laws), ...witnesses(pm)], instances: Record<string, Instances> = {}
  // (an EPR-shaped machine's set over tuple keys proved first as proveSetFast proves it: each law settled by the EPR
  // path, its instances sorted and only the tuples its proofs read, its cores widened to goals that small; i4's learning
  // switch over relations 6 s there against 80 s here, whose check alone read goals of 1,200 hypotheses for 55 s. Not
  // proven, the usual way)
  const fast = defer ? undefined : setFirst(m, laws)
  if (!fast) laws.forEach((law, i) => {
    instances[law.name] = instancesFor(pm, laws, inst => obligations(m, laws, {...instances, [law.name]: inst}, i), {
      seed: [...keys, ...(law.forall ? [{op: 'var', name: `${law.forall}#`} as E] : []), ...(law.keys ?? []).map((name): E => ({op: 'var', name}))],
      focus: [...(law.forall ? [`${law.forall}#`] : []), ...(law.keys ?? [])],
    })
  })
  // (by default a covered machine's certificate is its cyclic proof, core/cyclic.ts's certCyclic, the usual trees its
  // input, not checked again; where none is made, the usual trees are checked and the proof counted uncovered)
  // (what no instance covers, read only where a cyclic mode is on: the usual route's own proofs, inferLaws' trial ones
  // among them, do nothing more than before)
  // A machine with a history: its laws are its plain machine's (historyMachine; the record goals leaf goals beside them).
  const modes = cyclicOn() || certOn(), hist = modes && m.history ? historyMachine(m) : undefined, mc = hist ? hist.machine : m
  const why = modes ? (sumsWhy(m) ?? uncoveredWhy(mc, laws)) : undefined, cert = certOn() && !why
  usualCheck.on = !cert && !defer
  const t0 = performance.now(), out = fast ?? (() => { try { return proveThinned(m, laws, {...instances}) } finally { usualCheck.on = true } })(), usualMs = performance.now() - t0
  if (out.proof) usualProof.last = {m, laws, proof: out.proof}
  const inst = out.proof?.instances ?? instances
  const searched = () => { const {facts, specs} = machineNodes(mc, laws, inst); return proveCyclic(facts, specs) }
  const translated = out.proof ? ((st: TStats) => translatedProof(() => JSON.stringify(['machine', mc, laws, inst]), () => timedKind('instance', 0, () => machineNodes(mc, laws, inst, out.proof!, st)), st)) : undefined
  // The certificate (or, where none is made, the check), now or where the caller defers it.
  const finish = () => {
    if (defer && !cert && cyclicOn() && out.proven && out.proof) out.checked = checkLaws(m, laws, out.proof)
    if (cyclicOn()) {
      const usual = out.proven && out.checked
      // (a history: its plain machine's cyclic proof, and its record goals as the leaf goals they are; a machine with flags
      // that hold at every key the usual route doesn't prove: not searched, as before 0.19.0, a search there costs seconds)
      const records = !hist || hist.goals.every(g => { const tr = out.proof?.trees[g.name] ?? (() => { const o = grow(g); return 'tree' in o ? o.tree : undefined })(); return tr !== undefined && check(g, tr) })
      const recordFails = (): CyclicVerdict => ({proven: false, checked: false, node: m.name, goal: 'a record goal', stuck: 'not proven'})
      if (!why && (usual || !hasQuantified(mc))) crossCyclic('machine', m.name, usual, records ? searched : recordFails, usualMs, records ? translated : undefined)
      else cycLog({kind: 'machine', name: m.name, usual, uncovered: true, why: why ?? 'a flag at every key the usual route does not prove'})
    }
    if (cert && out.proven && out.proof) {
      const c = certCyclic('machine', m.name, translated, searched, usualMs)
      if (c.checked) {
        // (a history's record goals checked as they are: leaf goals)
        out.checked = !hist || hist.goals.every(g => out.proof!.trees[g.name] !== undefined && check(g, out.proof!.trees[g.name]!))
        Object.assign(out.proof, {cyclic: c.proof})
      } else {
        // (deferred: the step laws' certificate translates these trees too, and where it isn't made checkStepLaws checks them)
        if (!defer) out.checked = checkLaws(m, laws, out.proof!)
        uncovered('machine', m.name, c.why)
      }
    } else if (certOn() && why && out.proven) cycLog({kind: 'machine', name: m.name, cert: true, uncovered: true, why})
  }
  if (defer) defer(finish)
  else finish()
  return out
}
// Whether the usual proof's trees are checked (off while GDP_CERT=cyclic makes the certificate a cyclic proof).
export const usualCheck = {on: true}
// The last machine proof made (core/dsl.ts's recurrences read their machine's, to translate it: core/cyclic.ts).
export const usualProof: {last?: {m: Machine, laws: Law[], proof: {instances: Record<string, Instances>, trees: Record<string, Tree>}}} = {}
// Each law with its instances thinned (`triggered`) where that proves it, else with all of them.
// A machine with sums has no cyclic twin yet: its certificate is the usual trees, checked with its cover goals.
const sumsWhy = (m: Machine): string | undefined => (m.sums && Object.keys(m.sums).length ? 'a sum over a map\'s keys (Sums.lean checks the usual trees)' : undefined)
function proveThinned(m: Machine, laws: Law[], instances: Record<string, Instances>): Report & {proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}} {
  return withPatterns(m, laws, () => pointed(laws, () => thinned(m, laws, instances)))
}
function thinned(m: Machine, laws: Law[], instances: Record<string, Instances>): Report & {proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}} {
  const trees: Record<string, Tree> = {}, fulls = {...instances}
  let nodes = 0, leaves = 0
  for (const [i, law] of laws.entries()) {
    const full = instances[law.name]!, focus = law.forall ? [`${law.forall}#`] : []
    const few = triggered(plainOf(m), laws, full, inst => obligations(m, laws, {...instances, [law.name]: inst}, i), focus)
    if (modelsTrace) console.error(`[models] law ${law.name}: ${Object.values(full).reduce((a, ks) => a + ks.length, 0)} keys, ${Object.values(few).reduce((a, ks) => a + ks.length, 0)} triggered`)
    // (thinned instances first, then the full ones; each asked again at the tuples its models ask for)
    for (const inst of sameInstances(few, full) ? [full] : [few, full]) {
      const {result: a, inst: at} = withModels(m, laws, inst, i2 => obligations(m, laws, {...instances, [law.name]: i2}, i), growAll, grownModel, grownSettled)
      instances[law.name] = at
      if (inst === full) fulls[law.name] = at
      // (one that ran out past the wall: the next instances can't be tried, and the goal that ran out is the verdict's, not
      // the next one's first goal)
      if (a.out && inst !== full && !(a.out.stuck === 'unknown' && ranOut())) continue
      if (a.out) return stuckAt(a.goal!, a.out, nodes, leaves)
      Object.assign(trees, a.done); nodes += a.n; leaves += a.lv
      break
    }
  }
  // The goals of no one law (a history's own), with the instances chosen.
  for (const goal of obligations(m, laws, instances)) {
    if (trees[goal.name]) continue
    const out = grow(goal)
    // Where thinned instances leave such a goal unproven, every goal again with the full ones.
    if (!('tree' in out) && laws.some(l => instances[l.name] !== fulls[l.name])) return proveWith(m, laws, fulls)
    if (!('tree' in out)) return stuckAt(goal, out, nodes, leaves)
    trees[goal.name] = out.tree
    nodes += out.nodes
    leaves += countLeaves(out.tree)
  }
  const proof = {instances, trees}
  return {proven: true, nodes, leaves, checked: !usualCheck.on || checkLaws(m, laws, proof), proof}
}
// A goal left unproven, the search's report so far.
const stuckAt = (goal: Goal, out: Extract<Outcome, {stuck: unknown}>, nodes: number, leaves: number): Report => ({proven: false, nodes, leaves, failed: {goal: goal.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {}), ...(out.why ? {why: out.why} : {})}, checked: false})
// Every goal of the laws with these instances.
function proveWith(m: Machine, laws: Law[], instances: Record<string, Instances>): Report & {proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}} {
  const trees: Record<string, Tree> = {}
  let nodes = 0, leaves = 0
  for (const goal of obligations(m, laws, instances)) {
    const out = grow(goal)
    if (!('tree' in out)) return stuckAt(goal, out, nodes, leaves)
    trees[goal.name] = out.tree
    nodes += out.nodes
    leaves += countLeaves(out.tree)
  }
  const proof = {instances, trees}
  return {proven: true, nodes, leaves, checked: !usualCheck.on || checkLaws(m, laws, proof), proof}
}
// Step laws (kernel.ts's stepLawObligations): the laws proven first (they are assumed), then one goal per step law, the
// every-key laws assumed at every key the step, the laws and the step laws read.
type StepProof = {laws: {instances: Record<string, Instances>, trees: Record<string, Tree>}, instances: Instances, perStep?: Record<string, Instances>, trees: Record<string, Tree>}
export function proveStepLaws(given0: Machine, given: Law[], stepLaws: StepLaw[]): Report & {laws?: Law[], machine?: Machine, stepLaws?: StepLaw[], proof?: StepProof, uncovered?: string[]} {
  // (plain laws: their certificate and check made only once the step laws are proven too, `ready` below; where it isn't
  // made, checkStepLaws reads their trees again)
  let finish: (() => void) | undefined
  const base: ReturnType<typeof proveLaws> = !someLaws(given) && !given.some(l => someKeys(l.holds).length) ? proveLawsAsGiven(given0, given, f => { finish = f }) : proveLaws(given0, given)
  const ready = () => { const f = finish; finish = undefined; f?.() }
  if (!base.proven || !base.proof) return {proven: false, nodes: base.nodes, leaves: base.leaves, ...(base.failed ? {failed: base.failed} : {}), checked: false}
  const laws = base.laws ?? given
  // (laws with "there exists": the step laws over the machine with the ghosts their witnesses are)
  const m = base.machine ?? given0, mx = base.machine ? {machine: base.machine} : {}
  if (stepLaws.some(sl => someKeys(sl.then).length)) {
    // Each step law's witnesses on its own (a step law assumes no other), the request and the state after among them.
    const plain = plainOf(m), after = Object.keys(plain.state).map(n => `${n}'`)
    const out = chooseWitnesses(stepLaws, sl => sl.then, sl => [...(sl.forall ? [sl.forall] : []), ...plain.inputs, ...after], plain,
      sls => sls.every(sl => { const r = proveStepLawsAsGiven(m, laws, [sl], base, ready); return r.proven && r.checked }), (sl, then) => ({...sl, then}))
    if ('stuck' in out) return {proven: false, nodes: base.nodes, leaves: base.leaves, failed: {goal: 'witnesses', stuck: out.stuck}, checked: false}
    return {...proveStepLawsAsGiven(m, laws, out.items, base, ready), ...(base.laws ? {laws} : {}), ...mx, stepLaws: out.items}
  }
  return {...proveStepLawsAsGiven(m, laws, stepLaws, base, ready), ...(base.laws ? {laws} : {}), ...mx}
}
// The keys a step law reads its maps at, and its own.
const ownKeys = (plain: Machine, sl: StepLaw): E[] => [...keysInlined(plain, [sl.then, ...(sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when])].flatMap(readKeysC)),
  ...[sl.forall, ...(sl.keys ?? [])].flatMap(key => (key ? [{op: 'var', name: key} as E] : []))]
// Each step law's instances (proveStepLaws'; core/infer.ts's join asks one goal at a time).
export function stepLawInstances(m: Machine, laws: Law[]): (sl: StepLaw) => Instances {
  const plain = plainOf(m)
  const shared = [...readKeys(plain, laws), ...witnesses(plain)], named = [...laws, ...(plain.facts ?? [])], reads = shifts(plain) || laws.some(l => l.keys?.length) || pairFlags(plain)
  const own = (sl: StepLaw) => ownKeys(plain, sl)
  return sl => {
    const zone = stepZone(plain, sl.steps ?? 1), keep = (inst: Instances) => avoiding(inst, zone, named, plain)
    return keep(instancesFor(plain, laws, inst => stepLawObligations(m, laws, keep(inst), sl),
      {seed: [...shared, ...own(sl)], focus: [sl.forall, ...(sl.keys ?? [])].flatMap(k => (k ? [k] : [])), reads}))
  }
}
function proveStepLawsAsGiven(m: Machine, laws: Law[], stepLaws: StepLaw[], base: Report & {proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}}, ready: () => void = () => {}): Report & {proof?: StepProof, uncovered?: string[]} {
  if (!base.proof) return {proven: false, nodes: base.nodes, leaves: base.leaves, checked: false}
  const t0 = performance.now()
  const plain = plainOf(m)
  // Each step law its own instances, from its own goal: the keys the step and the laws read, and its own (a k-step
  // law's later frames read keys no other step law has); where positions shift or a law is about several keys, the
  // keys its goal reads a map at too. A frame's hypotheses read no name the run introduces later (kernel.ts's
  // stepZone), so a k-step law drops the keys that read one; but a flag that holds at every key holds at a later step's
  // key too: where these instances don't prove it, each flag at its own witness at every step is tried (keptAcross).
  const perStep: Record<string, Instances> = {}, at = stepLawInstances(m, laws)
  for (const sl of stepLaws) perStep[sl.name] = at(sl)
  const instances = perStep[stepLaws[0]?.name ?? ''] ?? {}
  const trees: Record<string, Tree> = {}
  let nodes = base.nodes, leaves = base.leaves
  // (each step law's own time, its share of the usual proof: what its certificate alone may take, stepCertFloor)
  const ownMs: Record<string, number> = {}
  for (const sl of stepLaws) for (const goal of stepLawObligations(m, laws, perStep[sl.name] ?? instances, sl)) {
    const g0 = performance.now()
    const full = perStep[sl.name] ?? instances, few = triggered(plain, laws, full, inst => stepLawObligations(m, laws, inst, sl), [sl.forall, ...(sl.keys ?? [])].flatMap(k => (k ? [k] : [])))
    let out = sameInstances(few, full) ? grow(goal) : grow(stepLawObligations(m, laws, few, sl).find(g => g.name === goal.name) ?? goal)
    if ('tree' in out && !sameInstances(few, full)) perStep[sl.name] = few
    else if (!sameInstances(few, full)) out = grow(goal)
    // A k-step law that reads a condition kept across its steps: each flag at its own witnesses, at every step.
    if (!('tree' in out)) for (const kept of keptAcross(plain, laws, perStep[sl.name] ?? instances, ownKeys(plain, sl), sl.steps ?? 1)) {
      const again = grow(stepLawObligations(m, laws, kept, sl)[0]!)
      if ('tree' in again) { out = again; perStep[sl.name] = kept; break }
    }
    if (!('tree' in out)) return stuckAt(goal, out, nodes, leaves)
    if (minimal.on) {
      const had = perStep[sl.name] ?? instances, built = stepLawObligations(m, laws, had, sl).find(g => g.name === goal.name)
      if (built) {
        const focus = [sl.forall, ...(sl.keys ?? [])].flatMap(k => (k ? [k] : [])), thin = usedInstances(plain, built, had, usedHyps(built, out.tree), focus)
        const g2 = sameInstances(thin, had) ? undefined : stepLawObligations(m, laws, thin, sl).find(g => g.name === goal.name)
        const again = g2 && grow(g2)
        if (again && 'tree' in again) { out = again; perStep[sl.name] = thin }
      }
    }
    trees[goal.name] = out.tree
    nodes += out.nodes
    leaves += countLeaves(out.tree)
    ownMs[sl.name] = (ownMs[sl.name] ?? 0) + performance.now() - g0
  }
  // (every step law proven: the laws' certificate, or their check, as proveLaws makes it; its time not the step laws')
  const r0 = performance.now()
  ready()
  const usual0 = t0 + performance.now() - r0
  const proof = {laws: base.proof, instances, ...(Object.keys(perStep).length ? {perStep} : {}), trees}
  // Step laws of a machine the cyclic instances cover (one step, or several over no map) are translated with the laws
  // (core/cyclic.ts); the rest are counted as no instance's.
  // (a machine with a history: its plain machine's; a flag at every key through its sk machine; k-step laws over a map
  // searched, where GDP_CERT_SEARCH=1; where no cyclic proof is made the usual trees, checked above, stay the certificate)
  const modes = cyclicOn() || certOn(), why = modes ? (sumsWhy(m) ?? uncoveredWhy(plain, laws)) : undefined, one = stepLaws
  // Where the cyclic certificate is made below (GDP_CERT, not the cross-check; the laws' certificate checked), the usual
  // trees are its input, as a machine's laws' are: checkStepLaws (the laws' usual trees again, then the step laws') runs
  // only where no certificate is made.
  const byCert = certOn() && !cyclicOn() && !why && one.length > 0 && base.checked
  // (`uncovered`: why each step law left on the usual rule is, where the certificate is on: none, every step law has its
  // cyclic certificate; proveLiveness reads it)
  const left: string[] = [], miss = (sl: StepLaw, why: string) => { uncovered((sl.steps ?? 1) > 1 ? 'k-step law' : 'step law', m.name, why); left.push(why) }
  const out = {proven: true, nodes, leaves, checked: byCert || checkStepLaws(m, laws, stepLaws, proof), proof, ...(certOn() ? {uncovered: left} : {})}
  if (!modes) return out
  if (!why && one.length && out.checked) {
    const all = one.map(sl => { const inst = perStep[sl.name] ?? instances, goal = stepLawObligations(m, laws, inst, sl)[0]!; return {sl, inst, goal, tree: trees[goal.name]!} })
    const translatedOf = (steps: typeof all) => (st: TStats) => translatedProof(() => JSON.stringify(['steps', plain, laws, base.proof!.instances, steps.map(x => [x.sl, x.inst])]), reused => timedKind('instance', 0, () => machineNodes(plain, laws, base.proof!.instances, {trees: base.proof!.trees, steps, lawsMade: reused}, st)), st,
      () => JSON.stringify(['machine', plain, laws, base.proof!.instances]))
    const usualMs = performance.now() - usual0
    if (cyclicOn()) crossCyclic('step law', m.name, true, undefined, usualMs, translatedOf(all))
    // (where the step laws' proof together isn't made, each step law's alone: one the translation misses leaves the
    // others theirs; and the usual trees, unchecked where the certificate was to be the verdict, are checked)
    // (a certificate's translation is worth at most a few times the usual proof, which is an equally checked
    // certificate: the step laws together within translateMs of their usual time, then each alone within its share,
    // all of them within translateMs again; past that a step law's certificate is its usual trees)
    const floor = stepCertFloor(), owned = Object.values(ownMs).reduce((a, b) => a + b, 0)
    const together = certOn() ? certCyclic('step law', m.name, translatedOf(all), undefined, usualMs, floor) : undefined
    if (together && !together.checked) {
      if (byCert) out.checked = checkStepLaws(m, laws, stepLaws, proof)
      const end = clock() + translateMs(usualMs, floor)
      for (const x of all) {
        const share = owned > 0 ? usualMs * (ownMs[x.sl.name] ?? 0) / owned : usualMs / all.length
        const c = all.length === 1 ? together : clock() < end ? withDeadline(end, () => certCyclic('step law', m.name, translatedOf([x]), undefined, share, floor))
          : {checked: false, why: `the step laws' certificates past ${Math.round(translateMs(usualMs, floor))} ms (their usual trees)`}
        if (!c.checked) miss(x.sl, c.why)
      }
    }
  }
  // (the rest: k steps over a map a request carries, or a machine no instance covers)
  const rest = stepLaws.filter(sl => why || !one.includes(sl)), restWhy = (sl: StepLaw) => why ?? `${sl.steps} steps over a map a request carries`
  if (certOn() && certSearch() && out.checked && rest.length && !why) {
    // The rest searched: the laws' nodes (searched), each step law's node (core/cyclic.ts's stepLawNodes).
    const searchedSteps = () => {
      const b = machineNodes(plain, laws, base.proof!.instances)
      return proveCyclic(b.facts, [...b.specs, ...searchedStepNodes(plain, laws, rest.map(sl => ({law: sl, instances: perStep[sl.name] ?? instances})), b.facts, b.specs)])
    }
    const c = certCyclic('step law', m.name, undefined, searchedSteps, performance.now() - usual0)
    for (const sl of c.checked ? [] : rest) miss(sl, `${restWhy(sl)}: ${c.why}`)
  } else if (cyclicOn() || certOn()) for (const sl of rest) miss(sl, restWhy(sl))
  return out
}
// Progress (kernel.ts's progressObligations): the laws proven first, then each goal, the every-key laws assumed at every
// key the goals read a map at.
export function proveProgress(m: Machine, laws: Law[], p: {name: string, when: C, then: C, request: Record<string, E>}): Report & {instances?: Instances, trees?: Record<string, Tree>, uncovered?: string} {
  const t0 = performance.now(), base = proveLaws(m, laws)
  if (!base.proven || !base.checked) return {proven: false, nodes: base.nodes, leaves: base.leaves, ...(base.failed ? {failed: base.failed} : {}), checked: false}
  const ls = base.laws ?? laws
  const instances = instancesFor(plainOf(m), ls, inst => progressObligations(m, ls, inst, p))
  const trees: Record<string, Tree> = {}
  let nodes = base.nodes, leaves = base.leaves
  for (const goal of progressObligations(m, ls, instances, p)) {
    const out = grow(goal)
    if (!('tree' in out)) return stuckAt(goal, out, nodes, leaves)
    trees[goal.name] = out.tree
    nodes += out.nodes
    leaves += countLeaves(out.tree)
  }
  const checked = progressObligations(m, ls, instances, p).every(g => check(g, trees[g.name]!))
  // (a request allowed whose claim is that alone, over a machine without a history or carried maps: the laws' nodes,
  // then the allowed goal translated, core/cyclic.ts's allowTranslated, its last node BridgeRules.lean's cycAOk: from
  // every reachable state, every request meeting the region and its terms is allowed; where GDP_CERT_SEARCH=1 and that
  // isn't proven, allowNode searched with the witnesses withWitness finds)
  const alone = JSON.stringify(p.then) === JSON.stringify(trueC) && !m.history && !sumsWhy(m) && !m.inputMaps?.length && m.assume !== undefined
  if (certOn() && alone && checked && base.proof) {
    const lp = base.proof, q = hasQuantified(m), goal = progressObligations(m, ls, instances, p)[0]!
    const translated = (st: TStats) => translatedProof(() => JSON.stringify(['allowed', m, ls, lp.instances, instances, p]), reused => {
      const b = machineNodes(m, ls, lp.instances, {...lp, lawsMade: reused}, st)
      if (b.why) return b
      const a = allowTranslated(m, ls, instances, p, {goal, tree: trees[goal.name]!}, b.facts, b.specs, `${m.name}: allowed`, st)
      return a.why ? {facts: b.facts, specs: [], why: a.why} : {facts: b.facts, specs: [...b.specs, ...a.specs]}
    }, st, () => JSON.stringify(['machine', m, ls, lp.instances]))
    const allowed = (): CyclicVerdict => {
      const b = machineNodes(m, ls, lp.instances, lp)
      if (b.why || (b.specs[0]?.rank.length ?? 2) < 2) return {proven: false, checked: false, node: m.name, goal: 'allowed', stuck: b.why ?? 'laws ranked by time alone'}
      let last: CyclicVerdict = {proven: false, checked: false, node: m.name, goal: 'allowed', stuck: 'no witness'}
      const found = withWitness(m, p.request, wit => {
        const w: C = {op: 'and', xs: [p.when, reqTS(Object.entries(p.request)), reqTS(wit)]}
        const spec = allowNode(skMachine(m), ls, instances, w, b.facts, b.specs, `${m.name}: allowed`,
          q ? closingInsts(m, b.facts, [instances, ...Object.values(lp.instances)], [{op: 'var', name: 't$'}], ls) : [])
        last = proveCyclic(b.facts, [...b.specs, spec])
        return last.proven && last.checked ? last : undefined
      })
      return found?.out ?? last
    }
    const c = certCyclic('progress', m.name, translated, certSearch() ? allowed : undefined, performance.now() - t0)
    if (!c.checked) { const why = `a request allowed: ${c.why}`; uncovered('progress', m.name, why); return {proven: true, nodes, leaves, checked, instances, trees, uncovered: why} }
  } else if (cyclicOn() || certOn()) {
    const why = alone ? 'a request allowed' : 'a request allowed and a claim after it'
    uncovered('progress', m.name, why)
    if (certOn()) return {proven: true, nodes, leaves, checked, instances, trees, uncovered: why}
  }
  return {proven: true, nodes, leaves, checked, instances, trees}
}
// Liveness (kernel.ts's livenessParts): its step laws, proven together. The claim needs no more (a run takes the
// request, so it is allowed); but a request never allowed would leave the claim about no run, so where a helpful request
// names every input a client sends and carries no maps, it is proven allowed in its region too.
// The certificate is its parts': the step laws' cyclic proof (translated, as any machine's step laws), and each helpful
// request's allowed node. The claim about runs that never end is no certificate's, under either: the rank that can't
// drop forever, the region that stays once it stops and the request that comes there are Live.lean's `leads_of_lex`,
// read from the step laws' meaning (BridgeRules.lean's `sleads_of_holds`, of a cyclic proof's step laws through
// `cyc_kstep_sound`) as from their usual trees (Live.lean's `sleads_sound`): one claim, its statement the same. So a
// liveness is covered exactly where every part has its cyclic certificate (`cyclic: {kind: 'liveness', ...}`), and
// uncovered, with the part's why, where one is on the usual rule.
// (`uncovered`, where the certificate is on: why each part is on the usual rule; none, the liveness is covered)
// Under strong fairness, where no levels are given: each helpful request's goal tried handing over to no region and to
// each other one alone (levels 0 but its own and that one's), then levels from the hand-overs that end at a request
// reaching `to` or lowering the rank (each level above the one it hands over from: no cycle). Undefined where none.
export function chooseLevels(m: Machine, laws: Law[], l: Liveness): number[] | undefined {
  // (help i at level 0 hands over to j alone at level 1, or to none: every level 0)
  const n = livenessHelpful(l).length, at = (j?: number) => Array.from({length: n}, (_, x) => (x === j ? 1 : 0))
  const proves = (i: number, j?: number) => { const r = proveStepLaws(m, laws, [livenessParts(m, {...l, levels: at(j)}).helps[i]!]); return r.proven && r.checked }
  const dist: (number | undefined)[] = Array.from({length: n}, (_, i) => (proves(i) ? 0 : undefined))
  if (dist.every(d => d === 0)) return dist.map(() => 0)
  const edges = Array.from({length: n}, (_, i) => (dist[i] === 0 ? [] : Array.from({length: n}, (_, j) => j).filter(j => j !== i && proves(i, j))))
  for (let round = 0; round < n; round++) for (let i = 0; i < n; i++) if (dist[i] === undefined) {
    const ds = edges[i]!.flatMap(j => (dist[j] === undefined ? [] : [dist[j]!]))
    if (ds.length) dist[i] = Math.min(...ds) + 1
  }
  if (dist.some(d => d === undefined)) return undefined
  const top = Math.max(...(dist as number[]))
  return (dist as number[]).map(d => top - d)
}
export function proveLiveness(m: Machine, laws: Law[], given: Liveness): Report & {steps?: ReturnType<typeof proveStepLaws>, uncovered?: string[], levels?: number[]} {
  // (strong fairness: the levels the helpful requests hand over by, where they aren't given)
  const lv = strongly(given) && !given.levels && livenessHelpful(given).length > 1 ? chooseLevels(m, laws, given) : undefined
  const l: Liveness = lv ? {...given, levels: lv} : given
  const {stay, cover, helps} = livenessParts(m, l)
  const a = proveStepLaws(m, laws, [stay, cover, ...helps])
  if (!a.proven || !a.checked) return {proven: false, nodes: a.nodes, leaves: a.leaves, ...(a.failed ? {failed: a.failed} : {}), checked: false}
  const plain = plainOf(m)
  let nodes = a.nodes, leaves = a.leaves
  const left = [...(a.uncovered ?? []).map(why => `a step law: ${why}`)]
  for (const [i, h] of livenessHelpful(l).entries()) {
    // (a machine with sums: allowed by the rule's own assumption, its plain machine's facts given; Sums.lean)
    const own = sumsWhy(m) ? m.assume : plain.assume
    // Under strong fairness the claim reads each helpful request allowed in its region (Live.lean's sleads_sf_soundA):
    // proven always, the inputs it leaves free given witness terms.
    if (strongly(l)) {
      if (m.history || plain.inputMaps?.length) return {proven: false, nodes, leaves, failed: {goal: `${l.name}: helpful request ${i + 1} is allowed`, stuck: 'a history or carried maps: no request allowed shown under strong fairness'}, checked: false}
      if (!own) continue
      const w = withWitness(plain, h.request, wit => {
        if (!plain.inputs.every(inp => inp in h.request || wit.some(([x2]) => x2 === inp))) return undefined
        const b = proveProgress(sumsWhy(m) ? m : plain, laws, {name: `${l.name}: helpful request ${i + 1} is allowed`, when: {op: 'and', xs: [l.from, {op: 'not', x: l.to}, h.when]}, then: trueC, request: {...h.request, ...Object.fromEntries(wit)}})
        return b.proven && b.checked ? b : undefined
      })
      if (!w) return {proven: false, nodes, leaves, failed: {goal: `${l.name}: helpful request ${i + 1} is allowed`, stuck: 'no request with its terms the assumption allows'}, checked: false}
      nodes += w.out.nodes; leaves += w.out.leaves
      if (w.out.uncovered) left.push(`helpful request ${i + 1} allowed: ${w.out.uncovered}`)
      continue
    }
    if (m.history || plain.inputMaps?.length || !own || !plain.inputs.every(inp => inp in h.request)) continue
    const b = proveProgress(sumsWhy(m) ? m : plain, laws, {name: `${l.name}: helpful request ${i + 1} is allowed`, when: {op: 'and', xs: [l.from, {op: 'not', x: l.to}, h.when]}, then: trueC, request: h.request})
    nodes += b.nodes; leaves += b.leaves
    if (!b.proven || !b.checked) return {proven: false, nodes, leaves, ...(b.failed ? {failed: b.failed} : {}), checked: false}
    if (b.uncovered) left.push(`helpful request ${i + 1} allowed: ${b.uncovered}`)
  }
  if (certOn()) {
    if (left.length) uncovered('liveness', m.name, left.join('; '))
    else cycLog({kind: 'liveness', name: m.name, cert: true, usual: true, cyclic: true, route: 'its step laws', parts: 2 + helps.length})
  } else if (cyclicOn()) uncovered('liveness', m.name, 'a claim about runs that never end')
  return {proven: true, checked: true, nodes, leaves, steps: a, ...(certOn() ? {uncovered: left} : {}), ...(lv ? {levels: lv} : {})}
}

// A loop's halting (kernel.ts's loopObligations: its machine's laws, and its liveness's step laws, `while` failing later
// from anywhere, every request helpful), its usual trees given: translated to one cyclic proof as proveStepLaws
// translates a machine's step laws (core/cyclic.ts's machineNodes, the laws' nodes and the step laws' after them), the
// proof Lean reads (lean-kernel/emit.ts's cycMachineToLean: Live.lean's loop_halts_of from BridgeRules.lean's
// sleads_of_holds). The claim is the usual one: loop_halts_of reads the liveness's meaning, from either certificate.
// Undefined where the cyclic certificate is off (GDP_CERT=usual; with GDP_CYCLIC=1 the cross-check runs); else checked,
// the proof, and why not.
export function certLoop(l: Loop, laws: Law[], rank: E | E[], trees: Record<string, Tree>, usualMs?: number): {checked: boolean, proof?: Cyclic, why: string} | undefined {
  if (!certOn() && !cyclicOn()) return undefined
  // (a proof made from the same loop, laws and rank before is that proof: it proves the same claim)
  const translated = (st: TStats) => translatedProof(() => JSON.stringify(['loop', loopMachine(l), laws, rank]), () => timedKind('instance', 0, () => loopNodes(l, laws, rank, trees, st)), st)
  if (!certOn()) { crossCyclic('loop', l.name, true, undefined, usualMs, translated); return undefined }
  const c = certCyclic('loop', l.name, translated, undefined, usualMs)
  if (!c.checked) uncovered('loop', l.name, c.why)
  return c
}

// The key terms a condition reads maps at; a primed map's key is a key of the map before the step too.
function readKeysC(c: C): E[] {
  const out: E[] = []
  const inE = (e: E): void => { if (e.op === 'get') (out.push(...tupleParts(e.key)), inE(e.key)); else if (e.op === 'if') (inC(e.c), inE(e.then), inE(e.else)); else if (e.op === 'mul' || e.op === 'proj') inE(e.a); else if ('b' in e) (inE(e.a), inE(e.b)) }
  const inC = (x: C): void => (x.op === 'flag' || x.op === 'all' ? undefined : x.op === 'not' ? inC(x.x) : x.op === 'and' || x.op === 'or' ? x.xs.forEach(inC) : (inE(x.a), inE(x.b)))
  inC(c)
  return out
}

export const countLeaves = (t: Tree): number => ('leaf' in t ? 1 : countLeaves(t.yes) + countLeaves(t.no))

// A real counterexample for a goal the prover couldn't close (with products, its witness may be abstract): the free
// variables over 0..bound, every hypothesis evaluated with true arithmetic. Goals that read maps are left to the
// machine searches (research/search/), which run whole histories.
export function concretize(goal: Goal, bound = 12): Record<string, number> | undefined {
  const names = new Set<string>()
  let reads = false
  const walkE = (e: E): void => { if (e.op === 'var') names.add(e.name); else if (e.op === 'get') reads = true; else if (e.op === 'if') (walkC(e.c), walkE(e.then), walkE(e.else)); else if ('a' in e) (walkE(e.a), 'b' in e && walkE(e.b)) }
  const walkC = (c: C): void => (c.op === 'flag' ? undefined : c.op === 'all' ? void (reads = true) : c.op === 'not' ? walkC(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.forEach(walkC) : (walkE(c.a), walkE(c.b)))
  goal.hyps.forEach(walkC)
  if (reads || names.size > 4) return undefined
  const ev = (e: E, env: Record<string, number>): number => {
    switch (e.op) {
      case 'var': return env[e.name]!
      case 'const': return e.value
      case 'add': return ev(e.a, env) + ev(e.b, env)
      case 'sub': return Math.max(0, ev(e.a, env) - ev(e.b, env))
      case 'min': return Math.min(ev(e.a, env), ev(e.b, env))
      case 'max': return Math.max(ev(e.a, env), ev(e.b, env))
      case 'mul': return e.k * ev(e.a, env)
      case 'prod': return ev(e.a, env) * ev(e.b, env)
      case 'if': return holds(e.c, env) ? ev(e.then, env) : ev(e.else, env)
      case 'get': case 'tup': case 'proj': return NaN
    }
  }
  const holds = (c: C, env: Record<string, number>): boolean => c.op === 'not' ? !holds(c.x, env) : c.op === 'and' ? c.xs.every(y => holds(y, env)) : c.op === 'or' ? c.xs.some(y => holds(y, env))
    : c.op === 'flag' || c.op === 'all' ? false : c.op === '<' ? ev(c.a, env) < ev(c.b, env) : c.op === '<=' ? ev(c.a, env) <= ev(c.b, env) : ev(c.a, env) === ev(c.b, env)
  const vars = [...names]
  const total = (bound + 1) ** vars.length
  for (let i = 0; i < total; i++) {
    let rest = i
    const env = Object.fromEntries(vars.map(v => { const d = rest % (bound + 1); rest = Math.floor(rest / (bound + 1)); return [v, d] }))
    if (goal.hyps.every(h => holds(h, env))) return env
  }
  return undefined
}

// The facts a goal needs, as hypotheses: each fact about every key at the keys the goal reads a function at (and at
// the keys those facts read, a second round), each plain fact as it is.
export function factsFor(m: Machine, goal: Goal): C[] {
  return assumed(m.facts ?? [], instancesFor(m, [], inst => [{...goal, hyps: [...assumed(m.facts ?? [], inst), ...goal.hyps]}]))
}

// A goal built from its instances (an exporter's goal, shaped as its Lean twin builds it): the every-key laws, the
// quantified flags and the facts assumed at every key it reads a map or function at, then a tree, checked.
export function proveBuilt(m: Machine, laws: Law[], build: (inst: Instances) => Goal): {proven: boolean, instances?: Instances, goal?: Goal, tree?: Tree} {
  const instances = instancesFor(m, laws, inst => [build(inst)])
  const goal = build(instances), out = grow(goal)
  if (!('tree' in out) || !check(goal, out.tree)) return {proven: false}
  return {proven: true, instances, goal, tree: out.tree}
}
