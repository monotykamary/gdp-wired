// A copy of kernel/prove.ts's tree search (its lines 1-703: grow, growRoot, growPlain, lift, withCuts, growFocused,
// bisect, fractional), unchanged but for its imports and a recorder: with `rec.on`, every leaf the search finds (each
// refuted case, whether it ends in the tree or is thrown away by a lift or a failed sibling) is kept with its path and
// derivation, and each phase of growRoot timed. research/dag/profile.ts reads them. Nothing here is trusted.
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
import type {C, E} from '../../core/machine.ts'
import {type Lin, type Step, add, k, refuteFast, scale, solve, sub, v, work} from '../../core/solver.ts'
import {checkRefutation} from '../../core/check.ts'
import {type Goal, type Path, type Tree, atomOf, canon, canonFlip, columnTerm, decided, factorsOf, isCell, isMonomial, leafConstraints, leafConstraintsReusing, linear, reusing, type Seen, truth, unreachable, withProducts} from '../../kernel/kernel.ts'

// The recorder (research/dag/profile.ts): each leaf found, its path's decisions in order and its derivation over
// leafConstraints(goal, path) (with its products and squares); and the time each phase of growRoot took.
export type LeafRec = {path: [string, Lin, boolean][], steps: Step[], products?: [number, number][], squares?: Lin[], at: number}
export const rec: {on: boolean, leaves: LeafRec[], phases: Record<string, number>, t0: number} = {on: false, leaves: [], phases: {}, t0: 0}
const note = (path: Path, steps: Step[], products?: [number, number][], squares?: Lin[]) => { if (rec.on) rec.leaves.push({path: [...path].map(([key, a]) => [key, a.lin, a.holds]), steps, ...(products?.length ? {products} : {}), ...(squares?.length ? {squares} : {}), at: performance.now() - rec.t0}) }
const phase = <T>(name: string, f: () => T): T => { if (!rec.on) return f(); const t = performance.now(); try { return f() } finally { rec.phases[name] = (rec.phases[name] ?? 0) + performance.now() - t } }

// The atoms the path leaves open, in evaluation order: deciding any of them makes progress.
function openE(e: E, path: Path, out: Lin[]): void {
  switch (e.op) {
    case 'var': case 'const': return
    case 'mul': return openE(e.a, path, out)
    case 'prod': return (openE(e.a, path, out), openE(e.b, path, out))
    case 'get': return openE(e.key, path, out)
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
  const before = out.length
  openE(c.a, path, out), openE(c.b, path, out)
  if (out.length === before && !positive && c.op === '=' && truth(c, path) === undefined) openC(c, path, out)
}

// Pairs of reads of one map whose keys the path doesn't yet compare. With `pairedKeys.skip` (core/data.ts), reads at
// keys a pairing builds ((a + b)² + b, keys whose difference has monomials) are left uncompared: that encoding states
// their congruence as facts, and comparing their keys only brings products into leaves its linear rows decide.
export const pairedKeys = {skip: false}
function openCells(rows: {lin: Lin}[], path: Path): Lin[] {
  const names = [...new Set(rows.flatMap(r => Object.keys(r.lin)))].filter(isCell)
  const out: Lin[] = []
  const keyText = (n: string) => n.slice(n.indexOf('[') + 1, -1)
  for (const [i, p] of names.entries()) for (const q of names.slice(i + 1)) {
    if (p.slice(0, p.indexOf('[')) !== q.slice(0, q.indexOf('['))) continue
    const d = sub(parse(keyText(p)), parse(keyText(q)))
    if (pairedKeys.skip && Object.keys(d).some(isMonomial)) continue
    const dec = (lin: Lin) => path.get(canon(lin))?.holds ?? (path.has(canonFlip(lin)) ? !path.get(canonFlip(lin))!.holds : undefined)
    // Two cells of a run's map (core/cyclic.ts: time u and key k at u + k·Ω) at keys k·Ω and k'·Ω: k = k' first, a
    // linear atom; the keys' own difference only where k = k' (its other side then refuted by (k − k')·Ω = 0, a product).
    const q0 = cellProducts.on ? quotient(d) : undefined
    if (q0) {
      const qa = dec(q0), qb = dec(scale(q0, -1))
      if (qa === undefined) { out.push(q0); continue }
      if (qa === true && qb === undefined) { out.push(scale(q0, -1)); continue }
      if (!(qa && qb)) continue
      cellDiffs.set(canon(d), q0); cellDiffs.set(canon(scale(d, -1)), scale(q0, -1))
    }
    const a = dec(d), b = dec(scale(d, -1))
    if (a === undefined) out.push(d)
    else if (a === true && b === undefined) out.push(scale(d, -1))
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
function parse(text: string): Lin {
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
const proveTrace = !!(globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env?.PROVE_TRACE
// `why`, when the budget ran out: which limit, at what size, and what usually helps.
// Set while core/cyclic.ts grows its goals.
export const cellProducts = {on: false}
export type Outcome = {tree: Tree, nodes: number} | {stuck: 'sat' | 'unknown', witness?: Record<string, number>, path: Path, why?: string}

// The budget: 200,000 nodes and, by default, a second per hypothesis (at least 20 seconds) per goal; past either the goal
// is left `unknown`. A goal with many instances (a law about two keys at its pairs) has that many more rows per leaf.
// A deadline every goal grown inside `withDeadline` keeps, beside its own budget: a search that proves many things (core/
// infer.ts, core/discover.ts, the search proveRule falls back on) bounds them all; a goal past it is left `unknown`.
let deadline = Infinity
// The clock every budget here reads (grow's `until`, withDeadline's; core/cyclic.ts's and core/data.ts's searches): wall
// time, or within `counted` the work the prover has done (the solver's rows read and made, each node's rows), `perMs`
// units a millisecond, so that what a search's budget lets it try, and so its verdict, doesn't depend on the machine's
// speed. A counted search inside another reads the outer's clock.
let rate = 0
export const clock = (): number => (rate ? work.n / rate : performance.now())
export function counted<T>(perMs: number, f: () => T): T {
  if (rate) return f()
  const outer = deadline
  rate = perMs; deadline = Infinity
  try { return f() } finally { rate = 0; deadline = outer }
}
// A budget's end, within the deadline (a translation's own bound, core/cyclic.ts's, kept by the export's GDP_CERT_MS).
export const withinDeadline = (until: number): number => Math.min(until, deadline)
export function withDeadline<T>(until: number, f: () => T): T {
  const outer = deadline
  deadline = Math.min(outer, until)
  try { return f() } finally { deadline = outer }
}
// `units: false`: the goal's own order, no units first (a caller after a model, not a proof: a run guided by the
// prover's witnesses, say, whose models units would steer).
export function grow(goal: Goal, path: Path = new Map(), budget: {nodes: number, until?: number, units?: boolean} = {nodes: 0, until: clock() + Math.max(20_000, 1_000 * goal.hyps.length)}): Outcome {
  if (deadline < (budget.until ?? Infinity)) budget.until = deadline
  if (budget.units === false && unitsNow) { unitsNow = false; try { return grow(goal, path, budget) } finally { unitsNow = true } }
  if (proveDump && !path.size && !budget.nodes) { proveDump(goal); }
  if (proveTrace && !path.size && !budget.nodes) {
    const t = performance.now(), out = growRoot(goal, path, budget)
    console.error(`[grow] ${goal.name}: ${goal.hyps.length} hyps, ${budget.nodes} nodes, ${Math.round(performance.now() - t)} ms, ${'tree' in out ? 'proven' : `${out.stuck}${out.why ? ` (${out.why})` : ''}`}`)
    return out
  }
  if (!profile.on || path.size || budget.nodes) return growRoot(goal, path, budget)
  const t = performance.now(), s0 = profile.solves, m0 = profile.solveMs, r0 = profile.rowsMs, n0 = profile.nodes
  const out = growRoot(goal, path, budget)
  profile.goals.push({name: goal.name, ms: performance.now() - t, nodes: profile.nodes - n0, solves: profile.solves - s0, solveMs: profile.solveMs - m0, rowsMs: profile.rowsMs - r0, proven: 'tree' in out})
  return out
}
function growRoot(goal: Goal, path: Path, budget: {nodes: number, until?: number}): Outcome {
  // At the root: plainly first; where the cases multiply past a budget, through cuts. The plain budget halves with each
  // two open choices (what a plain search's cases grow by), so a long run's steps reach the cuts early.
  if (path.size === 0 && budget.nodes === 0 && unitFirst && unitsNow) {
    // A goal that a few cases settle needs no units (finding them costs a Farkas check per atom); the rest get them.
    unitsNow = false
    try {
      const quick = phase('quick (cap 64, no units)', () => growPlain(goal, path, {nodes: 0, until: budget.until, cap: 64}))
      if ('tree' in quick || quick.stuck === 'sat' || quick.why === undefined) return quick
    } finally { unitsNow = true }
  }
  if (path.size === 0 && budget.nodes === 0) {
    const open = new Set(leafConstraints(goal, path).flatMap(r => Object.keys(r.lin)).filter(n => n.startsWith('⟦') && columnTerm(n)?.op === 'if')).size
    const plain = phase('plain (capped)', () => growPlain(goal, path, {nodes: 0, until: budget.until, cap: Math.max(32, Math.round(4_000 / 2 ** (open / 2)))}))
    if ('tree' in plain || plain.stuck === 'sat' || plain.why === undefined) return plain
    const cut = phase('cuts', () => withCuts(goal, path, budget))
    if (cut) return cut
  }
  return phase('plain (uncapped)', () => growPlain(goal, path, budget))
}
function growPlain(goal: Goal, path: Path, budget: {nodes: number, until?: number, cap?: number}): Outcome {
  if (budget.cap !== undefined && budget.nodes >= budget.cap) return {stuck: 'unknown', path, why: 'cap'}
  if (profile.on) profile.nodes++
  if (++budget.nodes > 200_000 || (budget.until !== undefined && clock() > budget.until)) return {stuck: 'unknown', path, why: outOfBudget(goal, budget.nodes > 200_000 ? 'nodes' : 'time', path.size)}
  // Rows that read a term column only once a cut has put one on the path; before, the rows a choice-free search uses
  // (what it saw before term columns), renumbered to the whole leaf's when a leaf is found.
  const full = timed(() => rowsAt(goal, path), ms => { profile.rowsMs += ms })
  work.n += 1 + full.length
  const columns = [...path.values()].some(a => Object.keys(a.lin).some(key => key.startsWith('⟦')))
  const idx = full.flatMap((r, i) => (columns || !Object.keys(r.lin).some(key => key.startsWith('⟦')) ? [i] : []))
  const rows = idx.map(i => full[i]!), at = (i: number) => (i < rows.length ? idx[i]! : full.length + i - rows.length)
  const leafOf = (steps0: Step[], products0?: [number, number][], squares0?: Lin[]): Tree => {
    const {steps, products, squares} = products0 || squares0 ? trimmed(rows.length, steps0, products0 ?? [], squares0 ?? []) : {steps: steps0, products: undefined, squares: undefined}
    const out: Tree = {leaf: steps.map(st => (st.kind === 'input' ? {...st, index: at(st.index)} : st)), ...(products?.length ? {products: products.map(([i, j]) => [at(i), at(j)] as [number, number])} : {}), ...(squares?.length ? {squares} : {})}
    if ('leaf' in out) note(path, out.leaf, out.products, out.squares)
    return out
  }
  // The conclusion's own atoms first (the goal's last hypothesis is the law refuted): a case it doesn't read is often
  // one no refutation needs, and splitting it first multiplies every case after it.
  const open: Lin[] = []
  const hyps = goal.hyps, last = hyps.length - 1
  let byHyp = openSeen.get(goal)
  if (!byHyp) openSeen.set(goal, (byHyp = new Map()))
  const openOf = (h: C) => { let seen = byHyp.get(h); if (!seen) byHyp.set(h, (seen = {})); return reusing(seen, path, p => { const out: Lin[] = []; openH(h, p, out); return out }) }
  // Then the hypotheses about only the names the conclusion reads (an assumption about another key, a witness, can
  // wait: a refutation seldom needs it), then the rest, each group in the goal's order.
  if (unitFirst && unitsNow) open.push(...unitsOf(goal))
  if (last >= 0) open.push(...openOf(hyps[last]!))
  const near = nearOf(goal)
  for (const [i, h] of hyps.entries()) if (i !== last && near[i]) open.push(...openOf(h))
  for (const [i, h] of hyps.entries()) if (i !== last && !near[i]) open.push(...openOf(h))
  open.push(...openCells(rows, path))
  const next = open.find(lin => Object.keys(lin).some(key => key !== '1') && !path.has(canon(lin)) && !path.has(canonFlip(lin)))
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
  // Before a split, the rows the plain search sets aside (those reading a term column) by their Farkas rows: an open
  // choice's bounds (min(a, c) ≤ c) often refute the case whichever way the choice goes, so its cases need no split.
  if (next && !columns && full.length > rows.length) {
    const fast = timed(() => refuteFast(full), ms => { profile.solves++; profile.solveMs += ms })
    if (fast?.kind === 'refuted') { note(path, fast.steps); return {tree: {leaf: fast.steps}, nodes: budget.nodes} }
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
function rowsAt(goal: Goal, path: Path): ReturnType<typeof leafConstraintsReusing> {
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

// A tree for a weaker goal (some hypotheses left out, some conjuncts of one left out) made a tree for the whole: at any
// path a leaf's rows are among the whole goal's (each hypothesis' facts are a hypothesis' own, the cells, terms and
// naturals they read a subset), so each input is renumbered to the same row there, a square or product past the rows
// moved by the difference. Where a dropped conjunct makes the whole hypothesis false under the path, its row 1 <= 0
// refutes the leaf alone; a leaf neither maps is grown again on the whole goal.
// `opaque`: variables the weaker goal has for terms of the whole (a step's value, read the same in two hypotheses), each
// read as the term's linear form at the whole goal's path; a split the whole's path already decides is followed, not
// made again.
export function widen(part: Goal, whole: Goal, tree: Tree, opaque: Record<string, E> = {}, pp: Path = new Map(), wp: Path = pp): Tree | undefined {
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
  const rp = rowsAt(part, pp), rw = rowsAt(whole, wp), at = new Map<string, number>()
  rw.forEach((r, i) => { const key = canon(r.lin); if (!at.has(key)) at.set(key, i) })
  const map = (i: number) => { if (i >= rp.length) return i - rp.length + rw.length; const l = rename(rp[i]!.lin); return l && at.get(canon(l)) }
  const leaf: Step[] = [], products: [number, number][] = [], squares = (tree.squares ?? []).map(rename)
  let ok = squares.every(Boolean)
  for (const st of ok ? tree.leaf : []) { if (st.kind !== 'input') { leaf.push(st); continue } const j = map(st.index); if (j === undefined) { ok = false; break } leaf.push({...st, index: j}) }
  for (const [i, j] of ok ? tree.products ?? [] : []) { const pi = map(i), pj = map(j); if (pi === undefined || pj === undefined) { ok = false; break } products.push([pi, pj]) }
  // (renamed, a derivation through products or cuts is replayed: a cut's divisor may not divide the terms' coefficients)
  if (ok && names.length && !checkRefutation(withProducts(rw, products, squares as Lin[]), leaf)) ok = false
  if (ok) return {leaf, ...(tree.products ? {products} : {}), ...(tree.squares ? {squares: squares as Lin[]} : {})}
  const absurd = rw.findIndex(r => Object.keys(r.lin).every(key => key === '1') && (r.lin['1'] ?? 0) > 0)
  if (absurd >= 0) return {leaf: [{kind: 'input', index: absurd}]}
  const out = grow(whole, wp)
  return 'tree' in out ? out.tree : undefined
}

// Whether each hypothesis reads only names the goal's conclusion (its last hypothesis) reads.
const nearSeen = new WeakMap<Goal, boolean[]>()
const namesOf = (t: unknown): string[] => (t === undefined ? [] : [...JSON.stringify(t).matchAll(/"(?:name|map)":"([^"]+)"/g)].map(m => m[1]!))
function nearOf(goal: Goal): boolean[] {
  let out = nearSeen.get(goal)
  if (!out) {
    const theirs = new Set(namesOf(goal.hyps.at(-1)))
    nearSeen.set(goal, (out = goal.hyps.map(h => namesOf(h).every(n => theirs.has(n)))))
  }
  return out
}
// Units first: an atom some hypothesis splits on whose value the root's rows already force (a guard `?f = 0` where
// `?f = 1` holds, `k < len` where it is given). Split at the top, its forced side refutes at once; split late, under
// every other case, it is split again in each.
// GDP_UNITS=0 leaves them in the goal's order (for comparing).
const unitFirst = (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env?.GDP_UNITS !== '0'
let unitsNow = true
const unitSeen = new WeakMap<Goal, Lin[]>()
function unitsOf(goal: Goal): Lin[] {
  let out = unitSeen.get(goal)
  if (out) return out
  // Forced by the root's rows without a solver: a row the atom is (or is the negation of), or the bounds the rows give
  // single variables (x <= c, x >= c) deciding it whichever way its variables go.
  const root: Path = new Map(), rows = leafConstraints(goal, root), seen = new Set<string>(), given = new Set<string>()
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
    if (e.op !== 'if') continue
    const a = linear(e.then, at), b = linear(e.else, at), focus = topAtoms(e.c, at)
    if (!a || !b || !focus.length) continue
    for (const lemma of [sub(v(n), a), sub(v(n), b), sub(a, v(n)), sub(b, v(n))]) {
      const id = canon(lemma)
      if (at.has(id) || Object.keys(lemma).every(key => key === '1')) continue
      const no = growFocused(goal, new Map(at).set(id, {lin: lemma, holds: false}), focus, {nodes: 0})
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
// A refutation that splits only on these atoms (a cut's failing side), within a small budget.
function growFocused(goal: Goal, path: Path, focus: Lin[], budget: {nodes: number}, near: Lin[] = focus): Outcome {
  if (++budget.nodes > 64) return {stuck: 'unknown', path}
  const verdict = solveNear(leafConstraints(goal, path), [...near, ...[...path.values()].slice(-1).map(a => a.lin)])
  if (verdict.kind === 'refuted') { note(path, verdict.steps); return {tree: {leaf: verdict.steps}, nodes: budget.nodes} }
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

// (for profile.ts) The atoms the hypotheses leave open at a path, as growPlain finds its next split (no units, no cells).
export function openAtoms(goal: Goal, path: Path): Lin[] {
  const out: Lin[] = []
  for (const h of goal.hyps) openH(h, path, out)
  const seen = new Set<string>()
  return out.filter(lin => { const id = canon(lin); if (seen.has(id) || !Object.keys(lin).some(key => key !== '1') || path.has(id) || path.has(canonFlip(lin))) return false; seen.add(id); return true })
}
export const countLeavesOf = (t: Tree): number => ('leaf' in t ? 1 : countLeavesOf(t.yes) + countLeavesOf(t.no))
// (for dag.ts) growPlain's order of candidate splits at a path: units first, the conclusion's atoms, the hypotheses
// near it, the rest, then pairs of cells (the same code as growPlain's, the units on).
export function openOrder(goal: Goal, path: Path, rows: {lin: Lin}[]): Lin[] {
  const open: Lin[] = []
  const hyps = goal.hyps, last = hyps.length - 1
  let byHyp = openSeen.get(goal)
  if (!byHyp) openSeen.set(goal, (byHyp = new Map()))
  const openOf = (h: C) => { let seen = byHyp.get(h); if (!seen) byHyp.set(h, (seen = {})); return reusing(seen, path, p => { const out: Lin[] = []; openH(h, p, out); return out }) }
  if (unitFirst) open.push(...unitsOf(goal))
  if (last >= 0) open.push(...openOf(hyps[last]!))
  const near = nearOf(goal)
  for (const [i, h] of hyps.entries()) if (i !== last && near[i]) open.push(...openOf(h))
  for (const [i, h] of hyps.entries()) if (i !== last && !near[i]) open.push(...openOf(h))
  open.push(...openCells(rows, path))
  return open
}
