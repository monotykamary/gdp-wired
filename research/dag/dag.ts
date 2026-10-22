// The DAG search: kernel/prove.ts's case splits with learned clauses. `bun research/dag/dag.ts <goal.json> [--ms 55000]
// [--out <dir>] [--no-learn] [--no-units]`. Untrusted; its certificate goes to check-dag.ts.
//
// A node of the search is a path (atoms decided, as kernel.ts's Path). Where the rows at the path are refuted, the
// refutation's core (cores.ts: the decisions the rows it reads depend on) is replayed at the core alone, and the leaf
// is that shorter path with its derivation: a clause, "not all of these decisions", proven by a linear-arithmetic
// certificate (core/check.ts) over the rows the kernel reads at that path. Where both sides of a split are refuted,
// the two clauses resolve on the split's atom (a clause that doesn't hold the atom is the answer as it is: the other
// side is never grown, conflict-directed backjumping). Every clause is learned: a later path that holds all of a learned
// clause's decisions is closed by citing it (no solve, no new leaf: the certificate is a DAG), and a path holding all
// of a learned clause's decisions but one splits on that one next (unit propagation; its one side closes at once).
// The splits otherwise come in growPlain's order (the conclusion's atoms first, then the hypotheses near it, then
// the rest, then cells), and a node's arithmetic is growPlain's (Farkas rows first for a large system with a case still
// open, bounded elimination, the full one at a leaf; bisection or a fractional split when elimination is inexact).
//
// The certificate: {goal, nodes, root}; a node is {leaf: [[lin, holds], ...], steps, products?, squares?} or
// {res: [yes, no], on: lin} (resolution on the atom lin <= 0: `yes` a clause with it decided true, `no` with it decided
// false). A node's clause is the set of decisions of its leaf path, or the union of its two parents' less the atom.
// The root's clause is empty: the hypotheses can't hold together.
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import type {Lin, Step} from '../../core/solver.ts'
import {refuteFast, solve, work} from '../../core/solver.ts'
import {type Goal, type Path, canon, canonFlip, columnTerm, leafConstraintsReusing} from '../../kernel/kernel.ts'
import {loadGoal} from './goalio.ts'
import {coreOf, normLit, replay, sub, usedRows} from './cores.ts'
import {openOrder} from './tree.ts'

export type DagNode = {leaf: [Lin, boolean][], steps: Step[], products?: [number, number][], squares?: Lin[]} | {res: [number, number], on: Lin}
export type Dag = {goal: string, nodes: DagNode[], root: number}
type Clause = {lits: Map<string, boolean>, node: number}
type Out = {clause: Clause} | {stuck: 'sat' | 'unknown', why: string}

export function dagSearch(goal: Goal, opts: {until: number, learn?: boolean, units?: boolean, maxNodes?: number}) {
  const learn = opts.learn !== false, units = opts.units !== false
  const nodes: DagNode[] = [], learned: Clause[] = []
  const byLit = new Map<string, Clause[]>() // learned clauses by each of their literals
  const stats = {visits: 0, leaves: 0, memoHits: 0, unitSplits: 0, backjumps: 0, resolutions: 0, fullPathLeaves: 0, solves: 0, solveMs: 0, rowsMs: 0, coreMs: 0, maxDepth: 0}
  const litsOf = (path: Path) => { const m = new Map<string, boolean>(); for (const [key, a] of path) { const n = normLit(key, a.lin, a.holds); m.set(n.v, n.pos) } return m }
  const remember = (c: Clause) => { if (!learn) return; learned.push(c); for (const [v, pos] of c.lits) { const key = `${v}=${pos}`; let xs = byLit.get(key); if (!xs) byLit.set(key, (xs = [])); xs.push(c) } }
  const linOf = new Map<string, Lin>() // a literal's variable (canonical text) to its atom
  const go = (path: Path): Out => {
    stats.visits++
    stats.maxDepth = Math.max(stats.maxDepth, path.size)
    if (performance.now() > opts.until || stats.visits > (opts.maxNodes ?? 2_000_000)) return {stuck: 'unknown', why: 'budget'}
    const here = litsOf(path)
    // A learned clause the path holds: closed. One it holds but for one literal whose atom is open: split there next.
    let unit: {v: string, pos: boolean} | undefined
    if (learn) {
      const seen = new Set<Clause>()
      for (const [v, pos] of here) for (const c of byLit.get(`${v}=${pos}`) ?? []) {
        if (seen.has(c)) continue
        seen.add(c)
        let missing: [string, boolean] | undefined, ok = true
        for (const [w, p] of c.lits) {
          const h = here.get(w)
          if (h === p) continue
          if (h === undefined && !missing) { missing = [w, p]; continue }
          ok = false; break
        }
        if (!ok) continue
        if (!missing) { stats.memoHits++; return {clause: c} }
        if (units && !unit) unit = {v: missing[0], pos: missing[1]}
      }
      for (const c of byLit.get('') ?? []) { stats.memoHits++; return {clause: c} }
    }
    const t0 = performance.now()
    const full = leafConstraintsReusing(goal, path)
    stats.rowsMs += performance.now() - t0
    work.n += 1 + full.length
    const columns = [...path.values()].some(a => Object.keys(a.lin).some(key => key.startsWith('⟦')))
    const idx = full.flatMap((r, i) => (columns || !Object.keys(r.lin).some(key => key.startsWith('⟦')) ? [i] : []))
    const rows = idx.map(i => full[i]!), at = (i: number) => (i < rows.length ? idx[i]! : full.length + i - rows.length)
    const order = openOrder(goal, path, rows)
    const next = unit ? undefined : order.find(lin => Object.keys(lin).some(key => key !== '1') && !path.has(canon(lin)) && !path.has(canonFlip(lin)))
    const pending = !!unit || !!next
    const leaf = (steps: Step[]): Out => {
      stats.leaves++
      const t1 = performance.now()
      const used = usedRows(full.length, steps)
      const core = coreOf(goal, path, full, used)
      const short = core.size < path.size ? replay(goal, full, sub(path, core), steps) : undefined
      stats.coreMs += performance.now() - t1
      const p = short ? sub(path, core) : path
      if (!short) stats.fullPathLeaves++
      nodes.push({leaf: [...p.values()].map(a => [a.lin, a.holds]), steps: short ? short.steps : steps})
      const c = {lits: litsOf(p), node: nodes.length - 1}
      remember(c)
      return {clause: c}
    }
    const timed = <T>(f: () => T): T => { const t = performance.now(); stats.solves++; try { return f() } finally { stats.solveMs += performance.now() - t } }
    if (pending && rows.length > 60) {
      const fast = timed(() => refuteFast(rows))
      if (fast?.kind === 'refuted') return leaf(fast.steps.map(st => (st.kind === 'input' ? {...st, index: at(st.index)} : st)))
    }
    const verdict = timed(() => (pending && rows.length > 60 ? solve(rows, 2 * rows.length) : solve(rows)))
    if (verdict.kind === 'refuted') return leaf(verdict.steps.map(st => (st.kind === 'input' ? {...st, index: at(st.index)} : st)))
    if (pending && !columns && full.length > rows.length) {
      const fast = timed(() => refuteFast(full))
      if (fast?.kind === 'refuted') return leaf(fast.steps)
    }
    let split: Lin | undefined
    if (unit) { split = linOf.get(unit.v); stats.unitSplits++ }
    split ??= next ?? (verdict.kind === 'unknown' ? fractionalOf(verdict.point, path) : undefined)
    if (!split) return {stuck: verdict.kind === 'sat' ? 'sat' : 'unknown', why: verdict.kind === 'sat' ? 'a model' : 'no split'}
    const id = canon(split), n = normLit(id, split, true)
    linOf.set(n.v, split)
    // The side a unit clause closes first (it is closed at once); otherwise yes first, as growPlain.
    const first = unit ? (normLit(id, split, true).pos === unit.pos) : true
    const a = go(new Map(path).set(id, {lin: split, holds: first}))
    if ('stuck' in a) return a
    const holdsIn = (c: Clause, holds: boolean) => { const m = normLit(id, split!, holds); return c.lits.get(m.v) === m.pos }
    if (!holdsIn(a.clause, first)) { stats.backjumps++; return a }
    const b = go(new Map(path).set(id, {lin: split, holds: !first}))
    if ('stuck' in b) return b
    if (!holdsIn(b.clause, !first)) { stats.backjumps++; return b }
    const [yes, no] = first ? [a.clause, b.clause] : [b.clause, a.clause]
    const lits = new Map<string, boolean>()
    for (const c of [yes, no]) for (const [v, pos] of c.lits) if (v !== n.v) lits.set(v, pos)
    nodes.push({res: [yes.node, no.node], on: split})
    stats.resolutions++
    const c = {lits, node: nodes.length - 1}
    remember(c)
    return {clause: c}
  }
  // linOf for literals of the path: every split goes through go's split, so each learned literal's atom is known.
  const out = go(new Map())
  void columnTerm
  return {out, nodes, stats, learned: learned.length}
}

function fractionalOf(point: Record<string, number> | undefined, path: Path): Lin | undefined {
  for (const [x, value] of Object.entries(point ?? {})) {
    if (Math.abs(value - Math.round(value)) < 1e-9 || x.includes('*')) continue
    const c = Math.floor(value), lin: Lin = c === 0 ? {[x]: 1} : {[x]: 1, 1: -c}
    if (!path.has(canon(lin)) && !path.has(canonFlip(lin))) return lin
  }
  return undefined
}

// The DAG's size, and the tree it unfolds to (every cited clause's subproof written out again where it is cited).
export function sizes(dag: Dag) {
  const leafCount = new Array<number>(dag.nodes.length), stepCount = new Array<number>(dag.nodes.length)
  dag.nodes.forEach((n, i) => {
    if ('leaf' in n) { leafCount[i] = 1; stepCount[i] = n.steps.length }
    else { leafCount[i] = leafCount[n.res[0]]! + leafCount[n.res[1]]!; stepCount[i] = stepCount[n.res[0]]! + stepCount[n.res[1]]! }
  })
  // Only the nodes the root reaches.
  const live = new Set<number>(), todo = [dag.root]
  while (todo.length) { const i = todo.pop()!; if (live.has(i)) continue; live.add(i); const n = dag.nodes[i]!; if ('res' in n) todo.push(...n.res) }
  const ls = [...live].filter(i => 'leaf' in dag.nodes[i]!)
  return {nodes: live.size, leaves: ls.length, steps: ls.reduce((s, i) => s + (dag.nodes[i] as {steps: Step[]}).steps.length, 0),
    unfoldedLeaves: leafCount[dag.root]!, unfoldedSteps: stepCount[dag.root]!, bytes: JSON.stringify(dag).length}
}

if (import.meta.main) {
  const file = process.argv[2]!
  const arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
  const ms = Number(arg('--ms') ?? 55000), outDir = arg('--out')
  const goal = loadGoal(readFileSync(file, 'utf8'))
  const t0 = performance.now()
  const r = dagSearch(goal, {until: t0 + ms, learn: !process.argv.includes('--no-learn'), units: !process.argv.includes('--no-units')})
  const searchMs = performance.now() - t0
  const proven = 'clause' in r.out && r.out.clause.lits.size === 0
  const dag: Dag | undefined = proven ? {goal: goal.name, nodes: r.nodes, root: (r.out as {clause: Clause}).clause.node} : undefined
  let check: {ok: boolean, ms: number, why?: string} | undefined
  if (dag) {
    const {checkDag} = await import('./check-dag.ts')
    const t1 = performance.now(), c = checkDag(goal, dag)
    check = {ok: c.ok, ms: Math.round(performance.now() - t1), ...(c.ok ? {} : {why: c.why})}
  }
  const res = {goal: goal.name, hyps: goal.hyps.length, outcome: proven ? 'proven' : 'stuck' in r.out ? r.out.stuck : 'a clause not empty', searchMs: Math.round(searchMs),
    ...Object.fromEntries(Object.entries(r.stats).map(([key, x]) => [key, Math.round(x)])), learned: r.learned, nodesMade: r.nodes.length,
    ...(dag ? {size: sizes(dag)} : {}), ...(check ? {check} : {})}
  console.log(JSON.stringify(res))
  if (outDir) { mkdirSync(outDir, {recursive: true}); writeFileSync(`${outDir}/result.json`, JSON.stringify(res)); if (dag) writeFileSync(`${outDir}/dag.json`, JSON.stringify(dag)) }
  process.exit(0)
}
