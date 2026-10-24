// Untrusted, like prove.ts: a second search for a goal's tree, CDCL over the goal's atoms with the kernel's reading as
// the theory. Its refutation is a resolution DAG of refuted cases, unfolded into a kernel tree at the end, so the
// certificate is the kernel's as it is (kernel.ts's check); nothing here is trusted.
//
// The trail is a path (kernel.ts's Path). After unit propagation over the learned clauses (and bound propagation: an
// open atom its variables' single-variable bounds decide), the rows the kernel reads at the trail (reader.ts, which
// reads them again only where the trail changed what they read) are given to an incremental simplex (simplex.ts),
// and an infeasible one's rows are refuted exactly (core/solver.ts). Refuted, the refutation's core is the decisions
// the rows it reads need (reader.ts's reasons: a conjunction false needs one false part, a disjunction's last open part
// needs the others false, a term's value the decisions its choices took), and the leaf is that core with the
// derivation: a clause of decisions that can't all hold. Conflict analysis resolves the leaf with the clauses that propagated its latest literals down to the
// first unique implication point, learns the result, jumps back to where it is unit and asserts the flipped literal.
// Not refuted, the next decision is the open atom (growPlain's candidates at the trail) of highest activity (VSIDS),
// its last value first (phase saving); Luby restarts. A conflict at level 0 resolves to the empty clause.
//
// The DAG unfolds into a tree: a resolution on an atom the path leaves open is a split on it, its two parents the two
// sides; one the path decides follows the parent that agrees; a leaf's derivation is found again among the rows at
// its tree path (a longer path than its clause's), and where a row isn't there, the rows at the tree path are solved
// afresh.
import {type Constraint, type Lin, type Step, costs, env, refuteFast, solve, work} from '../core/solver.ts'
import {checkRefutation} from '../core/check.ts'
import {type Goal, type Path, type Tree, atomOf, canon, canonFlip, isMonomial, leafConstraints} from './kernel.ts'
import {cellPair, late, logged, nearOf, openAt, openCells, pairedKeys, queryHook, rowsAt, unitAtoms, type Outcome} from './prove.ts'
import {Reader, type Row, keepClean, namesOf} from './reader.ts'
import {Simplex} from './simplex.ts'

// A derivation's own inputs: the rows it reads, in order, and the steps renumbered to them.
function localize(rows: {lin: Lin}[], steps: Step[]): {inputs: Lin[], steps: Step[]} {
  const inputs: Lin[] = [], at = new Map<number, number>()
  const out = steps.map(st => {
    if (st.kind !== 'input') return st
    let j = at.get(st.index)
    if (j === undefined) { j = inputs.length; at.set(st.index, j); inputs.push(rows[st.index]!.lin) }
    return {...st, index: j}
  })
  return {inputs, steps: out}
}
// An atom's variable: the smaller of its canonical text and its flip's (remembered per form).
const keyMemo = new WeakMap<Lin, string>()
const keyOf = (lin: Lin): string => {
  let key = keyMemo.get(lin)
  if (key === undefined) { const a = canon(lin), b = canonFlip(lin); keyMemo.set(lin, (key = b < a ? b : a)) }
  return key
}
// --- the search -----------------------------------------------------------------------------------------------------------

// A node of the refutation: a leaf (its decisions, by variable, and a derivation over the rows at its path) or a
// resolution of two earlier nodes on a variable (`res[0]` the one with the atom as stored true, `res[1]` false).
type DagNode = {inputs: Lin[], steps: Step[]} | {res: [number, number], on: Lin}
type Var = {name: string, lin: Lin, terms: [string, number][], col: boolean, tid?: number[], val?: boolean, level: number, reason?: number, at: number, act: number, phase: boolean,
  bj?: number[], bjAt?: number, bsig?: number, bver?: number, sj?: (number | undefined)[], sx?: Simplex, pair?: boolean}
type Clause = {lits: Map<string, boolean>, node: number}
// GDP_CDCL_LP=0: each node solved by elimination alone (no simplex); GDP_CDCL_FILL (8): the simplex's tableau begun
// again past this many entries a row the node reads (research/step's comparisons).
const lpFill = Number(env.GDP_CDCL_FILL ?? 8), useLp = env.GDP_CDCL_LP !== '0', verify = env.GDP_CDCL_VERIFY === '1'
// GDP_CDCL_INC=0: each node's rows read whole and loaded into the simplex whole (as before, for comparing); else the
// rows kept from node to node (reader.ts's sync) and the simplex given the rows that came and went.
const useInc = env.GDP_CDCL_INC !== '0' && keepClean
// Counters research/step reads (times only while `on`).
export const cdclStats = {on: false, runs: 0, proven: 0, conflicts: 0, decisions: 0, solveMs: 0, rowsMs: 0, coreMs: 0, unfoldMs: 0, leaves: 0, resolved: 0, coreSize: 0, pathSize: 0, lpMisses: 0, resolved2: 0, unfoldWhy: '', orderMs: 0, boundMs: 0, openMisses: 0, lpMs: 0, lpUnknown: 0, fmCalls: 0, pivots: 0, lpRebuilds: 0, lpRows: 0, lpNnz: 0, lpVars: 0, lpLoad: 0, nodes: 0, boundRounds: 0}

// `opts.model`: only whether the goal has a model is wanted (core/bmc.ts): a refutation isn't unfolded into a tree, its
// outcome `unknown` with `why` REFUTED; each decision's phase is the simplex's point's (phaseAtPoint); past `opts.wall` (wall time) the search stops as past its budget.
// `opts.core`, with `model`: a refutation's outcome also names the hypotheses its leaves read (`core`, their indices in
// goal.hyps): those alone have no model (each leaf's rows are those hypotheses' facts at its decisions, or rows true of
// any value: the trail's atoms, the naturals, the term columns' definitions), as core/infer.ts's join reads it.
export const REFUTED = 'refuted, not unfolded'
export type Refuted = Outcome & {core?: number[]}
export function growCdcl(goal: Goal, root: Path, budget: {nodes: number, until?: number}, opts: {maxLeaves?: number, model?: boolean, wall?: number, core?: boolean} = {}): Outcome {
  const go = () => cdclSession(goal, root, opts).run(budget, opts.wall)
  return queryHook.on && !queryHook.depth ? logged(opts.model ? 'model' : 'cdcl', goal, go) : go()
}
// A search kept from one run to the next (core/bmc.ts's deeper goals): its atoms, their activities and phases, its learned
// clauses and the simplex's tableau. Between runs the caller may add hypotheses to the goal (goal.hyps grows; none is
// taken away), so every clause learned stays a consequence of the goal. A run may assume an atom (`assume`, decided
// first, at level 1): where the search learns it false the run ends refuted (REFUTED), as where nothing is assumed and
// the goal is refuted. Each run's own budget: nodes, `until` on the counted clock, `wall`.
export function cdclSession(goal: Goal, root: Path, opts: {maxLeaves?: number, model?: boolean, core?: boolean} = {}) {
  let until = Infinity, budget: {nodes: number, until?: number} = {nodes: 0}, wall: number | undefined, assumed: [string, boolean] | undefined
  const st = cdclStats, timing = st.on
  const t = <T>(f: () => T, add: (ms: number) => void): T => { if (!timing) return f(); const t0 = performance.now(); try { return f() } finally { add(performance.now() - t0) } }
  st.runs++
  costs.sessions++; costs.sessionHyps += goal.hyps.length
  const vars = new Map<string, Var>(), trail: string[] = [], levels: number[] = []
  let sx = useLp ? new Simplex() : undefined
  const nodes: DagNode[] = [], clauses: Clause[] = [], occ = new Map<string, number[]>()
  // (with opts.core: each leaf's hypotheses, by node; the hypothesis each row at this node came from)
  const leafHyps = new Map<number, number[]>(), wantCore = !!(opts.core && opts.model)
  const hypsOf = (rs: Row[]): number[] => {
    if (useInc && sx) return reader.hypsOf(rs)
    const at = new Map<Row, number>()
    for (let i = 0; i < goal.hyps.length; i++) for (const r of reader.facts(i).rows) at.set(r, i)
    return [...new Set(rs.flatMap(r => { const i = at.get(r); return i === undefined ? [] : [i] }))]
  }
  let inc = 1
  // An atom as a variable: the stored form is the one whose canonical text is the variable's name (the smaller).
  const ensure = (lin: Lin): string => {
    const key = keyOf(lin)
    if (!vars.has(key)) {
      const flip = key !== canon(lin), stored = flip ? atomOf(lin, false).lin : lin, terms = Object.entries(stored).filter(([x0]) => x0 !== '1')
      vars.set(key, {name: key, lin: stored, terms, col: terms.some(([x0]) => x0.startsWith('⟦')), level: -1, at: -1, act: 0, phase: !flip})
    }
    return key
  }
  // Each candidate form's variable (none for a constant form), and the node it was last met at (the candidates told
  // apart by form, as a set of forms would).
  const recs = new WeakMap<Lin, {x: Var | undefined, seen: number}>()
  const recOf = (lin: Lin) => { let r = recs.get(lin); if (!r) recs.set(lin, (r = {x: namesOf(lin).length > 0 ? vars.get(ensure(lin)) : undefined, seen: 0})); return r }
  let candGen = 0, colsOn = 0, boundGen = 0, pairsChanged = 0
  // prove.ts's openCells at the trail, from the reader's live cells: each pair of one map whose keys' difference the
  // trail leaves open (that atom, or its flip where the trail decides it one way); made again only where the live cells
  // or the decisions about pairs have changed.
  let cellsAt = [-1, -1], cellsOpen: Lin[] = []
  const truthOf = (lin: Lin): boolean | undefined => { const x = recOf(lin).x; return x?.val === undefined ? undefined : x.name === canon(lin) ? x.val : !x.val }
  const openCellsLive = (): Lin[] => {
    if (cellsAt[0] === reader.cellsChanged && cellsAt[1] === pairsChanged) return cellsOpen
    const out: Lin[] = []
    for (const names of reader.cells.values()) {
      const ns = [...names]
      for (let i = 0; i < ns.length; i++) for (let j = i + 1; j < ns.length; j++) {
        const pair = cellPair(ns[i]!, ns[j]!)
        if (pairedKeys.skip && Object.keys(pair.d).some(isMonomial)) continue
        for (const lin of [pair.d, pair.neg]) { const x = recOf(lin).x; if (x) x.pair = true }
        const a = truthOf(pair.d), b = truthOf(pair.neg)
        if (a === undefined) out.push(pair.d)
        else if (a === true && b === undefined) out.push(pair.neg)
      }
    }
    cellsAt = [reader.cellsChanged, pairsChanged]
    return (cellsOpen = out)
  }
  const listRecs = new WeakMap<Lin[], {x: Var | undefined, seen: number}[]>()
  const bx = new Simplex(true, true), bxIn = new Set<number>(), toAssert = new Set<number>(), toRetract = new Set<number>()
  const loAt: number[] = [], loB: number[] = [], loRow: number[] = [], hiAt: number[] = [], hiB: number[] = [], hiRow: number[] = []
  // The root's own decisions are level 0, with no reason: they stay in every clause (the tree starts below them).
  const rootNames = new Set<string>(), stamps: number[] = []
  let stampN = 0
  for (const [key, a] of root) {
    const name = ensure(a.lin), x = vars.get(name)!, val = name === key ? a.holds : !a.holds
    x.val = val; x.level = 0; x.at = trail.length; stamps[x.at] = ++stampN; trail.push(name); rootNames.add(name)
    if (x.col) colsOn++
  }
  const reader = new Reader(goal, {
    get: name => vars.get(name), stamp: at => stamps[at]!, size: () => trail.length,
    lin: at => { const name = trail[at]!, x = vars.get(name)!; return {name, lin: x.lin, holds: x.val!} },
  })
  let last = goal.hyps.length - 1
  const near = nearOf(goal)
  const decidedLin = (lin: Lin) => vars.get(keyOf(lin))?.val !== undefined
  const fixed = trail.length
  const level = () => levels.length
  const pathOf = (): Path => new Map(trail.map(name => { const x = vars.get(name)!; return [name, {lin: x.lin, holds: x.val!}] }))
  const assign = (name: string, val: boolean, reason?: number) => {
    const x = vars.get(name)!
    x.val = val; x.level = level(); x.at = trail.length; x.phase = val; stamps[x.at] = ++stampN
    if (reason === undefined) delete x.reason; else x.reason = reason
    trail.push(name)
    if (x.col) colsOn++
    if (x.pair) pairsChanged++
    reader.touch(name)
  }
  const undoTo = (l: number) => {
    const keep = levels[l] ?? trail.length
    while (trail.length > Math.max(keep, fixed)) { const name = trail.pop()!, x = vars.get(name)!; delete x.val; x.level = -1; delete x.reason; if (x.col) colsOn--; if (x.pair) pairsChanged++; reader.touch(name) }
    levels.length = l
  }
  const addClause = (lits: Map<string, boolean>, node: number): number => {
    clauses.push({lits, node})
    const i = clauses.length - 1
    for (const [name, pos] of lits) { const key = `${name}=${pos}`; let xs = occ.get(key); if (!xs) occ.set(key, (xs = [])); xs.push(i) }
    return i
  }
  let qhead = 0
  // Unit propagation: a clause whose literals all hold is a conflict (its index); all but one, the last is flipped.
  const propagate = (): number | undefined => {
    while (qhead < trail.length) {
      const name = trail[qhead++]!, x = vars.get(name)!
      for (const ci of occ.get(`${name}=${x.val}`) ?? []) {
        const c = clauses[ci]!
        costs.props += c.lits.size
        let open: string | undefined, nOpen = 0, dead = false
        for (const [w, p] of c.lits) {
          const y = vars.get(w)!
          if (y.val === undefined) { nOpen++; open = w; if (nOpen > 1) break } else if (y.val !== p) { dead = true; break }
        }
        if (dead || nOpen > 1) continue
        if (nOpen === 0) return ci
        assign(open!, !c.lits.get(open!)!, ci)
      }
    }
    return undefined
  }
  const bump = (lits: Map<string, boolean>) => {
    for (const name of lits.keys()) { const x = vars.get(name)!; x.act += inc; if (x.act > 1e100) { for (const y of vars.values()) y.act *= 1e-100; inc *= 1e-100 } }
    inc /= 0.95
  }
  const resolveOn = (c: Clause, name: string): Clause => {
    const x = vars.get(name)!, r = clauses[x.reason!]!
    if (r.node < 0) materialize(x.reason!)
    const lits = new Map(c.lits)
    lits.delete(name)
    for (const [w, p] of r.lits) if (w !== name) lits.set(w, p)
    nodes.push({res: c.lits.get(name)! ? [c.node, r.node] : [r.node, c.node], on: x.lin})
    st.resolved++
    return {lits, node: nodes.length - 1}
  }
  // A leaf: the decisions of a reason (the root's are every leaf's, below which the tree starts: not literals of its
  // clause) and a derivation over the rows it reads.
  const leafNode = (w: Iterable<string>, inputs: Lin[], steps: Step[], extra?: [string, boolean], hyps?: number[]): Clause => {
    nodes.push({inputs, steps})
    if (hyps) leafHyps.set(nodes.length - 1, hyps)
    st.leaves++
    const lits = new Map<string, boolean>()
    for (const name of w) if (!rootNames.has(name)) lits.set(name, vars.get(name)!.val!)
    if (extra) lits.set(extra[0], extra[1])
    st.coreSize += lits.size
    return {lits, node: nodes.length - 1}
  }
  // A theory conflict at the trail: the leaf at its core, the reasons of the rows its derivation reads.
  const leafAt = (rows: Row[], steps: Step[]): Clause => t(() => {
    const w = new Set<string>()
    for (const s of steps) if (s.kind === 'input') for (const name of rows[s.index]!.w) w.add(name)
    st.pathSize += trail.length - fixed
    const local = localize(rows, steps)
    return leafNode(w, local.inputs, local.steps, undefined, wantCore ? hypsOf(steps.flatMap(s => (s.kind === 'input' ? [rows[s.index]!] : []))) : undefined)
  }, ms => { st.coreMs += ms })
  // Bound propagation's reasons, made when conflict analysis reads them: the atom's bounds (single-variable rows at the
  // trail then) and its other side refute each other, a leaf at the bounds' reasons with that side decided.
  const pending = new Map<number, {w: Set<string>, used: Lin[], name: string, val: boolean, hyps?: number[]}>()
  const materialize = (ci: number) => t(() => {
    const b = pending.get(ci)!, x = vars.get(b.name)!, c = clauses[ci]!
    pending.delete(ci)
    const local = [...b.used.map(lin => ({lin, label: ''})), {lin: atomOf(x.lin, !b.val).lin, label: ''}]
    const s = solve(local)
    if (s.kind !== 'refuted') throw new Error('a bound propagation its bounds do not refute')
    const loc = localize(local, s.steps), made = leafNode(b.w, loc.inputs, loc.steps, [b.name, !b.val], b.hyps)
    c.lits = made.lits; c.node = made.node
  }, ms => { st.coreMs += ms })
  const luby = (i: number): number => { let n = 1; while ((1 << n) - 1 < i + 1) n++; return (1 << n) - 1 === i + 1 ? 1 << (n - 1) : luby(i + 1 - (1 << (n - 1))) }
  // With a model wanted: each open atom's phase (no term column's) set to its value at the simplex's point, which meets
  // every row read (over the rationals), so a decision tends to stay feasible (runs/unsat/bmc-only-phase: 320 of
  // CHC-COMP's 475 unsat tasks, 280 without; each atom decided at once at the point instead, 271).
  // (set where it is read: for the atom decided, at the node it is decided; an atom met open at a node and decided at a
  // later one where the simplex didn't run keeps the phase it last had)
  const phaseAtPoint = (x: Var, lp: Simplex) => {
    if (x.val !== undefined || x.col) return
    // (lp.holds(x.lin), its columns kept per tableau)
    if (x.sx !== lp) { x.sx = lp; x.sj = x.terms.map(([x0]) => lp.indexOf(x0)) }
    let v = x.lin['1'] ?? 0, known = true
    for (let q = 0; q < x.sj!.length && known; q++) { const j = x.sj![q]; if (j === undefined) known = false; else v += x.terms[q]![1] * lp.value(j) }
    if (!known) { const at = lp.holds(x.lin); if (at !== undefined) x.phase = at; x.sx = undefined; return }
    x.phase = v <= 1e-7 * Math.max(1, Math.abs(v))
  }
  let restartAt = 32, nRestart = 0, sinceRestart = 0
  const stuck = (kind: 'sat' | 'unknown', why: string, extra: {witness?: Record<string, number>} = {}): Outcome => ({stuck: kind, path: pathOf(), why, ...extra})
  const run = (b: {nodes: number, until?: number}, w?: number, assume?: Lin): Outcome => {
    budget = b; until = b.until ?? Infinity; wall = w; last = goal.hyps.length - 1
    restartAt = 32; nRestart = 0; sinceRestart = 0
    undoTo(0); qhead = Math.min(qhead, trail.length) // (a run before this one may have left decisions)
    if (assume) { const name = ensure(assume); assumed = [name, name === canon(assume)] } else assumed = undefined
    return queryHook.on && !queryHook.depth ? logged(opts.model ? 'model' : 'cdcl', goal, search) : search()
  }
  const search = (): Outcome => {
    for (;;) {
      if (++budget.nodes > 200_000 || late(until) || (wall !== undefined && performance.now() > wall)) return stuck('unknown', budget.nodes > 200_000 ? 'nodes' : 'time')
      let conflict: Clause | undefined
      const ci = propagate()
      if (ci !== undefined) conflict = clauses[ci]!
      else if (assumed && vars.get(assumed[0])!.val === !assumed[1]) return {stuck: 'unknown', path: new Map(), why: REFUTED}
      else if (assumed && vars.get(assumed[0])!.val === undefined) {
        levels.push(trail.length)
        assign(assumed[0], assumed[1])
        continue
      } else {
        reader.begin()
        st.nodes++
        const inc = useInc && sx !== undefined
        const rowsR = t(() => (inc ? (reader.sync(), reader.live) : reader.rows()), ms => { st.rowsMs += ms })
        const full: Constraint[] = rowsR
        if (inc) {
          // The forms that came and went: the single-variable ones' bounds now (for bound propagation, `bx`), the
          // simplex's when it next runs (`toAssert`, `toRetract`: a form in and out between its runs never reaches it).
          const single = (id: number) => reader.form(full[reader.slotOf(id)]!.lin).names.length === 1
          for (const id of reader.left) { if (bxIn.delete(id)) bx.retract(id); if (!toAssert.delete(id)) toRetract.add(id) }
          for (const id of reader.entered) { if (single(id)) { bxIn.add(id); bx.assert(id, full[reader.slotOf(id)]!.lin) } if (!toRetract.delete(id)) toAssert.add(id) }
        }
        if (verify) {
          const mine = new Set(rowsR.map(r => canon(r.lin))), theirs = new Set(leafConstraints(goal, pathOf()).map(r => canon(r.lin)))
          if (mine.size !== theirs.size || [...mine].some(x => !theirs.has(x))) throw new Error(`reader.ts's rows differ from kernel.ts's at a node of ${goal.name}`)
        }
        work.n += 1 + full.length
        costs.cdclNodes++; costs.cdclRows += full.length
        // (the elimination below reads term columns' rows only once the trail has an atom about one, as growPlain does)
        const columns = colsOn > 0
        // (the rows read by the elimination, made when it runs)
        let idx: number[] | undefined, rows: Constraint[] | undefined
        const plain = (): Constraint[] => {
          if (rows) return rows
          idx = columns ? undefined : full.flatMap((r, i) => (reader.readsColumn(r.lin) ? [] : [i]))
          return (rows = idx ? idx.map(i => full[i]!) : full)
        }
        const at = (i: number) => (!idx ? i : i < plain().length ? idx[i]! : full.length + i - plain().length)
        // The candidates, in growPlain's order: the units, the conclusion's open atoms, the hypotheses' near it, the
        // rest, pairs of cells.
        const cands = t(() => {
          // (each list's forms' variables kept with the list, the same array while it stands)
          const g = ++candGen, keep: Var[] = []
          const take = (lins: Lin[]) => {
            let rs = listRecs.get(lins)
            if (!rs) listRecs.set(lins, (rs = lins.map(recOf)))
            costs.scan += rs.length
            for (const r of rs) { if (r.seen === g) continue; r.seen = g; if (r.x && r.x.val === undefined) keep.push(r.x) }
          }
          take(unitAtoms(goal))
          if (last >= 0) take(reader.openList(last))
          for (let i = 0; i < last; i++) if (near[i]) take(reader.openList(i))
          for (let i = 0; i < last; i++) if (!near[i]) take(reader.openList(i))
          if (inc) { if (reader.hasCells()) take(openCellsLive()) } else if (plain().some(r => reader.readsCell(r.lin))) take(openCells(plain(), pathOf()))
          return keep
        }, ms => { st.orderMs += ms })
        const open = cands.length > 0
        costs.cands += cands.length
        // Bound propagation: an open atom its variables' bounds (the single-variable rows) decide.
        const tb = timing ? performance.now() : 0
        if (open) {
          // (each name's tightest bounds and their rows, by the name's id, stamped by node; kept from node to node, the
          // simplex's own bounds)
          const g = ++boundGen
          for (let i = 0; i < (inc ? 0 : full.length); i++) {
            const lin = full[i]!.lin, ks = reader.form(lin).names
            if (ks.length !== 1) continue
            const j = ks[0]!, c = lin[reader.nameOf(j)]!, k0 = lin['1'] ?? 0
            if (c > 0) { const b = Math.floor(-k0 / c); if (hiAt[j] !== g || b < hiB[j]!) { hiAt[j] = g; hiB[j] = b; hiRow[j] = i } }
            else if (c < 0) { const b = Math.ceil(k0 / -c); if (loAt[j] !== g || b > loB[j]!) { loAt[j] = g; loB[j] = b; loRow[j] = i } }
          }
          let forced = 0
          for (const x of cands) {
            const name = x.name
            if (x.val !== undefined || x.col) continue // (a term column's rows read differently once its choice is decided)
            // (unforced at the bounds it last read, which haven't changed since: unforced still)
            // (no bound has changed since; or a name without any; or no bound it reads has)
            let sig = 0
            if (inc) {
              if (x.bver === bx.changes) continue
              if (!x.bj) {
                if (x.bjAt === bx.vars) continue
                x.bjAt = bx.vars
                const bj = x.terms.map(([x0]) => bx.indexOf(x0))
                if (bj.some(j => j === undefined)) continue
                x.bj = bj as number[]
              }
              for (const j of x.bj) sig += bx.version(j)
              if (x.bsig === sig) { x.bver = bx.changes; continue }
            }
            const tid = (x.tid ??= reader.form(x.lin).names)
            const side = (val: boolean): number[] | undefined => { // the rows that force the stored atom to `val`
              let sum = x.lin['1'] ?? 0
              const used: number[] = []
              if (inc) {
                for (let q = 0; q < x.terms.length; q++) {
                  const [x0, c] = x.terms[q]!, j = x.bj ? x.bj[q] : bx.indexOf(x0), up = (c > 0) === val
                  if (j === undefined) return undefined
                  const b = up ? bx.high(j) : bx.low(j)
                  if (!Number.isFinite(b)) return undefined
                  sum += c * b; used.push(reader.slotOf(up ? bx.highWhy(j) : bx.lowWhy(j)))
                }
                return (val ? sum <= 0 : sum >= 1) ? used : undefined
              }
              for (let q = 0; q < tid.length; q++) {
                const c = x.terms[q]![1], j = tid[q]!, up = (c > 0) === val
                if (up ? hiAt[j] !== g : loAt[j] !== g) return undefined
                sum += c * (up ? hiB[j]! : loB[j]!); used.push(up ? hiRow[j]! : loRow[j]!)
              }
              return (val ? sum <= 0 : sum >= 1) ? used : undefined
            }
            let hit = false
            for (const val of [true, false]) {
              const used = side(val)
              if (!used) continue
              hit = true
              const w = new Set<string>()
              for (const i of used) for (const n of rowsR[i]!.w) w.add(n)
              clauses.push({lits: new Map([[name, !val]]), node: -1})
              pending.set(clauses.length - 1, {w, used: used.map(i => full[i]!.lin), name, val, ...(wantCore ? {hyps: hypsOf(used.map(i => rowsR[i]!))} : {})})
              assign(name, val, clauses.length - 1)
              forced++
              break
            }
            if (inc) { x.bsig = hit ? undefined : sig; x.bver = hit ? undefined : bx.changes }
          }
          if (timing) st.boundMs += performance.now() - tb
          if (forced) { st.boundRounds++; continue }
        }
        let steps: Step[] | undefined, lpSat = false
        let verdict: ReturnType<typeof solve> | undefined
        t(() => {
          // The simplex first (warm from the node before): a conflict's rows, refuted exactly, are the leaf. With a case
          // still open, a node it finds feasible is split; with none, the exact elimination below decides it (integers).
          if (sx) {
            const t0 = timing ? performance.now() : 0
            // (a tableau that has gathered many more forms than a node reads is begun again: every pivot updates them all)
            const over = sx.size > 4 * full.length + 500 || sx.nnz > lpFill * full.length
            if (over) { sx = new Simplex(); st.lpRebuilds++ }
            if (inc) {
              // (a tableau begun has the rows asserted in kernel.ts's order, which its variables', so Bland's rule, follow)
              if (over || !sx.vars) for (const r of reader.rows()) sx.assert(reader.form(r.lin).id, r.lin)
              else { for (const id of toRetract) sx.retract(id); for (const id of toAssert) sx.assert(id, full[reader.slotOf(id)]!.lin) }
              toAssert.clear(); toRetract.clear()
            }
            const p0 = sx.pivots
            let lp = inc ? sx.settle() : sx.load(full)
            if (lp.kind === 'sat') lp = sx.check()
            if (inc && lp.kind === 'conflict') lp = {kind: 'conflict', rows: lp.rows.map(id => reader.slotOf(id))}
            costs.pivots += sx.pivots - p0; if (sx.pivots > p0) costs.pivotNnz += (sx.pivots - p0) * sx.size
            if (timing) { st.lpMs += performance.now() - t0; st.pivots += sx.pivots - p0; st.lpRows = sx.size; st.lpNnz = sx.nnz; st.lpVars = sx.vars; st.lpLoad = full.length; if (lp.kind === 'unknown') st.lpUnknown++ }
            if (lp.kind === 'conflict') {
              const support = lp.rows.sort((x, y) => x - y), out = solve(support.map(i => full[i]!))
              if (out.kind === 'refuted') steps = out.steps.map(s => (s.kind === 'input' ? {...s, index: support[s.index]!} : s))
              else st.lpMisses++
            }
            lpSat = lp.kind === 'sat'
            if (steps || (open && lp.kind === 'sat')) return
          }
          st.fmCalls++
          const rows = plain()
          if (open && rows.length > 60) { const fast = refuteFast(rows); if (fast?.kind === 'refuted') steps = fast.steps.map(s => (s.kind === 'input' ? {...s, index: at(s.index)} : s)) }
          if (!steps) {
            verdict = open && rows.length > 60 ? solve(rows, 2 * rows.length) : solve(rows)
            if (verdict.kind === 'refuted') steps = verdict.steps.map(s => (s.kind === 'input' ? {...s, index: at(s.index)} : s))
          }
          if (!steps && open && !columns && full.length > rows.length) { const fast = refuteFast(full); if (fast?.kind === 'refuted') steps = fast.steps }
        }, ms => { st.solveMs += ms })
        if (steps) conflict = leafAt(rowsR, steps)
        else {
          // A decision: the open atom of highest activity (the first candidate among equals).
          let pick: string | undefined, best = -1, px: Var | undefined
          for (const x of cands) if (x.val === undefined && x.act > best) { best = x.act; pick = x.name; px = x }
          if (opts.model && lpSat && sx && open && px) phaseAtPoint(px, sx)
          if (!pick && verdict?.kind === 'unknown') {
            for (const [x0, value] of Object.entries(verdict.point ?? {})) {
              if (Math.abs(value - Math.round(value)) < 1e-9 || isMonomial(x0)) continue
              const c = Math.floor(value), lin: Lin = c === 0 ? {[x0]: 1} : {[x0]: 1, 1: -c}
              if (!decidedLin(lin)) { pick = ensure(lin); break }
            }
          }
          // Nothing open by this reading: the kernel's own reading of the trail (prove.ts's) has the last word.
          if (!pick) {
            const p = pathOf(), more = openAt(goal, p, rowsAt(goal, p)).find(lin => Object.keys(lin).some(key => key !== '1') && !decidedLin(lin))
            if (more) { st.openMisses++; pick = ensure(more) }
          }
          if (!pick) return verdict?.kind === 'sat' ? stuck('sat', 'a model', {witness: verdict.witness}) : stuck('unknown', 'no split')
          levels.push(trail.length)
          st.decisions++
          assign(pick, vars.get(pick)!.phase)
          continue
        }
      }
      // Conflict analysis.
      st.conflicts++; sinceRestart++
      let c = conflict
      for (;;) {
        if (!c.lits.size) {
          if (opts.model) {
            if (!wantCore) return {stuck: 'unknown', path: new Map(), why: REFUTED}
            // the hypotheses the leaves below the empty clause read (a clause never made into a node, a bound's not yet
            // materialized, leaves the core unknown)
            const core = new Set<number>(), seen = new Set<number>(), todo = [c.node]
            let whole = true
            while (todo.length) {
              const i = todo.pop()!
              if (i < 0) { whole = false; break }
              if (seen.has(i)) continue
              seen.add(i)
              const nd = nodes[i]!
              if ('res' in nd) todo.push(...nd.res); else for (const h of leafHyps.get(i) ?? []) core.add(h)
            }
            return {stuck: 'unknown', path: new Map(), why: REFUTED, ...(whole ? {core: [...core].sort((a, b) => a - b)} : {})} as Refuted
          }
          const tree = t(() => unfold(goal, nodes, c.node, root, opts.maxLeaves ?? 20_000, until), ms => { st.unfoldMs += ms })
          if (!tree) return stuck('unknown', 'unfold')
          st.proven++
          return {tree, nodes: budget.nodes}
        }
        const top = Math.max(...[...c.lits.keys()].map(name => vars.get(name)!.level))
        if (top < level()) { undoTo(top); qhead = trail.length }
        const here = [...c.lits.keys()].filter(name => vars.get(name)!.level === top)
        if (top === 0) { c = resolveOn(c, here.reduce((a, b) => (vars.get(a)!.at > vars.get(b)!.at ? a : b))); continue }
        if (here.length === 1) break
        const latest = here.reduce((a, b) => (vars.get(a)!.at > vars.get(b)!.at ? a : b))
        if (vars.get(latest)!.reason === undefined) break
        c = resolveOn(c, latest)
      }
      const top = Math.max(...[...c.lits.keys()].map(name => vars.get(name)!.level))
      const here = [...c.lits.keys()].filter(name => vars.get(name)!.level === top)
      bump(c.lits)
      const learned = addClause(c.lits, c.node)
      if (here.length !== 1) { undoTo(Math.max(0, top - 1)); qhead = Math.min(qhead, trail.length); continue }
      const uip = here[0]!
      undoTo(Math.max(0, ...[...c.lits.keys()].filter(name => name !== uip).map(name => vars.get(name)!.level)))
      qhead = trail.length
      assign(uip, !c.lits.get(uip)!, learned)
      if (sinceRestart >= restartAt) { sinceRestart = 0; restartAt = 32 * luby(++nRestart); undoTo(0); qhead = Math.min(qhead, trail.length) }
    }
  }
  return {run}
}

// The DAG as a kernel tree below `root`, walked depth first with a reader of its own (the tree's path is a stack, as
// the search's trail is): each leaf's derivation found again among the rows at its tree path, in kernel.ts's order (the
// tree's leaves index those), else those rows refuted afresh. GDP_CDCL_VERIFY=1 compares each leaf's rows with
// kernel.ts's (kernel/cdcl.test.ts).
function unfold(goal: Goal, nodes: DagNode[], top: number, root: Path, maxLeaves: number, until: number): Tree | undefined {
  const stack: {name: string, lin: Lin, holds: boolean}[] = [], on = new Map<string, {val: boolean, at: number}>(), stamps: number[] = []
  let stampN = 0, leaves = 0
  const reader = new Reader(goal, {get: name => on.get(name), stamp: at => stamps[at]!, size: () => stack.length, lin: at => stack[at]!})
  const push = (name: string, lin: Lin, holds: boolean) => { on.set(name, {val: holds, at: stack.length}); stamps[stack.length] = ++stampN; stack.push({name, lin, holds}); reader.touch(name) }
  const pop = () => { const name = stack.pop()!.name; on.delete(name); reader.touch(name) }
  for (const [key, a] of root) push(key, a.lin, a.holds)
  const go = (i: number): Tree | undefined => {
    const n = nodes[i]!
    if ('res' in n) {
      const key = canon(n.on), d = on.get(key)
      if (d) return go(d.val ? n.res[0] : n.res[1])
      push(key, n.on, true); const yes = go(n.res[0]); pop()
      if (!yes) return undefined
      push(key, n.on, false); const no = go(n.res[1]); pop()
      return no && {split: n.on, yes, no}
    }
    if (++leaves > maxLeaves || late(until)) { cdclStats.unfoldWhy = leaves > maxLeaves ? 'leaves' : 'time'; return undefined }
    reader.begin()
    const rows = reader.leafRows()
    costs.unfoldRows += rows.length
    if (verify) {
      const path: Path = new Map(stack.map(x => [x.name, {lin: x.lin, holds: x.holds}])), kr = leafConstraints(goal, path)
      if (kr.length !== rows.length || kr.some((r, j) => canon(r.lin) !== canon(rows[j]!.lin))) {
        const j = kr.findIndex((r, j2) => canon(r.lin) !== canon(rows[j2]?.lin ?? {}))
        throw new Error(`reader.ts's rows differ from kernel.ts's at a leaf of ${goal.name}: ${kr.length} vs ${rows.length}, at ${j}: ${JSON.stringify(kr[j])} vs ${JSON.stringify(rows[j]?.lin)}; next ${JSON.stringify(kr.slice(j + 1, j + 3).map(r => r.lin))} vs ${JSON.stringify(rows.slice(j + 1, j + 3).map(r => r.lin))}`)
      }
    }
    const at = new Map<string, number>()
    rows.forEach((r, j) => { const key = canon(r.lin); if (!at.has(key)) at.set(key, j) })
    const steps: Step[] = []
    for (const s of n.steps) {
      if (s.kind !== 'input') { steps.push(s); continue }
      const j = at.get(canon(n.inputs[s.index]!))
      if (j === undefined) break
      steps.push({...s, index: j})
    }
    if (steps.length === n.steps.length && checkRefutation(rows, steps)) return {leaf: steps}
    // (a row a longer path reads otherwise: a hypothesis false outright there, a choice decided)
    cdclStats.resolved2++
    work.n += 1 + rows.length
    costs.unfoldRows += rows.length
    const fast = rows.length > 60 ? refuteFast(rows) : undefined
    if (fast?.kind === 'refuted') return {leaf: fast.steps}
    const out = solve(rows)
    if (out.kind === 'refuted') return {leaf: out.steps}
    cdclStats.unfoldWhy = 'refute'
    return undefined
  }
  return go(top)
}
