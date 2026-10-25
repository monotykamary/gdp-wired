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
import {cellPair, late, leafRowsOf, logged, nearOf, openAt, pairedKeys, queryHook, rowsAt, unitAtoms, type Outcome} from './prove.ts'
import {Clausal, Reader, type Row, namesOf} from './reader.ts'
import {Simplex} from './simplex.ts'

// A derivation's own inputs: the rows it reads, in order, and the steps renumbered to them.
function localize(rows: {lin: Lin}[], steps: Step[]): {inputs: Lin[], steps: Step[], from: number[]} {
  const inputs: Lin[] = [], at = new Map<number, number>(), from: number[] = []
  const out = steps.map(st => {
    if (st.kind !== 'input') return st
    let j = at.get(st.index)
    if (j === undefined) { j = inputs.length; at.set(st.index, j); inputs.push(rows[st.index]!.lin); from.push(st.index) }
    return {...st, index: j}
  })
  return {inputs, steps: out, from}
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
// (with opts.dag, a leaf also has each input's hypothesis, -1 for a row of no hypothesis, and its clause's literals)
// (in the clausal mode, a leaf may be a clause of a hypothesis', `hyp` its index: its literals, as a leaf's, can't all hold)
type DagNode = {inputs: Lin[], steps: Step[], src?: number[], lits?: [Lin, boolean][]} | {res: [number, number], on: Lin} | {hyp: number, lits: [Lin, boolean][]}
// A refutation's DAG (opts.dag, with model): its nodes and the empty clause's, for interpolants read off it
// (core/interp.ts's fromDag) instead of the tree it unfolds to.
export type Dag = {nodes: DagNode[], top: number}
// (the clausal mode's: `id` its index, a pair (x, v) coded 2·id + v; `hp` its place in the heap; `cond` whether a
// decision may take it)
type Var = {name: string, lin: Lin, terms: [string, number][], col: boolean, quiet?: boolean, id: number, hp?: number, cond?: boolean, val?: boolean | undefined, level: number, reason?: number | undefined, at: number, act: number, phase: boolean,
  bj?: number[], bjAt?: number, bsig?: number, bver?: number, sj?: (number | undefined)[], sx?: Simplex, pair?: boolean}
type Clause = {lits: Map<string, boolean>, node: number, input?: boolean}
// GDP_CDCL_LP=0: each node solved by elimination alone (no simplex); GDP_CDCL_FILL (8): the simplex's tableau begun
// again past this many entries a row the node reads (research/step's comparisons).
const lpFill = Number(env.GDP_CDCL_FILL ?? 8), lpGrow = Number(env.GDP_CDCL_GROW ?? 4), lpBase = Number(env.GDP_CDCL_BASE ?? 500), lpGreedy = Number(env.GDP_CDCL_GREEDY ?? 200), useLp = env.GDP_CDCL_LP !== '0', verify = env.GDP_CDCL_VERIFY === '1'
// Counters research/step reads (times only while `on`).
export const cdclStats = {on: false, runs: 0, proven: 0, conflicts: 0, decisions: 0, solveMs: 0, rowsMs: 0, coreMs: 0, unfoldMs: 0, leaves: 0, resolved: 0, coreSize: 0, pathSize: 0, lpMisses: 0, resolved2: 0, unfoldWhy: '', orderMs: 0, boundMs: 0, openMisses: 0, lpMs: 0, lpUnknown: 0, fmCalls: 0, pivots: 0, lpRebuilds: 0, lpRows: 0, lpNnz: 0, lpVars: 0, lpLoad: 0, nodes: 0, boundRounds: 0}

// `opts.model`: only whether the goal has a model is wanted (core/bmc.ts): a refutation isn't unfolded into a tree, its
// outcome `unknown` with `why` REFUTED; each decision's phase is the simplex's point's (phaseAtPoint); past `opts.wall` (wall time) the search stops as past its budget.
// `opts.core`, with `model`: a refutation's outcome also names the hypotheses its leaves read (`core`, their indices in
// goal.hyps): those alone have no model (each leaf's rows are those hypotheses' facts at its decisions, or rows true of
// any value: the trail's atoms, the naturals, the term columns' definitions), as core/infer.ts's join reads it.
export const REFUTED = 'refuted, not unfolded'
export type Refuted = Outcome & {core?: number[], dag?: Dag, assumed?: number[]}
export type CdclOptions = {maxLeaves?: number, model?: boolean, core?: boolean, dag?: boolean, clausal?: boolean, sideOf?: (hyp: number) => number, quiet?: (name: string) => boolean}
export function growCdcl(goal: Goal, root: Path, budget: {nodes: number, until?: number}, opts: CdclOptions & {wall?: number} = {}): Outcome {
  const go = () => cdclSession(goal, root, opts).run(budget, opts.wall)
  return queryHook.on && !queryHook.depth ? logged(opts.model ? 'model' : 'cdcl', goal, go) : go()
}
// A search kept from one run to the next (core/bmc.ts's deeper goals, core/unroll.ts's sessions): its atoms, their
// activities and phases, its learned clauses and the simplex's tableau. Between runs the caller may add hypotheses to the
// goal (goal.hyps grows; none is taken away), so every clause learned stays a consequence of the goal. A run may assume
// atoms (`assume`, each decided first, at a level of its own, in order; gen/chc5-pdr's): where the search learns one false
// the run ends refuted (REFUTED), as where nothing is assumed and the goal is refuted; given a list, the refutation names
// the assumptions it needed (`assumed`, their indices, MiniSat's analyzeFinal), and with `dag` its DAG ends in the
// clause of those assumptions. Each run's own budget: nodes, `until` on the counted clock, `wall`.
// `quiet`, with `model`: names read only as decisions (a session's selectors): an atom over one of them alone brings no
// row (the simplex and the elimination never see it).
// `clausal`, with `model`: the goal read as clauses (reader.ts's Clausal) in place of the kernel's reading: unit
// propagation over them, the rows at a node the trail's atoms and their names' naturals, a decision an atom or gate of a
// clause no literal satisfies yet (the most active), a model where every clause is satisfied and the rows have an
// integer point. Where the goal reads what the clauses don't, the kernel's reading as before. `sideOf` colors gates and
// columns for interpolation (by the hypothesis that wrote them).
export function cdclSession(goal: Goal, root: Path, opts: CdclOptions = {}) {
  let until = Infinity, budget: {nodes: number, until?: number} = {nodes: 0}, wall: number | undefined, assumed: [string, boolean][] = [], listed = false
  // (the first assumption not known to hold: those before it held when last looked at, and an assumption taken back
  // brings it down to its own; each assumption's index by name)
  let aq = 0, aqOf = new Map<string, number>()
  const st = cdclStats, timing = st.on
  const t = <T>(f: () => T, add: (ms: number) => void): T => { if (!timing) return f(); const t0 = performance.now(); try { return f() } finally { add(performance.now() - t0) } }
  st.runs++
  const vars = new Map<string, Var>(), trail: string[] = [], levels: number[] = []
  // The clausal mode: the hypotheses as clauses (each clause a leaf of the DAG), how many literals of each input clause
  // hold and how many input clauses none satisfies; the variables by activity (a heap), and those found read by
  // satisfied clauses alone at a level (out of the heap until that level is taken back).
  let clausal = !!(opts.clausal && opts.model), enc = clausal ? new Clausal(opts.sideOf) : undefined, fed = 0, dead = -1, unread = false, lowAt = 0
  if (enc) for (; fed < goal.hyps.length; fed++) if (!enc.add(goal.hyps[fed]!, fed)) { clausal = false; enc = undefined; fed = 0; break }
  // (by a pair's code, 2·id + v: whether it holds, `vals[id]` 1 true, 2 false, 0 open; the clauses watching it; the input
  // clauses that have it; a gate's clauses needed where it holds; each clause's pairs by code, the first two watched, and
  // its gate's pair, or -1)
  const heap: Var[] = [], byId: Var[] = [], vals: number[] = []
  // (relevance, top-down: a hypothesis' own clauses' variables at level 0, a gate's clauses' where the gate is relevant
  // and holds the value that needs them; `rel` the level a variable became relevant at, or -1, `relStack` in order)
  const rel: number[] = [], relStack: number[] = []
  const wl: number[][] = [], ownBy: number[][] = [], cls: Int32Array[] = [], oc: number[] = []
  // (each hypothesis' input clauses; those of a hypothesis retired, read no more)
  const byHyp: number[][] = [], retired: boolean[] = []
  const holds = (c: number) => vals[c >> 1] === 2 - (c & 1), opposed = (c: number) => vals[c >> 1] === 1 + (c & 1)
  const heapUp = (i: number) => { const x = heap[i]!; while (i > 0) { const p = (i - 1) >> 1, y = heap[p]!; if (y.act >= x.act) break; heap[i] = y; y.hp = i; i = p } heap[i] = x; x.hp = i }
  const heapDown = (i: number) => {
    const x = heap[i]!, n = heap.length
    for (;;) { let c = 2 * i + 1; if (c >= n) break; if (c + 1 < n && heap[c + 1]!.act > heap[c]!.act) c++; if (heap[c]!.act <= x.act) break; heap[i] = heap[c]!; heap[i]!.hp = i; i = c }
    heap[i] = x; x.hp = i
  }
  const heapIn = (x: Var) => { if (!x.cond || rel[x.id]! < 0 || (x.hp !== undefined && x.hp >= 0)) return; x.hp = heap.length; heap.push(x); heapUp(x.hp) }
  const heapPop = () => { const top = heap[0]!, end = heap.pop()!; top.hp = -1; if (heap.length) { heap[0] = end; end.hp = 0; heapDown(0) } }
  let sx = useLp ? new Simplex() : undefined
  if (sx && clausal) sx.greedy = lpGreedy
  const nodes: DagNode[] = [], clauses: Clause[] = [], occ = new Map<string, number[]>()
  // (with opts.core: each leaf's hypotheses, by node; the hypothesis each row at this node came from)
  const leafHyps = new Map<number, number[]>(), wantCore = !!(opts.core && opts.model), wantDag = !!(opts.dag && opts.model)
  const hypsOf = (rs: Row[]): number[] => {
    return reader.hypsOf(rs)
  }
  let inc = 1
  // An atom as a variable: the stored form is the one whose canonical text is the variable's name (the smaller).
  const ensure = (lin: Lin): string => {
    const key = keyOf(lin)
    if (!vars.has(key)) {
      const flip = key !== canon(lin), stored = flip ? atomOf(lin, false).lin : lin, terms = Object.entries(stored).filter(([x0]) => x0 !== '1')
      const x: Var = {name: key, lin: stored, terms, col: terms.some(([x0]) => x0.startsWith('⟦')), id: byId.length, level: -1, at: -1, act: 0, phase: !flip}
      byId.push(x); vals.push(0); rel.push(-1)
      if (opts.model && terms.length === 1 && (opts.quiet?.(terms[0]![0]) || (clausal && terms[0]![0].startsWith('τ')))) x.quiet = true
      vars.set(key, x)
      if (clausal) heapIn(x)
    }
    return key
  }
  // Each candidate form's variable (none for a constant form), and the node it was last met at (the candidates told
  // apart by form, as a set of forms would).
  const recs = new WeakMap<Lin, {x: Var | undefined, seen: number}>()
  const recOf = (lin: Lin) => { let r = recs.get(lin); if (!r) recs.set(lin, (r = {x: namesOf(lin).length > 0 ? vars.get(ensure(lin)) : undefined, seen: 0})); return r }
  let candGen = 0, colsOn = 0, pairsChanged = 0
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
  // The root's own decisions are level 0, with no reason: they stay in every clause (the tree starts below them).
  const rootNames = new Set<string>(), stamps: number[] = []
  let stampN = 0
  for (const [key, a] of root) {
    const name = ensure(a.lin), x = vars.get(name)!, val = name === key ? a.holds : !a.holds
    x.val = val; x.level = 0; x.at = trail.length; stamps[x.at] = ++stampN; trail.push(name); rootNames.add(name)
    if (x.col) colsOn++
  }
  const reader = new Reader(clausal ? {name: goal.name, hyps: []} : goal, {
    get: name => vars.get(name), stamp: at => stamps[at]!, size: () => trail.length,
    lin: at => { const name = trail[at]!, x = vars.get(name)!; return {name, lin: x.lin, holds: x.val!} },
    quiet: at => !!vars.get(trail[at]!)!.quiet,
  })
  let last = goal.hyps.length - 1
  const near = nearOf(goal)
  const decidedLin = (lin: Lin) => vars.get(keyOf(lin))?.val !== undefined
  const fixed = trail.length
  const level = () => levels.length
  const pathOf = (): Path => new Map(trail.map(name => { const x = vars.get(name)!; return [name, {lin: x.lin, holds: x.val!}] }))
  const assign = (name: string, val: boolean, reason?: number) => {
    const x = vars.get(name)!
    lowAt = Math.min(lowAt, trail.length)
    x.val = val; x.level = level(); x.at = trail.length; x.phase = val; stamps[x.at] = ++stampN
    x.reason = reason
    trail.push(name)
    if (x.col) colsOn++
    if (x.pair) pairsChanged++
    if (!clausal) { reader.touch(name); return }
    vals[x.id] = val ? 1 : 2
    if (rel[x.id]! >= 0) activate(x.id)
  }
  // A variable relevant (at this level), and, where it is a gate with a value, the clauses that value needs: their
  // variables relevant in turn.
  const relevant = (id: number) => {
    if (rel[id]! >= 0) return
    rel[id] = levels.length; relStack.push(id); heapIn(byId[id]!)
    if (vals[id]) activate(id)
  }
  const activate = (id0: number) => {
    for (const todo = [id0]; todo.length;) {
      const id = todo.pop()!, own = ownBy[2 * id + (vals[id] === 1 ? 1 : 0)]
      if (!own) continue
      for (let i = 0; i < own.length; i++) {
        const ci = own[i]!
        if (retired[ci]) continue
        const c = cls[ci]!
        costs.scan += 1 + (c.length >> 2)
        for (let j = 0; j < c.length; j++) { const y = c[j]! >> 1; if (rel[y]! < 0) { rel[y] = levels.length; relStack.push(y); heapIn(byId[y]!); if (vals[y]) todo.push(y) } }
      }
    }
  }
  const undoTo = (l: number) => {
    const keep = levels[l] ?? trail.length, undone: Var[] = []
    while (trail.length > Math.max(keep, fixed)) {
      const name = trail.pop()!, x = vars.get(name)!, q = aqOf.get(name)
      if (clausal) { vals[x.id] = 0; undone.push(x) }
      x.val = undefined; x.level = -1; x.reason = undefined; if (x.col) colsOn--; if (x.pair) pairsChanged++; if (!clausal) reader.touch(name)
      if (q !== undefined && q < aq) aq = q
    }
    lowAt = Math.min(lowAt, trail.length)
    levels.length = l
    if (clausal) {
      while (relStack.length && rel[relStack.at(-1)!]! > l) rel[relStack.pop()!] = -1
      for (const x of undone) heapIn(x)
    }
  }
  const addClause = (lits: Map<string, boolean>, node: number): number => {
    clauses.push({lits, node})
    const i = clauses.length - 1
    if (clausal) { watches(i); return i }
    for (const [name, pos] of lits) { const key = `${name}=${pos}`; let xs = occ.get(key); if (!xs) occ.set(key, (xs = [])); xs.push(i) }
    return i
  }
  // The clausal mode's watches: each clause's pairs by code, its first two watched, those that don't hold first, then
  // those that came last on the trail (a learned clause's: its latest two).
  const watches = (ci: number) => {
    const c = Int32Array.from([...clauses[ci]!.lits].map(([name, pos]) => 2 * vars.get(name)!.id + (pos ? 1 : 0)))
    cls[ci] = c; oc[ci] = -1
    if (c.length < 2) return
    const rank = (z: number) => (holds(z) ? byId[z >> 1]!.at : Infinity)
    for (const j of [0, 1]) { let b = j; for (let q = j + 1; q < c.length; q++) if (rank(c[q]!) > rank(c[b]!)) b = q; const t0 = c[j]!; c[j] = c[b]!; c[b] = t0 }
    for (const j of [0, 1]) (wl[c[j]!] ??= []).push(ci, c[1 - j]!)
  }
  // The clausal mode's clauses of the hypotheses not yet taken (each a leaf: its hypothesis and its literals), at level 0:
  // a unit's literal assigned, an empty one the goal refuted, every clause read again by propagation from the trail's
  // start; the variables left out as read by satisfied clauses alone put back.
  const take = () => {
    if (!enc) return
    for (; fed < goal.hyps.length; fed++) if (!enc.add(goal.hyps[fed]!, fed)) { unread = true; break }
    if (!enc.made.length) return
    for (const {lits, hyp, own, out} of enc.made) {
      const m = new Map<string, boolean>()
      for (const l of lits) { const name = ensure(l.lin); m.set(name, !(name === canon(l.lin) ? l.holds : !l.holds)) }
      nodes.push({hyp, lits: [...m].map(([name, pos]) => [vars.get(name)!.lin, pos])})
      // (a variable decided only where some clause reads it as more than a case's atom)
      let j = 0
      for (const name of m.keys()) { const x = vars.get(name)!; if (!x.cond && !(out && j === m.size - 1)) { x.cond = true; heapIn(x) } j++ }
      const ci = addClause(m, nodes.length - 1)
      clauses[ci]!.input = true
      ;(byHyp[hyp] ??= []).push(ci)
      if (own && m.size) { const [name, pos] = m.entries().next().value!, z = 2 * vars.get(name)!.id + (pos ? 1 : 0); oc[ci] = z; (ownBy[z] ??= []).push(ci) }
      let open: string | undefined
      for (const name of m.keys()) if (vars.get(name)!.val === undefined) open = name
      if (!m.size) dead = nodes.length - 1
      else if (m.size === 1 && open !== undefined) assign(open, !m.get(open)!, ci)
      // (a hypothesis' own clause: its variables relevant for good; a gate's, where the gate needs it already)
      if (oc[ci]! < 0 || (rel[oc[ci]! >> 1]! >= 0 && holds(oc[ci]!))) for (const name of m.keys()) relevant(vars.get(name)!.id)
    }
    enc.made = []
    qhead = 0
  }
  // The open variable a decision takes in the clausal mode: the most active relevant one. A clause is needed where it is
  // a hypothesis' own (no gate's), or its gate is relevant and its literal in the clause false; every variable of a
  // needed clause is relevant, so where none is open, every needed clause is satisfied (unit propagation found no
  // conflict), and a model of the needed clauses is a model of the goal.
  const needed = (ci: number) => !retired[ci] && (oc[ci]! < 0 || (rel[oc[ci]! >> 1]! >= 0 && holds(oc[ci]!)))
  const satisfied = (ci: number) => { const c = cls[ci]!; costs.scan += 1 + (c.length >> 2); for (let j = 0; j < c.length; j++) if (opposed(c[j]!)) return true; return false }
  const pickOpen = (): Var | undefined => {
    while (heap.length) {
      const x = heap[0]!
      if (x.val !== undefined || rel[x.id]! < 0) { heapPop(); continue }
      return x
    }
    // (never: GDP_CDCL_VERIFY=1 checks it where a model is about to be answered)
    if (verify) for (let ci = 0; ci < clauses.length; ci++) if (clauses[ci]!.input && needed(ci) && !satisfied(ci)) throw new Error('clausal: a needed clause unsatisfied with no open variable')
    return undefined
  }
  // A point of the rows the simplex is at, where it is integral and meets them all (a model then).
  const pointOf = (lp: Simplex, rows: Row[]): Record<string, number> | undefined => {
    const w: Record<string, number> = {}
    for (const r of rows) for (const n of namesOf(r.lin)) if (!(n in w)) { const j = lp.indexOf(n); if (j === undefined) return undefined; const x = lp.value(j), y = Math.round(x); if (Math.abs(x - y) > 1e-9) return undefined; w[n] = y }
    for (const r of rows) { let x = r.lin['1'] ?? 0; for (const n of namesOf(r.lin)) x += r.lin[n]! * w[n]!; if (x > 0) return undefined }
    return w
  }
  let qhead = 0
  // Unit propagation: a clause whose literals all hold is a conflict (its index); all but one, the last is flipped.
  const propagate = (): number | undefined => {
    // (the clausal mode's, over the watches: a pair that now holds moves its watch to a pair that doesn't, else the clause
    // is unit, its other watched pair's variable flipped, or, that pair holding too, a conflict)
    if (clausal) {
      // (each watch a clause and a blocker, a pair of it that, where it doesn't hold, satisfies the clause untouched)
      while (qhead < trail.length) {
        const x = vars.get(trail[qhead++]!)!, code = 2 * x.id + (x.val ? 1 : 0), ws = wl[code]
        if (!ws) continue
        let n = 0
        for (let i = 0; i < ws.length;) {
          if (opposed(ws[i + 1]!)) { i += 2; continue }
          const ci = ws[i]!, c = cls[ci]!
          n++
          if (retired[ci]) { ws[i] = ws[ws.length - 2]!; ws[i + 1] = ws[ws.length - 1]!; ws.length -= 2; continue }
          if (c[0] === code) { c[0] = c[1]!; c[1] = code }
          const o = c[0]!
          if (opposed(o)) { ws[i + 1] = o; i += 2; continue }
          let j = 2
          while (j < c.length && holds(c[j]!)) j++
          if (j < c.length) { const z = c[j]!; c[j] = code; c[1] = z; (wl[z] ??= []).push(ci, o); ws[i] = ws[ws.length - 2]!; ws[i + 1] = ws[ws.length - 1]!; ws.length -= 2; continue }
          if (!vals[o >> 1]) { assign(byId[o >> 1]!.name, !(o & 1), ci); i += 2; continue }
          costs.scan += n
          return ci
        }
        costs.scan += n
      }
      return undefined
    }
    while (qhead < trail.length) {
      const name = trail[qhead++]!, x = vars.get(name)!, os = occ.get(`${name}=${x.val}`)
      if (!os) continue
      if (clausal) costs.scan += os.length
      for (const ci of os) {
        const c = clauses[ci]!
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
    for (const name of lits.keys()) { const x = vars.get(name)!; x.act += inc; if (x.act > 1e100) { for (const y of vars.values()) y.act *= 1e-100; inc *= 1e-100 } if (clausal && x.hp !== undefined && x.hp >= 0) heapUp(x.hp) }
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
  const leafNode = (w: Iterable<string>, inputs: Lin[], steps: Step[], extra?: [string, boolean], hyps?: number[], src?: number[]): Clause => {
    nodes.push(src ? {inputs, steps, src} : {inputs, steps})
    if (hyps) leafHyps.set(nodes.length - 1, hyps)
    st.leaves++
    const lits = new Map<string, boolean>()
    for (const name of w) if (!rootNames.has(name)) lits.set(name, vars.get(name)!.val!)
    if (extra) lits.set(extra[0], extra[1])
    if (src) (nodes.at(-1) as {lits?: [Lin, boolean][]}).lits = [...lits].map(([name, val]) => [vars.get(name)!.lin, val])
    st.coreSize += lits.size
    return {lits, node: nodes.length - 1}
  }
  // A theory conflict at the trail: the leaf at its core, the reasons of the rows its derivation reads.
  const leafAt = (rows: Row[], steps: Step[]): Clause => t(() => {
    const w = new Set<string>()
    for (const s of steps) if (s.kind === 'input') for (const name of rows[s.index]!.w) w.add(name)
    st.pathSize += trail.length - fixed
    const local = localize(rows, steps)
    return leafNode(w, local.inputs, local.steps, undefined, wantCore ? hypsOf(steps.flatMap(s => (s.kind === 'input' ? [rows[s.index]!] : []))) : undefined, wantDag ? local.from.map(i => reader.srcOf(rows[i]!) ?? -1) : undefined)
  }, ms => { st.coreMs += ms })
  // Bound propagation's reasons, made when conflict analysis reads them: the atom's bounds (single-variable rows at the
  // trail then) and its other side refute each other, a leaf at the bounds' reasons with that side decided.
  const pending = new Map<number, {w: Set<string>, used: Lin[], name: string, val: boolean, hyps?: number[], src?: number[]}>()
  const materialize = (ci: number) => t(() => {
    const b = pending.get(ci)!, x = vars.get(b.name)!, c = clauses[ci]!
    pending.delete(ci)
    const local = [...b.used.map(lin => ({lin, label: ''})), {lin: atomOf(x.lin, !b.val).lin, label: ''}]
    const s = solve(local)
    if (s.kind !== 'refuted') throw new Error('a bound propagation its bounds do not refute')
    const loc = localize(local, s.steps), made = leafNode(b.w, loc.inputs, loc.steps, [b.name, !b.val], b.hyps, b.src && loc.from.map(i => b.src![i] ?? -1))
    c.lits = made.lits; c.node = made.node
  }, ms => { st.coreMs += ms })
  const levelsOf = (c: Clause) => {
    let top = -1, here = 0, latest: string | undefined, at = -1
    for (const name of c.lits.keys()) {
      const x = vars.get(name)!
      if (x.level > top) { top = x.level; here = 1; latest = name; at = x.at } else if (x.level === top) { here++; if (x.at > at) { latest = name; at = x.at } }
    }
    let below = 0
    for (const name of c.lits.keys()) { const l = vars.get(name)!.level; if (name !== latest && l > below) below = l }
    return {top, here, latest, below}
  }
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
  let restartAt = 32, nRestart = 0, sinceRestart = 0, free = 0
  const batch = Number(env.GDP_CDCL_BATCH ?? 16)
  const stuck = (kind: 'sat' | 'unknown', why: string, extra: {witness?: Record<string, number>} = {}): Outcome => ({stuck: kind, path: pathOf(), why, ...extra})
  const run = (b: {nodes: number, until?: number}, w?: number, assume?: Lin | Lin[]): Outcome => {
    budget = b; until = b.until ?? Infinity; wall = w; last = goal.hyps.length - 1
    restartAt = 32; nRestart = 0; sinceRestart = 0
    listed = Array.isArray(assume)
    assumed = (assume === undefined ? [] : Array.isArray(assume) ? assume : [assume]).map(lin => { const name = ensure(lin); return [name, name === canon(lin)] as [string, boolean] })
    // (a run before this one may have left decisions: given a list, the levels whose decisions are its first
    // assumptions in order stay, each assumption before them holding below them already, so the rows they read stand;
    // none where the clausal mode has hypotheses to take)
    let keep = 0
    if (listed && !(enc && fed < goal.hyps.length)) for (let l = 0, q = 0; l < levels.length; l++) {
      const d = trail[levels[l]!]!
      for (let y = q < assumed.length ? vars.get(assumed[q]![0])! : undefined; y && y.val === assumed[q]![1] && y.at < levels[l]!; y = ++q < assumed.length ? vars.get(assumed[q]![0])! : undefined);
      if (q >= assumed.length || assumed[q]![0] !== d || vars.get(d)!.val !== assumed[q]![1]) break
      q++; keep = l + 1
    }
    aq = 0; aqOf = new Map(assumed.map(([name], q) => [name, q]))
    undoTo(keep); qhead = Math.min(qhead, trail.length)
    take()
    if (unread) return {stuck: 'unknown', path: new Map(), why: 'a hypothesis the clauses do not read'}
    if (dead >= 0) return {stuck: 'unknown', path: new Map(), why: REFUTED, ...(listed ? {assumed: []} : {}), ...(wantDag ? {dag: {nodes, top: dead}} : {})} as Refuted
    return queryHook.on && !queryHook.depth ? logged(opts.model ? 'model' : 'cdcl', goal, search) : search()
  }
  // The assumptions a falsified one rests on: the decisions its reasons reach, each reason materialized where it is a
  // bound's (every decision on the trail is an assumption here: the search decides nothing else until they all hold).
  const final = (q0: number): number[] => {
    const at = aqOf, out = new Set([q0]), seen = new Set<string>(), todo = [assumed[q0]![0]]
    while (todo.length) {
      const name = todo.pop()!, x = vars.get(name)!
      if (seen.has(name) || x.level <= 0) continue
      seen.add(name)
      if (x.reason === undefined) { const q = at.get(name); if (q !== undefined) out.add(q); continue }
      if (clauses[x.reason]!.node < 0) materialize(x.reason)
      for (const w of clauses[x.reason]!.lits.keys()) if (w !== name) todo.push(w)
    }
    return [...out].sort((a, b) => a - b)
  }
  // With `dag`: the falsified assumption's reason resolved with the reasons of every literal in it that is no
  // assumption, latest first, down to a clause of assumptions alone (the DAG's last node).
  const finalDag = (q0: number): number => {
    const x0 = vars.get(assumed[q0]![0])!
    if (clauses[x0.reason!]!.node < 0) materialize(x0.reason!)
    let c = clauses[x0.reason!]!
    for (;;) {
      let best: Var | undefined
      for (const name of c.lits.keys()) { if (aqOf.has(name)) continue; const y = vars.get(name)!; if (!best || y.at > best.at) best = y }
      if (!best) return c.node
      c = resolveOn(c, best.name)
    }
  }
  const search = (): Outcome => {
    for (;;) {
      if (++budget.nodes > 200_000 || late(until) || (wall !== undefined && performance.now() > wall)) return stuck('unknown', budget.nodes > 200_000 ? 'nodes' : 'time')
      let conflict: Clause | undefined
      const ci = propagate()
      let open = -1, wrong = -1
      if (ci === undefined) for (; aq < assumed.length; aq++) { const val = vars.get(assumed[aq]![0])!.val; if (val === !assumed[aq]![1]) { wrong = aq; break } if (val === undefined) { open = aq; break } }
      if (ci !== undefined) conflict = clauses[ci]!
      else if (wrong >= 0) return {stuck: 'unknown', path: new Map(), why: REFUTED, ...(listed ? {assumed: final(wrong)} : {}), ...(wantDag ? {dag: {nodes, top: finalDag(wrong)}} : {})} as Refuted
      else if (open >= 0) {
        levels.push(trail.length)
        assign(assumed[open]![0], assumed[open]![1])
        continue
      } else {
        // (the clausal mode: after a node whose rows the simplex met, up to `batch` decisions more before the next node,
        // each its own level, an atom's value the point's: they keep that point, so the rows meet it but where unit
        // propagation brought an atom it doesn't meet, which the next node finds)
        if (free > 0) {
          const x = pickOpen()
          if (x) {
            free--
            if (!x.quiet && sx) phaseAtPoint(x, sx)
            levels.push(trail.length); st.decisions++
            assign(x.name, x.phase)
            continue
          }
        }
        reader.begin()
        st.nodes++
        // The rows, kept from the node before (reader.ts's sync); the forms that came and went: the single-variable
        // ones' bounds now (for bound propagation, `bx`), the simplex's when it next runs (`toAssert`, `toRetract`: a
        // form in and out between its runs never reaches it).
        const rowsR = t(() => (reader.sync(lowAt), lowAt = trail.length, reader.live), ms => { st.rowsMs += ms })
        const full: Constraint[] = rowsR
        const single = (id: number) => reader.form(full[reader.slotOf(id)]!.lin).names.length === 1
        for (const id of reader.left) { if (bxIn.delete(id)) bx.retract(id); if (sx && !toAssert.delete(id)) toRetract.add(id) }
        for (const id of reader.entered) { if (single(id)) { bxIn.add(id); bx.assert(id, full[reader.slotOf(id)]!.lin) } if (sx && !toRetract.delete(id)) toAssert.add(id) }
        if (verify && !clausal) {
          const mine = new Set(rowsR.map(r => canon(r.lin))), theirs = new Set(leafConstraints(goal, pathOf()).map(r => canon(r.lin)))
          if (mine.size !== theirs.size || [...mine].some(x => !theirs.has(x))) throw new Error(`reader.ts's rows differ from kernel.ts's at a node of ${goal.name}`)
        }
        work.n += 1 + full.length
        costs.cdclNodes++; costs.cdclRows += full.length
        // (the elimination below reads term columns' rows only once the trail has an atom about one, as growPlain does)
        const columns = colsOn > 0
        // (the rows read by the elimination, made when it runs, in kernel.ts's order: elimination's choices, and the
        // bounded one's give-up, follow the order it is given)
        let kidx: number[] | undefined, idx: number[] | undefined, rows: Constraint[] | undefined
        const korder = (): number[] => (kidx ??= reader.rows().map(r => reader.slotOf(reader.form(r.lin).id)))
        const plain = (): Constraint[] => {
          if (rows) return rows
          idx = korder().filter(i => columns || !reader.readsColumn(full[i]!.lin))
          return (rows = idx.map(i => full[i]!))
        }
        const at = (i: number) => (i < plain().length ? idx![i]! : full.length + i - plain().length)
        // The candidates, in growPlain's order: the units, the conclusion's open atoms, the hypotheses' near it, the
        // rest, pairs of cells.
        const cands = t(() => {
          if (clausal) { const x = pickOpen(); return x ? [x] : [] }
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
          if (reader.hasCells()) take(openCellsLive())
          return keep
        }, ms => { st.orderMs += ms })
        const open = cands.length > 0
        // Bound propagation: an open atom its variables' bounds (the single-variable rows) decide.
        const tb = timing ? performance.now() : 0
        if (open) {
          let forced = 0
          for (const x of cands) {
            const name = x.name
            if (x.val !== undefined || x.col) continue // (a term column's rows read differently once its choice is decided)
            // (unforced at the bounds it last read, which haven't changed since: unforced still)
            // (no bound has changed since; or a name without any; or no bound it reads has)
            if (x.bver === bx.changes) continue
            if (!x.bj) {
              if (x.bjAt === bx.vars) continue
              x.bjAt = bx.vars
              const bj = x.terms.map(([x0]) => bx.indexOf(x0))
              if (bj.some(j => j === undefined)) continue
              x.bj = bj as number[]
            }
            const bj = x.bj
            let sig = 0
            for (const j of bj) sig += bx.version(j)
            if (x.bsig === sig) { x.bver = bx.changes; continue }
            const side = (val: boolean): number[] | undefined => { // the rows that force the stored atom to `val`
              let sum = x.lin['1'] ?? 0
              const used: number[] = []
              for (let q = 0; q < bj.length; q++) {
                const c = x.terms[q]![1], j = bj[q]!, up = (c > 0) === val, b = up ? bx.high(j) : bx.low(j)
                if (!Number.isFinite(b)) return undefined
                sum += c * b; used.push(reader.slotOf(up ? bx.highWhy(j) : bx.lowWhy(j)))
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
              pending.set(clauses.length - 1, {w, used: used.map(i => full[i]!.lin), name, val, ...(wantCore ? {hyps: hypsOf(used.map(i => rowsR[i]!))} : {}), ...(wantDag ? {src: used.map(i => reader.srcOf(rowsR[i]!) ?? -1)} : {})})
              assign(name, val, clauses.length - 1)
              forced++
              break
            }
            x.bsig = hit ? undefined : sig; x.bver = hit ? undefined : bx.changes
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
            const over = sx.size > (clausal ? lpGrow : 4) * full.length + (clausal ? lpBase : 500) || sx.nnz > lpFill * full.length
            if (over) { sx = new Simplex(); if (clausal) sx.greedy = lpGreedy; st.lpRebuilds++ }
            // (a tableau begun has the rows asserted in kernel.ts's order, which its variables', so Bland's rule, follow)
            if (over || !sx.vars) for (const r of reader.rows()) sx.assert(reader.form(r.lin).id, r.lin)
            else { for (const id of toRetract) sx.retract(id); for (const id of toAssert) sx.assert(id, full[reader.slotOf(id)]!.lin) }
            toAssert.clear(); toRetract.clear()
            const p0 = sx.pivots
            let lp = sx.settle()
            if (lp.kind === 'sat') lp = sx.check()
            if (lp.kind === 'conflict') lp = {kind: 'conflict', rows: lp.rows.map(id => reader.slotOf(id))}
            costs.pivots += sx.pivots - p0
            if (timing) { st.lpMs += performance.now() - t0; st.pivots += sx.pivots - p0; st.lpRows = sx.size; st.lpNnz = sx.nnz; st.lpVars = sx.vars; st.lpLoad = full.length; if (lp.kind === 'unknown') st.lpUnknown++ }
            if (lp.kind === 'conflict') {
              const support = lp.rows.sort((x, y) => x - y), out = solve(support.map(i => full[i]!))
              if (out.kind === 'refuted') steps = out.steps.map(s => (s.kind === 'input' ? {...s, index: support[s.index]!} : s))
              else st.lpMisses++
            }
            lpSat = lp.kind === 'sat'
            if (steps || (open && lp.kind === 'sat')) return
            // (the clausal mode, every clause satisfied: the simplex's point, where it is integral, is a model)
            if (clausal && !open && lpSat) { const w = pointOf(sx, rowsR); if (w) { verdict = {kind: 'sat', witness: w}; return } }
          }
          st.fmCalls++
          const rows = plain()
          if (open && rows.length > 60) { const fast = refuteFast(rows); if (fast?.kind === 'refuted') steps = fast.steps.map(s => (s.kind === 'input' ? {...s, index: at(s.index)} : s)) }
          if (!steps) {
            verdict = open && rows.length > 60 ? solve(rows, 2 * rows.length) : solve(rows)
            if (verdict.kind === 'refuted') steps = verdict.steps.map(s => (s.kind === 'input' ? {...s, index: at(s.index)} : s))
          }
          if (!steps && open && !columns && full.length > rows.length) { const k = korder(), fast = refuteFast(k.map(i => full[i]!)); if (fast?.kind === 'refuted') steps = fast.steps.map(s => (s.kind === 'input' ? {...s, index: k[s.index]!} : s)) }
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
          if (!pick && !clausal) {
            const p = pathOf(), more = openAt(goal, p, rowsAt(goal, p)).find(lin => Object.keys(lin).some(key => key !== '1') && !decidedLin(lin))
            if (more) { st.openMisses++; pick = ensure(more) }
          }
          if (!pick) return verdict?.kind === 'sat' ? stuck('sat', 'a model', {witness: verdict.witness}) : stuck('unknown', 'no split')
          levels.push(trail.length)
          st.decisions++
          assign(pick, vars.get(pick)!.phase)
          if (clausal && lpSat) free = batch
          continue
        }
      }
      // Conflict analysis.
      st.conflicts++; sinceRestart++; free = 0
      // (a clause's latest level, how many of its literals are at it, the latest of those on the trail, and the latest
      // level of the rest: one pass)
      let c = conflict
      if (clausal) {
        // (the same resolutions, in one pass down the trail: the clause kept as it is resolved, its literals at its
        // latest level counted, each step the latest of them on the trail)
        const lits = new Map(c.lits)
        let node = c.node, {top, here} = levelsOf(c), p = trail.length - 1
        if (top < level()) { undoTo(top); qhead = trail.length; p = trail.length - 1 }
        while (lits.size && !(top > 0 && here === 1)) {
          while (p >= 0 && !(lits.has(trail[p]!) && vars.get(trail[p]!)!.level === top)) p--
          const name = trail[p]!, x = vars.get(name)!
          if (top > 0 && x.reason === undefined) break
          const r = clauses[x.reason!]!
          if (r.node < 0) materialize(x.reason!)
          nodes.push({res: lits.get(name)! ? [node, r.node] : [r.node, node], on: x.lin})
          st.resolved++
          node = nodes.length - 1
          lits.delete(name); here--
          for (const [w, q] of r.lits) if (w !== name && !lits.has(w)) { lits.set(w, q); if (vars.get(w)!.level === top) here++ }
        }
        c = {lits, node}
      }
      for (;;) {
        if (!c.lits.size) {
          if (opts.model) {
            if (wantDag) return {stuck: 'unknown', path: new Map(), why: REFUTED, dag: {nodes, top: c.node}} as Refuted
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
        const {top, here, latest} = levelsOf(c)
        if (top < level()) { undoTo(top); qhead = trail.length }
        if (top === 0) { c = resolveOn(c, latest!); continue }
        if (here === 1) break
        if (vars.get(latest!)!.reason === undefined) break
        c = resolveOn(c, latest!)
      }
      const {top, here, latest: uip, below} = levelsOf(c)
      bump(c.lits)
      const learned = addClause(c.lits, c.node)
      if (here !== 1) { undoTo(Math.max(0, top - 1)); qhead = Math.min(qhead, trail.length); continue }
      undoTo(below)
      qhead = trail.length
      assign(uip!, !c.lits.get(uip!)!, learned)
      if (sinceRestart >= restartAt) { sinceRestart = 0; restartAt = 32 * luby(++nRestart); undoTo(0); qhead = Math.min(qhead, trail.length) }
    }
  }
  // A hypothesis read no more (clausal mode): its clauses out of propagation and of what a decision reads. Sound where
  // nothing else reads its gates (the caller's `sideOf` gives it gates of its own) and nothing later asks it to hold:
  // the clauses learned from it stay consequences of the goal with its gates' definitions, which any model of the rest
  // extends to (a gate its formula's value).
  const retire = (hyp: number) => { for (const ci of byHyp[hyp] ?? []) retired[ci] = true }
  return {run, retire}
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
    if ('hyp' in n) return undefined // (the clausal mode's: never unfolded, a model alone wanted there)
    if (++leaves > maxLeaves || late(until)) { cdclStats.unfoldWhy = leaves > maxLeaves ? 'leaves' : 'time'; return undefined }
    reader.begin()
    const src: (number | [string, string])[] = [], rows = reader.leafRows(src)
    costs.unfoldRows += rows.length
    // (the rows the leaf's derivation reads kept with it: prove.ts's leafRowsOf)
    const noted = (leaf: Step[]): Tree => {
      const t = {leaf}, at = new Map<number, {lin: Lin, src: number | [string, string]}>()
      for (const st of leaf) if (st.kind === 'input' && st.index < rows.length) at.set(st.index, {lin: rows[st.index]!.lin, src: src[st.index]!})
      leafRowsOf.set(t, {n: rows.length, at})
      return t
    }
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
    if (steps.length === n.steps.length && checkRefutation(rows, steps)) return noted(steps)
    // (a row a longer path reads otherwise: a hypothesis false outright there, a choice decided)
    cdclStats.resolved2++
    work.n += 1 + rows.length
    costs.unfoldRows += rows.length
    const fast = rows.length > 60 ? refuteFast(rows) : undefined
    if (fast?.kind === 'refuted') return noted(fast.steps)
    const out = solve(rows)
    if (out.kind === 'refuted') return noted(out.steps)
    cdclStats.unfoldWhy = 'refute'
    return undefined
  }
  return go(top)
}
