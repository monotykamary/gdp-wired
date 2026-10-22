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
import {type Constraint, type Lin, type Step, refuteFast, solve, work} from '../core/solver.ts'
import {checkRefutation} from '../core/check.ts'
import {type Goal, type Path, type Tree, atomOf, canon, canonFlip, isCell, isMonomial, leafConstraints} from './kernel.ts'
import {clock, nearOf, openAt, openCells, rowsAt, unitAtoms, type Outcome} from './prove.ts'
import {Reader, type Row, namesOf} from './reader.ts'
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
// --- the search -----------------------------------------------------------------------------------------------------------

// A node of the refutation: a leaf (its decisions, by variable, and a derivation over the rows at its path) or a
// resolution of two earlier nodes on a variable (`res[0]` the one with the atom as stored true, `res[1]` false).
type DagNode = {inputs: Lin[], steps: Step[]} | {res: [number, number], on: Lin}
type Var = {lin: Lin, terms: [string, number][], val?: boolean, level: number, reason?: number, at: number, act: number, phase: boolean}
type Clause = {lits: Map<string, boolean>, node: number}
// GDP_CDCL_LP=0: each node solved by elimination alone (no simplex); GDP_CDCL_FILL (8): the simplex's tableau begun
// again past this many entries a row the node reads (research/step's comparisons).
const env = (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env ?? {}
const lpFill = Number(env.GDP_CDCL_FILL ?? 8), useLp = env.GDP_CDCL_LP !== '0', verify = env.GDP_CDCL_VERIFY === '1'
// Counters research/step reads (times only while `on`).
export const cdclStats = {on: false, runs: 0, proven: 0, conflicts: 0, decisions: 0, solveMs: 0, rowsMs: 0, coreMs: 0, unfoldMs: 0, leaves: 0, resolved: 0, coreSize: 0, pathSize: 0, lpMisses: 0, resolved2: 0, unfoldWhy: '', orderMs: 0, boundMs: 0, openMisses: 0, lpMs: 0, lpUnknown: 0, fmCalls: 0, pivots: 0, lpRebuilds: 0, lpRows: 0, lpNnz: 0, lpVars: 0, lpLoad: 0}

export function growCdcl(goal: Goal, root: Path, budget: {nodes: number, until?: number}, opts: {maxLeaves?: number} = {}): Outcome {
  const until = budget.until ?? Infinity, st = cdclStats, timing = st.on
  const t = <T>(f: () => T, add: (ms: number) => void): T => { if (!timing) return f(); const t0 = performance.now(); try { return f() } finally { add(performance.now() - t0) } }
  st.runs++
  const vars = new Map<string, Var>(), trail: string[] = [], levels: number[] = []
  let sx = useLp ? new Simplex() : undefined
  const nodes: DagNode[] = [], clauses: Clause[] = [], occ = new Map<string, number[]>()
  let inc = 1
  // An atom as a variable: the stored form is the one whose canonical text is the variable's name (the smaller).
  const ensure = (lin: Lin): string => {
    const a = canon(lin), b = canonFlip(lin), flip = b < a, key = flip ? b : a
    if (!vars.has(key)) { const stored = flip ? atomOf(lin, false).lin : lin; vars.set(key, {lin: stored, terms: Object.entries(stored).filter(([x0]) => x0 !== '1'), level: -1, at: -1, act: 0, phase: !flip}) }
    return key
  }
  // The root's own decisions are level 0, with no reason: they stay in every clause (the tree starts below them).
  const rootNames = new Set<string>(), stamps: number[] = []
  let stampN = 0
  for (const [key, a] of root) {
    const name = ensure(a.lin), x = vars.get(name)!, val = name === key ? a.holds : !a.holds
    x.val = val; x.level = 0; x.at = trail.length; stamps[x.at] = ++stampN; trail.push(name); rootNames.add(name)
  }
  const reader = new Reader(goal, {
    get: name => vars.get(name), stamp: at => stamps[at]!, size: () => trail.length,
    lin: at => { const name = trail[at]!, x = vars.get(name)!; return {name, lin: x.lin, holds: x.val!} },
  })
  const last = goal.hyps.length - 1, near = nearOf(goal)
  const decidedLin = (lin: Lin) => vars.get(canon(lin))?.val !== undefined || vars.get(canonFlip(lin))?.val !== undefined
  const fixed = trail.length
  const level = () => levels.length
  const pathOf = (): Path => new Map(trail.map(name => { const x = vars.get(name)!; return [name, {lin: x.lin, holds: x.val!}] }))
  const assign = (name: string, val: boolean, reason?: number) => {
    const x = vars.get(name)!
    x.val = val; x.level = level(); x.at = trail.length; x.phase = val; stamps[x.at] = ++stampN
    if (reason === undefined) delete x.reason; else x.reason = reason
    trail.push(name)
  }
  const undoTo = (l: number) => {
    const keep = levels[l] ?? trail.length
    while (trail.length > Math.max(keep, fixed)) { const x = vars.get(trail.pop()!)!; delete x.val; x.level = -1; delete x.reason }
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
  const leafNode = (w: Iterable<string>, inputs: Lin[], steps: Step[], extra?: [string, boolean]): Clause => {
    nodes.push({inputs, steps})
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
    return leafNode(w, local.inputs, local.steps)
  }, ms => { st.coreMs += ms })
  // Bound propagation's reasons, made when conflict analysis reads them: the atom's bounds (single-variable rows at the
  // trail then) and its other side refute each other, a leaf at the bounds' reasons with that side decided.
  const pending = new Map<number, {w: Set<string>, used: Lin[], name: string, val: boolean}>()
  const materialize = (ci: number) => t(() => {
    const b = pending.get(ci)!, x = vars.get(b.name)!, c = clauses[ci]!
    pending.delete(ci)
    const local = [...b.used.map(lin => ({lin, label: ''})), {lin: atomOf(x.lin, !b.val).lin, label: ''}]
    const s = solve(local)
    if (s.kind !== 'refuted') throw new Error('a bound propagation its bounds do not refute')
    const loc = localize(local, s.steps), made = leafNode(b.w, loc.inputs, loc.steps, [b.name, !b.val])
    c.lits = made.lits; c.node = made.node
  }, ms => { st.coreMs += ms })
  const luby = (i: number): number => { let n = 1; while ((1 << n) - 1 < i + 1) n++; return (1 << n) - 1 === i + 1 ? 1 << (n - 1) : luby(i + 1 - (1 << (n - 1))) }
  let restartAt = 32, nRestart = 0, sinceRestart = 0
  const stuck = (kind: 'sat' | 'unknown', why: string, extra: {witness?: Record<string, number>} = {}): Outcome => ({stuck: kind, path: pathOf(), why, ...extra})
  for (;;) {
    if (++budget.nodes > 200_000 || clock() > until) return stuck('unknown', budget.nodes > 200_000 ? 'nodes' : 'time')
    let conflict: Clause | undefined
    const ci = propagate()
    if (ci !== undefined) conflict = clauses[ci]!
    else {
      reader.begin()
      const rowsR = t(() => reader.rows(), ms => { st.rowsMs += ms })
      const full: Constraint[] = rowsR
      if (verify) {
        const mine = new Set(rowsR.map(r => canon(r.lin))), theirs = new Set(leafConstraints(goal, pathOf()).map(r => canon(r.lin)))
        if (mine.size !== theirs.size || [...mine].some(x => !theirs.has(x))) throw new Error(`reader.ts's rows differ from kernel.ts's at a node of ${goal.name}`)
      }
      work.n += 1 + full.length
      // (the elimination below reads term columns' rows only once the trail has an atom about one, as growPlain does)
      let columns = false
      for (let i = 0; i < trail.length && !columns; i++) for (const key in vars.get(trail[i]!)!.lin) if (key.startsWith('⟦')) { columns = true; break }
      const idx = columns ? undefined : full.flatMap((r, i) => (namesOf(r.lin).some(key => key.startsWith('⟦')) ? [] : [i]))
      const rows = idx ? idx.map(i => full[i]!) : full, at = (i: number) => (!idx ? i : i < rows.length ? idx[i]! : full.length + i - rows.length)
      // The candidates, in growPlain's order: the units, the conclusion's open atoms, the hypotheses' near it, the
      // rest, pairs of cells.
      const cands = t(() => {
        const out: Lin[] = [...unitAtoms(goal)]
        if (last >= 0) reader.open(last, out)
        for (let i = 0; i < last; i++) if (near[i]) reader.open(i, out)
        for (let i = 0; i < last; i++) if (!near[i]) reader.open(i, out)
        if (rows.some(r => namesOf(r.lin).some(isCell))) for (const x of openCells(rows, pathOf())) out.push(x)
        const seen = new Set<Lin>()
        return out.filter(lin => !seen.has(lin) && (seen.add(lin), namesOf(lin).length > 0) && !decidedLin(lin))
      }, ms => { st.orderMs += ms })
      const open = cands.length > 0
      // Bound propagation: an open atom its variables' bounds (the single-variable rows) decide.
      const tb = timing ? performance.now() : 0
      if (open) {
        const lo = new Map<string, [number, number]>(), hi = new Map<string, [number, number]>()
        full.forEach((r, i) => {
          const ks = namesOf(r.lin)
          if (ks.length !== 1) return
          const x0 = ks[0]!, c = r.lin[x0]!, k0 = r.lin['1'] ?? 0
          if (c > 0) { const b = Math.floor(-k0 / c); if (b < (hi.get(x0)?.[0] ?? Infinity)) hi.set(x0, [b, i]) }
          else if (c < 0) { const b = Math.ceil(k0 / -c); if (b > (lo.get(x0)?.[0] ?? -Infinity)) lo.set(x0, [b, i]) }
        })
        let forced = 0
        for (const lin of cands) {
          const name = ensure(lin), x = vars.get(name)!
          if (x.val !== undefined || namesOf(x.lin).some(key => key.startsWith('⟦'))) continue // (a term column's rows read differently once its choice is decided)
          const side = (val: boolean): number[] | undefined => { // the rows that force the stored atom to `val`
            let sum = x.lin['1'] ?? 0
            const used: number[] = []
            for (const [x0, c] of x.terms) {
              const b = (c > 0) === val ? hi.get(x0) : lo.get(x0)
              if (!b) return undefined
              sum += c * b[0]; used.push(b[1])
            }
            return (val ? sum <= 0 : sum >= 1) ? used : undefined
          }
          for (const val of [true, false]) {
            const used = side(val)
            if (!used) continue
            const w = new Set<string>()
            for (const i of used) for (const n of rowsR[i]!.w) w.add(n)
            clauses.push({lits: new Map([[name, !val]]), node: -1})
            pending.set(clauses.length - 1, {w, used: used.map(i => full[i]!.lin), name, val})
            assign(name, val, clauses.length - 1)
            forced++
            break
          }
        }
        if (timing) st.boundMs += performance.now() - tb
        if (forced) continue
      }
      let steps: Step[] | undefined
      let verdict: ReturnType<typeof solve> | undefined
      t(() => {
        // The simplex first (warm from the node before): a conflict's rows, refuted exactly, are the leaf. With a case
        // still open, a node it finds feasible is split; with none, the exact elimination below decides it (integers).
        if (sx) {
          const t0 = timing ? performance.now() : 0
          // (a tableau that has gathered many more forms than a node reads is begun again: every pivot updates them all)
          if (sx.size > 4 * full.length + 500 || sx.nnz > lpFill * full.length) { sx = new Simplex(); st.lpRebuilds++ }
          const p0 = sx.pivots
          let lp = sx.load(full)
          if (lp.kind === 'sat') lp = sx.check()
          if (timing) { st.lpMs += performance.now() - t0; st.pivots += sx.pivots - p0; st.lpRows = sx.size; st.lpNnz = sx.nnz; st.lpVars = sx.vars; st.lpLoad = full.length; if (lp.kind === 'unknown') st.lpUnknown++ }
          if (lp.kind === 'conflict') {
            const support = lp.rows.sort((x, y) => x - y), out = solve(support.map(i => full[i]!))
            if (out.kind === 'refuted') steps = out.steps.map(s => (s.kind === 'input' ? {...s, index: support[s.index]!} : s))
            else st.lpMisses++
          }
          if (steps || (open && lp.kind === 'sat')) return
        }
        st.fmCalls++
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
        let pick: string | undefined, best = -1
        for (const lin of cands) { const name = ensure(lin), x = vars.get(name)!; if (x.val === undefined && x.act > best) { best = x.act; pick = name } }
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

// The DAG as a kernel tree below `root`, walked depth first with a reader of its own (the tree's path is a stack, as
// the search's trail is): each leaf's derivation found again among the rows at its tree path, in kernel.ts's order (the
// tree's leaves index those), else those rows refuted afresh. GDP_CDCL_VERIFY=1 compares each leaf's rows with
// kernel.ts's (kernel/cdcl.test.ts).
function unfold(goal: Goal, nodes: DagNode[], top: number, root: Path, maxLeaves: number, until: number): Tree | undefined {
  const stack: {name: string, lin: Lin, holds: boolean}[] = [], on = new Map<string, {val: boolean, at: number}>(), stamps: number[] = []
  let stampN = 0, leaves = 0
  const push = (name: string, lin: Lin, holds: boolean) => { on.set(name, {val: holds, at: stack.length}); stamps[stack.length] = ++stampN; stack.push({name, lin, holds}) }
  const pop = () => { on.delete(stack.pop()!.name) }
  for (const [key, a] of root) push(key, a.lin, a.holds)
  const reader = new Reader(goal, {get: name => on.get(name), stamp: at => stamps[at]!, size: () => stack.length, lin: at => stack[at]!})
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
    if (++leaves > maxLeaves || clock() > until) { cdclStats.unfoldWhy = leaves > maxLeaves ? 'leaves' : 'time'; return undefined }
    reader.begin()
    const rows = reader.leafRows()
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
    const fast = rows.length > 60 ? refuteFast(rows) : undefined
    if (fast?.kind === 'refuted') return {leaf: fast.steps}
    const out = solve(rows)
    if (out.kind === 'refuted') return {leaf: out.steps}
    cdclStats.unfoldWhy = 'refute'
    return undefined
  }
  return go(top)
}
