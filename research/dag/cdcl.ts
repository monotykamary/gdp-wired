// CDCL over the goal's atoms with the kernel's reading as the theory: `bun research/dag/cdcl.ts <goal.json> [--ms 55000]
// [--out <dir>]`. Untrusted; its certificate is dag.ts's (leaves and resolutions), checked by check-dag.ts.
//
// The trail is a path (kernel.ts's Path: atoms lin <= 0 decided true or false). After each round of unit propagation
// over the learned clauses, the rows the kernel reads at the trail are solved (as growPlain solves a node): refuted,
// the refutation's core (cores.ts) replayed at the core alone is a leaf, a clause of decisions that can't all hold;
// conflict analysis resolves it with the clauses that propagated its latest literals down to the first unique
// implication point (each resolution a node), learns the result, jumps back to the level where it is unit and asserts
// the flipped literal. Not refuted, the next decision is the open atom (growPlain's candidates at the trail: units,
// the conclusion's atoms, the hypotheses') of highest activity (VSIDS: each learned clause's atoms bumped, 0.95 decay),
// its last value first (phase saving, true at first); Luby restarts (unit 32 conflicts). A conflict at level 0 is
// resolved down to the empty clause: the DAG's root.
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import type {Constraint, Lin, Step} from '../../core/solver.ts'
import {refuteFast, solve, work} from '../../core/solver.ts'
import {type Goal, type Path, atomOf, canon, canonFlip, leafConstraints, leafConstraintsReusing} from '../../kernel/kernel.ts'
import {loadGoal} from './goalio.ts'
import {coreOf, replay, sub, usedRows} from './cores.ts'
import {openOrder} from './tree.ts'
import {type Dag, type DagNode, sizes} from './dag.ts'

type Var = {lin: Lin, val?: boolean, level: number, reason?: number, at: number, act: number, phase: boolean}
type Clause = {lits: Map<string, boolean>, node: number}

export function cdcl(goal: Goal, opts: {until: number, bounds?: boolean, lazy?: boolean}) {
  const vars = new Map<string, Var>(), trail: string[] = [], levels: number[] = [] // levels[l]: trail length at level l's decision
  const nodes: DagNode[] = [], clauses: Clause[] = [], occ = new Map<string, number[]>()
  const stats = {conflicts: 0, theoryConflicts: 0, decisions: 0, propagations: 0, restarts: 0, solves: 0, solveMs: 0, rowsMs: 0, coreMs: 0, fullPathLeaves: 0, resolutions: 0, maxLevel: 0, maxTrail: 0, boundProps: 0, boundLeaves: 0, boundFallback: 0, boundConflicts: 0, orderMs: 0}
  let inc = 1
  // An atom as a variable: the stored form is the one whose canonical text is the variable's name.
  const varOf = (lin: Lin): {v: string, flip: boolean} => { const a = canon(lin), b = canonFlip(lin); return a <= b ? {v: a, flip: false} : {v: b, flip: true} }
  const ensure = (lin: Lin): string => {
    const {v, flip} = varOf(lin)
    if (!vars.has(v)) vars.set(v, {lin: flip ? atomOf(lin, false).lin : lin, level: -1, at: -1, act: 0, phase: !flip})
    return v
  }
  const level = () => levels.length
  const path = (): Path => new Map(trail.map(v => { const x = vars.get(v)!; return [v, {lin: x.lin, holds: x.val!}] }))
  const assign = (v: string, val: boolean, reason?: number) => {
    const x = vars.get(v)!
    x.val = val; x.level = level(); x.at = trail.length; x.phase = val
    if (reason === undefined) delete x.reason; else x.reason = reason
    trail.push(v)
  }
  const undoTo = (l: number) => {
    const keep = l === 0 ? (levels[0] ?? trail.length) : (levels[l] ?? trail.length)
    while (trail.length > keep) { const x = vars.get(trail.pop()!)!; delete x.val; x.level = -1; delete x.reason }
    levels.length = l
  }
  const addClause = (lits: Map<string, boolean>, node: number): number => {
    clauses.push({lits, node})
    const i = clauses.length - 1
    for (const [v, pos] of lits) { const key = `${v}=${pos}`; let xs = occ.get(key); if (!xs) occ.set(key, (xs = [])); xs.push(i) }
    return i
  }
  // Unit propagation from the trail's position `from`: a clause whose literals all hold is a conflict (its index).
  let qhead = 0
  const propagate = (): number | undefined => {
    while (qhead < trail.length) {
      const v = trail[qhead++]!, x = vars.get(v)!
      for (const ci of occ.get(`${v}=${x.val}`) ?? []) {
        const c = clauses[ci]!
        let open: string | undefined, nOpen = 0, dead = false
        for (const [w, p] of c.lits) {
          const y = vars.get(w)!
          if (y.val === undefined) { nOpen++; open = w; if (nOpen > 1) break } else if (y.val !== p) { dead = true; break }
        }
        if (dead || nOpen > 1) continue
        if (nOpen === 0) return ci
        assign(open!, !c.lits.get(open!)!, ci)
        stats.propagations++
      }
    }
    return undefined
  }
  const bump = (lits: Map<string, boolean>) => {
    for (const v of lits.keys()) { const x = vars.get(v)!; x.act += inc; if (x.act > 1e100) { for (const y of vars.values()) y.act *= 1e-100; inc *= 1e-100 } }
    inc /= 0.95
  }
  // Resolve clause k (all literals holding) on variable v with v's reason: one node.
  const resolveOn = (k: Clause, v: string): Clause => {
    const x = vars.get(v)!, r = clauses[x.reason!]!
    if (r.node < 0) materialize(x.reason!)
    const lits = new Map(k.lits)
    lits.delete(v)
    for (const [w, p] of r.lits) if (w !== v) lits.set(w, p)
    // The node's two parents: the one deciding the atom (as stored) true, then the one deciding it false.
    const kHolds = k.lits.get(v)!
    nodes.push({res: kHolds ? [k.node, r.node] : [r.node, k.node], on: x.lin})
    stats.resolutions++
    return {lits, node: nodes.length - 1}
  }
  // A theory conflict at the trail: the leaf, at its core.
  const leafAt = (p: Path, full: ReturnType<typeof leafConstraintsReusing>, steps: Step[]): Clause => {
    const t1 = performance.now()
    const used = usedRows(full.length, steps)
    const core = coreOf(goal, p, full, used)
    const short = core.size < p.size ? replay(goal, full, sub(p, core), steps) : undefined
    stats.coreMs += performance.now() - t1
    const q = short ? sub(p, core) : p
    if (!short) stats.fullPathLeaves++
    nodes.push({leaf: [...q.values()].map(a => [a.lin, a.holds]), steps: short ? short.steps : steps})
    return {lits: new Map([...q.keys()].map(v => [v, vars.get(v)!.val!])), node: nodes.length - 1}
  }
  // Bound propagation's reasons, made when conflict analysis reads them: the atom's bounds (single-variable rows at
  // the path then) and its other side refute each other, a leaf at the bounds' core with that side decided.
  const pendingLeaf = new Map<number, {p: Path, full: Constraint[], used: number[], v: string, val: boolean}>()
  const materialize = (ci: number) => {
    const t1 = performance.now()
    try { materialize1(ci) } finally { stats.coreMs += performance.now() - t1 }
  }
  const materialize1 = (ci: number) => {
    const w0 = pendingLeaf.get(ci)!, x = vars.get(w0.v)!, c = clauses[ci]!
    const w = {...w0, core: coreOf(goal, w0.p, w0.full, new Set(w0.used)), from: w0.used.map(i => w0.full[i]!)}
    const local = [...w.from, {lin: atomOf(x.lin, !w.val).lin, label: ''}]
    const s = solve(local)
    if (s.kind !== 'refuted') throw new Error('a bound propagation its bounds do not refute')
    for (const keep of [w.core, new Set(w.p.keys())]) {
      const to = sub(w.p, keep).set(w.v, {lin: x.lin, holds: !w.val})
      let r = replay(goal, local, to, s.steps)
      if (!r) { // the rows read again there, refuted whole
        stats.boundFallback++
        const rows = leafConstraints(goal, to), whole = solve(rows)
        if (whole.kind === 'refuted') r = {rows, steps: whole.steps}
      }
      if (!r) continue
      nodes.push({leaf: [...to.values()].map(a => [a.lin, a.holds]), steps: r.steps})
      c.lits = new Map([...to].map(([key, a]) => [key, a.holds]))
      c.node = nodes.length - 1
      stats.boundLeaves++
      pendingLeaf.delete(ci)
      return
    }
    throw new Error('a bound propagation that does not replay')
  }
  const luby = (i: number): number => { let k = 1; while ((1 << k) - 1 < i + 1) k++; return (1 << k) - 1 === i + 1 ? 1 << (k - 1) : luby(i + 1 - (1 << (k - 1)) )}
  let restartAt = 32, nRestart = 0, sinceRestart = 0
  for (;;) {
    if (performance.now() > opts.until) return {out: {stuck: 'unknown' as const, why: 'budget'}, nodes, stats, learned: clauses.length}
    let conflict: Clause | undefined
    const ci = propagate()
    if (ci !== undefined) conflict = clauses[ci]!
    else {
      const p = path()
      stats.maxTrail = Math.max(stats.maxTrail, p.size)
      const t0 = performance.now(), full = leafConstraintsReusing(goal, p)
      stats.rowsMs += performance.now() - t0
      work.n += 1 + full.length
      const columns = [...p.values()].some(a => Object.keys(a.lin).some(key => key.startsWith('⟦')))
      const idx = full.flatMap((r, i) => (columns || !Object.keys(r.lin).some(key => key.startsWith('⟦')) ? [i] : []))
      const rows = idx.map(i => full[i]!), at = (i: number) => (i < rows.length ? idx[i]! : full.length + i - rows.length)
      const tOrder = performance.now()
      const cands = openOrder(goal, p, rows).filter(lin => Object.keys(lin).some(key => key !== '1') && !p.has(canon(lin)) && !p.has(canonFlip(lin)))
      const pending = cands.length > 0
      stats.orderMs += performance.now() - tOrder
      // Bound propagation: an open atom its variables' bounds (the single-variable rows) decide.
      const lo = new Map<string, [number, number]>(), hi = new Map<string, [number, number]>()
      if (opts.bounds !== false) full.forEach((r, i) => {
        const ks = Object.keys(r.lin).filter(key => key !== '1')
        if (ks.length !== 1) return
        const x0 = ks[0]!, c = r.lin[x0]!, k0 = r.lin['1'] ?? 0
        if (c > 0) { const b = Math.floor(-k0 / c); if (b < (hi.get(x0)?.[0] ?? Infinity)) hi.set(x0, [b, i]) }
        else if (c < 0) { const b = Math.ceil(k0 / -c); if (b > (lo.get(x0)?.[0] ?? -Infinity)) lo.set(x0, [b, i]) }
      })
      // --lazy: a row its variables' bounds already violate is the conflict (it and those bounds, refuted alone); the
      // whole system is solved only once no candidate is left open.
      if (opts.lazy && pending) {
        let small: Step[] | undefined
        for (const [i, r] of full.entries()) {
          let sum = r.lin['1'] ?? 0
          const used = [i]
          for (const [x0, c] of Object.entries(r.lin)) {
            if (x0 === '1' || c === 0) continue
            const b = c > 0 ? lo.get(x0) : hi.get(x0)
            if (!b) { sum = -Infinity; break }
            sum += c * b[0]; used.push(b[1])
          }
          if (sum > 0) {
            const local = used.map(j => full[j]!), out = solve(local)
            stats.solves++
            if (out.kind === 'refuted') { small = out.steps.map(st => (st.kind === 'input' ? {...st, index: used[st.index]!} : st)); break }
          }
        }
        if (small) { conflict = leafAt(p, full, small); stats.theoryConflicts++; stats.boundConflicts++ }
      }
      if (!conflict && opts.bounds !== false && pending) {
        let forced = 0
        for (const lin of cands) {
          const v = ensure(lin), x = vars.get(v)!
          if (x.val !== undefined || Object.keys(x.lin).some(key => key.startsWith('⟦'))) continue // (a term column's rows read differently once its choice is decided)
          const side = (val: boolean): number[] | undefined => { // the rows that force the stored atom to `val`
            let sum = x.lin['1'] ?? 0
            const used: number[] = []
            for (const [x0, c] of Object.entries(x.lin)) {
              if (x0 === '1') continue
              const b = (c > 0) === val ? hi.get(x0) : lo.get(x0)
              if (!b) return undefined
              sum += c * b[0]; used.push(b[1])
            }
            return (val ? sum <= 0 : sum >= 1) ? used : undefined
          }
          for (const val of [true, false]) {
            const used = side(val)
            if (!used) continue
            // (its clause made when analysis reads it: materialize, the core then)
            clauses.push({lits: new Map([[v, !val]]), node: -1})
            pendingLeaf.set(clauses.length - 1, {p, full, used, v, val})
            assign(v, val, clauses.length - 1)
            forced++; stats.boundProps++
            break
          }
        }
        if (forced) continue
      }
      const timed = <T>(f: () => T): T => { const t = performance.now(); stats.solves++; try { return f() } finally { stats.solveMs += performance.now() - t } }
      let steps: Step[] | undefined
      let verdict: ReturnType<typeof solve> | undefined
      const solveHere = !conflict && !(opts.lazy && pending)
      if (solveHere) {
        if (pending && rows.length > 60) { const fast = timed(() => refuteFast(rows)); if (fast?.kind === 'refuted') steps = fast.steps.map(st => (st.kind === 'input' ? {...st, index: at(st.index)} : st)) }
        if (!steps) {
          verdict = timed(() => (pending && rows.length > 60 ? solve(rows, 2 * rows.length) : solve(rows)))
          if (verdict.kind === 'refuted') steps = verdict.steps.map(st => (st.kind === 'input' ? {...st, index: at(st.index)} : st))
        }
        if (!steps && pending && !columns && full.length > rows.length) { const fast = timed(() => refuteFast(full)); if (fast?.kind === 'refuted') steps = fast.steps }
      }
      if (steps) { conflict = leafAt(p, full, steps); stats.theoryConflicts++ }
      else if (!conflict) {
        // A decision: the open atom of highest activity (the first candidate among equals).
        let pick: string | undefined, best = -1
        for (const lin of cands) { const v = ensure(lin), x = vars.get(v)!; if (x.val === undefined && x.act > best) { best = x.act; pick = v } }
        if (!pick && verdict?.kind === 'unknown') {
          for (const [x0, value] of Object.entries(verdict.point ?? {})) {
            if (Math.abs(value - Math.round(value)) < 1e-9 || x0.includes('*')) continue
            const c = Math.floor(value), lin: Lin = c === 0 ? {[x0]: 1} : {[x0]: 1, 1: -c}
            if (!p.has(canon(lin)) && !p.has(canonFlip(lin))) { pick = ensure(lin); break }
          }
        }
        if (!pick) return {out: {stuck: verdict?.kind === 'sat' ? 'sat' as const : 'unknown' as const, why: verdict?.kind === 'sat' ? 'a model' : 'no split', ...(verdict?.kind === 'sat' ? {witness: verdict.witness} : {})}, nodes, stats, learned: clauses.length}
        levels.push(trail.length)
        stats.decisions++
        stats.maxLevel = Math.max(stats.maxLevel, level())
        assign(pick, vars.get(pick)!.phase)
        continue
      }
    }
    // Conflict analysis.
    stats.conflicts++; sinceRestart++
    let k = conflict!
    for (;;) {
      if (!k.lits.size) {
        return {out: {root: k.node}, nodes, stats, learned: clauses.length}
      }
      const top = Math.max(...[...k.lits.keys()].map(v => vars.get(v)!.level))
      if (top < level()) { undoTo(top); qhead = trail.length }
      const here = [...k.lits.keys()].filter(v => vars.get(v)!.level === top)
      if (top === 0) { // every literal propagated at level 0 (no decisions there): resolve the latest away
        const v = here.reduce((a, b) => (vars.get(a)!.at > vars.get(b)!.at ? a : b))
        k = resolveOn(k, v)
        continue
      }
      if (here.length === 1) break
      const v = here.reduce((a, b) => (vars.get(a)!.at > vars.get(b)!.at ? a : b))
      if (vars.get(v)!.reason === undefined) break // the decision itself is the latest: one of several at its level — can't be, but stop safely
      k = resolveOn(k, v)
    }
    const top = Math.max(...[...k.lits.keys()].map(v => vars.get(v)!.level))
    const here = [...k.lits.keys()].filter(v => vars.get(v)!.level === top)
    bump(k.lits)
    const ci2 = addClause(k.lits, k.node)
    if (here.length !== 1) {
      // (no unique implication point: back to before the level and let propagation and the theory go again)
      undoTo(Math.max(0, top - 1)); qhead = Math.min(qhead, trail.length)
      continue
    }
    const uip = here[0]!
    const back = Math.max(0, ...[...k.lits.keys()].filter(v => v !== uip).map(v => vars.get(v)!.level))
    undoTo(back)
    qhead = trail.length
    assign(uip, !k.lits.get(uip)!, ci2)
    stats.propagations++
    if (sinceRestart >= restartAt) { stats.restarts++; sinceRestart = 0; restartAt = 32 * luby(++nRestart); undoTo(0); qhead = Math.min(qhead, trail.length) }
  }
}

if (import.meta.main) {
  const file = process.argv[2]!
  const arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
  const ms = Number(arg('--ms') ?? 55000), outDir = arg('--out')
  const goal = loadGoal(readFileSync(file, 'utf8'))
  const t0 = performance.now()
  const r = cdcl(goal, {until: t0 + ms, bounds: !process.argv.includes('--no-bounds'), lazy: process.argv.includes('--lazy')})
  const searchMs = performance.now() - t0
  const root = (r.out as {root?: number}).root
  const dag: Dag | undefined = root !== undefined ? {goal: goal.name, nodes: r.nodes, root} : undefined
  let check: {ok: boolean, ms: number, why?: string} | undefined
  if (dag) {
    const {checkDag} = await import('./check-dag.ts')
    const t1 = performance.now(), c = checkDag(goal, dag)
    check = {ok: c.ok, ms: Math.round(performance.now() - t1), ...(c.ok ? {} : {why: c.why})}
  }
  const res = {goal: goal.name, hyps: goal.hyps.length, outcome: dag ? 'proven' : 'stuck' in r.out ? r.out.stuck : '?', searchMs: Math.round(searchMs),
    ...Object.fromEntries(Object.entries(r.stats).map(([key, x]) => [key, Math.round(x)])), learned: r.learned, nodesMade: r.nodes.length,
    ...(dag ? {size: sizes(dag)} : {}), ...(check ? {check} : {})}
  console.log(JSON.stringify(res))
  if (outDir) { mkdirSync(outDir, {recursive: true}); writeFileSync(`${outDir}/result.json`, JSON.stringify(res)); if (dag) writeFileSync(`${outDir}/dag.json`, JSON.stringify(dag)) }
  process.exit(0)
}
