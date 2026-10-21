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
import type {C, E, Law, Machine} from '../core/machine.ts'
import {type Lin, type Step, add, k, refuteFast, scale, solve, sub, v} from '../core/solver.ts'
import {type Goal, type Instances, type Liveness, type Path, type Seen, type StepLaw, type Tree, assumed, boundOf, canon, canonFlip, columnTerm, decided, factorsOf, isCell, isMonomial, stepZone, check, checkLaws, checkStepLaws, historyMachine, leafConstraints, leafConstraintsReusing, reusing, linear, livenessHelpful, livenessParts, obligations, plainKey, progressObligations, stepLawObligations, trueC, truth, unreachable, witnessesOf, withProducts} from './kernel.ts'

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

// Pairs of reads of one map whose keys the path doesn't yet compare.
function openCells(rows: {lin: Lin}[], path: Path): Lin[] {
  const names = [...new Set(rows.flatMap(r => Object.keys(r.lin)))].filter(isCell)
  const out: Lin[] = []
  const keyText = (n: string) => n.slice(n.indexOf('[') + 1, -1)
  for (const [i, p] of names.entries()) for (const q of names.slice(i + 1)) {
    if (p.slice(0, p.indexOf('[')) !== q.slice(0, q.indexOf('['))) continue
    const d = sub(parse(keyText(p)), parse(keyText(q)))
    const dec = (lin: Lin) => path.get(canon(lin))?.holds ?? (path.has(canonFlip(lin)) ? !path.get(canonFlip(lin))!.holds : undefined)
    const a = dec(d), b = dec(scale(d, -1))
    if (a === undefined) out.push(d)
    else if (a === true && b === undefined) out.push(scale(d, -1))
  }
  return out
}
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
const proveTrace = !!(globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env?.PROVE_TRACE
// `why`, when the budget ran out: which limit, at what size, and what usually helps.
export type Outcome = {tree: Tree, nodes: number} | {stuck: 'sat' | 'unknown', witness?: Record<string, number>, path: Path, why?: string}

// The budget: 200,000 nodes and, by default, a second per hypothesis (at least 20 seconds) per goal; past either the goal
// is left `unknown`. A goal with many instances (a law about two keys at its pairs) has that many more rows per leaf.
export function grow(goal: Goal, path: Path = new Map(), budget: {nodes: number, until?: number} = {nodes: 0, until: performance.now() + Math.max(20_000, 1_000 * goal.hyps.length)}): Outcome {
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
  if (path.size === 0 && budget.nodes === 0) {
    const open = new Set(leafConstraints(goal, path).flatMap(r => Object.keys(r.lin)).filter(n => n.startsWith('⟦') && columnTerm(n)?.op === 'if')).size
    const plain = growPlain(goal, path, {nodes: 0, until: budget.until, cap: Math.max(32, Math.round(4_000 / 2 ** (open / 2)))})
    if ('tree' in plain || plain.stuck === 'sat' || plain.why === undefined) return plain
    const cut = withCuts(goal, path, budget)
    if (cut) return cut
  }
  return growPlain(goal, path, budget)
}
function growPlain(goal: Goal, path: Path, budget: {nodes: number, until?: number, cap?: number}): Outcome {
  if (budget.cap !== undefined && budget.nodes >= budget.cap) return {stuck: 'unknown', path, why: 'cap'}
  if (profile.on) profile.nodes++
  if (++budget.nodes > 200_000 || (budget.until !== undefined && performance.now() > budget.until)) return {stuck: 'unknown', path, why: outOfBudget(goal, budget.nodes > 200_000 ? 'nodes' : 'time', path.size)}
  // Rows that read a term column only once a cut has put one on the path; before, the rows a choice-free search uses
  // (what it saw before term columns), renumbered to the whole leaf's when a leaf is found.
  const full = timed(() => leafConstraintsReusing(goal, path), ms => { profile.rowsMs += ms })
  const columns = [...path.values()].some(a => Object.keys(a.lin).some(key => key.startsWith('⟦')))
  const idx = full.flatMap((r, i) => (columns || !Object.keys(r.lin).some(key => key.startsWith('⟦')) ? [i] : []))
  const rows = idx.map(i => full[i]!), at = (i: number) => (i < rows.length ? idx[i]! : full.length + i - rows.length)
  const leafOf = (steps0: Step[], products0?: [number, number][], squares0?: Lin[]): Tree => {
    const {steps, products, squares} = products0 || squares0 ? trimmed(rows.length, steps0, products0 ?? [], squares0 ?? []) : {steps: steps0, products: undefined, squares: undefined}
    return {leaf: steps.map(st => (st.kind === 'input' ? {...st, index: at(st.index)} : st)), ...(products?.length ? {products: products.map(([i, j]) => [at(i), at(j)] as [number, number])} : {}), ...(squares?.length ? {squares} : {})}
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
    if (fast?.kind === 'refuted') return {tree: {leaf: fast.steps}, nodes: budget.nodes}
  }
  let split = next ?? (verdict.kind === 'unknown' ? bisect(rows, path) ?? fractional(verdict.point, path) : undefined)
  // Products: with monomials about, try every pair of rows multiplied; failing that, split a factor at zero.
  const monomials = rows.some(r => Object.keys(r.lin).some(isMonomial))
  // A witness that multiplies out (each monomial's value is its factors' product) is a real model: nothing to refute.
  if (!split && monomials && verdict.kind === 'sat') {
    const w = verdict.witness, value = (key: string) => w[key] ?? 0
    const real = rows.every(r => Object.keys(r.lin).every(key => !isMonomial(key) || value(key) === factorsOf(key).reduce((acc, f) => acc * value(f), 1)))
    if (real) return {stuck: 'sat', witness: w, path}
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
    const ra = leafConstraintsReusing(goal, a), rb = leafConstraintsReusing(goal, b), at = new Map<string, number>()
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
// A key bound by a quantified flag or a write at every key isn't one: those reads are at every key already.
function readKeys(m: Machine, laws: Law[]): E[] {
  const out = new Map<string, E>()
  const bound = new Set<string>([...Object.values(m.step.flags ?? {}).flatMap(c => (c.op === 'all' ? boundOf(c) : [])), ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [w.each] : []))])
  const free = (e: E) => !JSON.stringify(e).match(/"name":"([^"]+)"/g)?.some(n => bound.has(n.slice(8, -1)))
  const inE = (e: E): void => {
    if (e.op === 'get') { if (free(e.key)) out.set(JSON.stringify(e.key), e.key); inE(e.key) }
    else if (e.op === 'if') (inC(e.c), inE(e.then), inE(e.else))
    else if (e.op === 'mul') inE(e.a)
    else if ('a' in e) (inE(e.a), inE(e.b))
  }
  const inC = (c: C): void => (c.op === 'flag' ? undefined : c.op === 'all' ? inC(c.c) : c.op === 'not' ? inC(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.forEach(inC) : (inE(c.a), inE(c.b)))
  Object.values(m.step.state ?? {}).forEach(inE)
  Object.values(m.step.flags ?? {}).forEach(inC)
  for (const w of Object.values(m.step.maps ?? {})) { if (!('each' in w)) { out.set(JSON.stringify(w.key), w.key); inE(w.key) } inE(w.value) }
  for (const l of laws.filter(l => !l.forall)) inC(l.holds)
  return [...out.values()]
}
const shifts = (m: Machine) => Object.values(m.step.maps ?? {}).some(w => 'each' in w && !plainKey(w.value, w.each))
// The keys some goals read a map at.
function mapKeys(goals: Goal[]): E[] {
  const out = new Map<string, E>()
  const inE = (e: E): void => {
    if (e.op === 'get') { out.set(JSON.stringify(e.key), e.key); inE(e.key) }
    else if (e.op === 'if') (inC(e.c), inE(e.then), inE(e.else))
    else if (e.op === 'mul') inE(e.a)
    else if ('a' in e) (inE(e.a), inE(e.b))
  }
  const inC = (c: C): void => (c.op === 'flag' ? undefined : c.op === 'all' ? inC(c.c) : c.op === 'not' ? inC(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.forEach(inC) : (inE(c.a), inE(c.b)))
  for (const g of goals) g.hyps.forEach(inC)
  return [...out.values()]
}
// Instances with each every-key law also at these keys. A law about two keys or more goes at tuples that relate the
// goal's own keys (`focus`: the skolems of the law it proves, or a step law's keys) to each other and to the keys that
// read none of them: at the i-th place, a key that reads the i-th focus alone (the first, past the focus there is), and
// at most one place a key that reads no focus.
const withReads = (laws: Law[], inst: Instances, keys: E[], focus: string[]): Instances => ({...inst, ...Object.fromEntries(laws.filter(l => l.forall).map(l => {
  const had = inst[l.name] ?? []
  if (l.keys?.length) {
    const n = l.keys.length + 1, out = new Map<string, E[]>()
    for (let i = 0; i + n <= had.length; i += n) out.set(JSON.stringify(had.slice(i, i + n)), had.slice(i, i + n))
    for (const tuple of related(keys, focus, n)) out.set(JSON.stringify(tuple), tuple)
    return [l.name, [...out.values()].flat()]
  }
  const seen = new Set(had.map(e => JSON.stringify(e)))
  return [l.name, [...had, ...keys.filter(e => { const id = JSON.stringify(e); return seen.has(id) ? false : (seen.add(id), true) })]]
}))})
// The n-tuples of the keys that relate the focus (withReads).
const related = (keys: E[], focus: string[], n: number): E[][] => {
  const reads = (e: E, x?: string) => x !== undefined && JSON.stringify(e).includes(`"name":${JSON.stringify(x)}`)
  const own = (i: number) => { const f = focus[i] ?? focus[0]; return keys.filter(e => reads(e, f) && focus.every(g => g === f || !reads(e, g))) }
  const R = keys.filter(e => !focus.some(f => reads(e, f))), out: E[][] = []
  const go = (i: number, tuple: E[], rest: boolean): void => {
    if (i === n) { out.push(tuple); return }
    for (const e of own(i)) go(i + 1, [...tuple, e], rest)
    if (!rest) for (const e of R) go(i + 1, [...tuple, e], true)
  }
  go(0, [], false)
  return out
}
// A law about every n keys at every n-tuple of the keys (flattened, as Instances keeps tuples).
const tuples = (keys: E[], n: number): E[] => (n === 0 ? [] : n === 1 ? keys : keys.flatMap(a => { const rest = tuples(keys, n - 1); return Array.from({length: rest.length / (n - 1)}, (_, t) => [a, ...rest.slice(t * (n - 1), (t + 1) * (n - 1))]).flat() }))
// The keys some goals read a function at.
function fnKeys(m: Machine, goals: Goal[]): E[] {
  const fns = Object.keys(m.fns ?? {}), out = new Map<string, E>()
  const inE = (e: E): void => {
    if (e.op === 'get') { if (fns.includes(e.map)) out.set(JSON.stringify(e.key), e.key); inE(e.key) }
    else if (e.op === 'if') (inC(e.c), inE(e.then), inE(e.else))
    else if (e.op === 'mul') inE(e.a)
    else if ('a' in e) (inE(e.a), inE(e.b))
  }
  const inC = (c: C): void => (c.op === 'flag' ? undefined : c.op === 'all' ? inC(c.c) : c.op === 'not' ? inC(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.forEach(inC) : (inE(c.a), inE(c.b)))
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
  return go(pattern, term) ? bound : undefined
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
  for (let round = 0; round < 2; round++) {
    if (m.facts?.length) inst = withFacts(m, inst, fnKeys(m, build(inst)))
    if (reads) { const keys = mapKeys(build(inst)); inst = union(withReads(laws, inst, keys, opts.focus ?? []), flagInstances(m, keys, opts.focus), m) }
  }
  return inst
}
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
      case 'add': case 'sub': case 'min': case 'max': case 'prod': return {...t, a: e(t.a), b: e(t.b)}
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

export function proveLaws(m: Machine, laws: Law[]): Report & {laws?: Law[], proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}} {
  if (!laws.some(l => someKeys(l.holds).length)) return proveLawsAsGiven(m, laws)
  const out = chooseWitnesses(laws, l => l.holds, l => (l.forall ? [l.forall] : []), m, ls => { const r = proveLawsAsGiven(m, ls); return r.proven && r.checked }, (l, holds) => ({...l, holds, stated: l.stated ?? l.holds}))
  if ('stuck' in out) return {proven: false, nodes: 0, leaves: 0, failed: {goal: 'witnesses', stuck: out.stuck}, checked: false}
  return {...proveLawsAsGiven(m, out.items), laws: out.items}
}
// One law's two goals, every law assumed (core/infer.ts adds laws one at a time and reproves only what isn't proven
// yet); not a proof of the set, which proveLaws gives. Laws with some key go through proveLaws.
export function proveLaw(m: Machine, laws: Law[], i: number): {proven: true} | {proven: false, goal: string, stuck: string, witness?: Record<string, number>} {
  const law = laws[i]!
  if (laws.some(l => someKeys(l.holds).length)) {
    const r = proveLaws(m, laws)
    return r.proven ? {proven: true} : {proven: false, goal: r.failed!.goal, stuck: r.failed!.stuck, ...(r.failed!.witness ? {witness: r.failed!.witness} : {})}
  }
  const keys = [...readKeys(m, laws), ...witnesses(m)]
  const inst = instancesFor(m, laws, inst => obligations(m, laws, {[law.name]: inst}, i), {
    seed: [...keys, ...(law.forall ? [{op: 'var', name: `${law.forall}#`} as E] : []), ...(law.keys ?? []).map((name): E => ({op: 'var', name}))],
    focus: [...(law.forall ? [`${law.forall}#`] : []), ...(law.keys ?? [])],
  })
  for (const goal of obligations(m, laws, {[law.name]: inst}, i)) {
    const out = grow(goal)
    if (!('tree' in out)) return {proven: false, goal: goal.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {})}
  }
  return {proven: true}
}
function proveLawsAsGiven(m: Machine, laws: Law[]): Report & {proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}} {
  // Each law's two goals (start and step) get their own instances, seeded with its own keys.
  const keys = [...readKeys(m, laws), ...witnesses(m)], instances: Record<string, Instances> = {}
  laws.forEach((law, i) => {
    instances[law.name] = instancesFor(m, laws, inst => obligations(m, laws, {...instances, [law.name]: inst}, i), {
      seed: [...keys, ...(law.forall ? [{op: 'var', name: `${law.forall}#`} as E] : []), ...(law.keys ?? []).map((name): E => ({op: 'var', name}))],
      focus: [...(law.forall ? [`${law.forall}#`] : []), ...(law.keys ?? [])],
    })
  })
  const trees: Record<string, Tree> = {}
  let nodes = 0, leaves = 0
  for (const goal of obligations(m, laws, instances)) {
    const out = grow(goal)
    if (!('tree' in out)) return {proven: false, nodes, leaves, failed: {goal: goal.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {}), ...(out.why ? {why: out.why} : {})}, checked: false}
    trees[goal.name] = out.tree
    nodes += out.nodes
    leaves += countLeaves(out.tree)
  }
  const proof = {instances, trees}
  return {proven: true, nodes, leaves, checked: checkLaws(m, laws, proof), proof}
}
// Step laws (kernel.ts's stepLawObligations): the laws proven first (they are assumed), then one goal per step law, the
// every-key laws assumed at every key the step, the laws and the step laws read.
type StepProof = {laws: {instances: Record<string, Instances>, trees: Record<string, Tree>}, instances: Instances, perStep?: Record<string, Instances>, trees: Record<string, Tree>}
export function proveStepLaws(m: Machine, given: Law[], stepLaws: StepLaw[]): Report & {laws?: Law[], stepLaws?: StepLaw[], proof?: StepProof} {
  const base = proveLaws(m, given)
  if (!base.proven || !base.proof) return {proven: false, nodes: base.nodes, leaves: base.leaves, ...(base.failed ? {failed: base.failed} : {}), checked: false}
  const laws = base.laws ?? given
  if (stepLaws.some(sl => someKeys(sl.then).length)) {
    // Each step law's witnesses on its own (a step law assumes no other), the request and the state after among them.
    const plain = m.history ? historyMachine(m).machine : m, after = Object.keys(plain.state).map(n => `${n}'`)
    const out = chooseWitnesses(stepLaws, sl => sl.then, sl => [...(sl.forall ? [sl.forall] : []), ...plain.inputs, ...after], plain,
      sls => sls.every(sl => { const r = proveStepLawsAsGiven(m, laws, [sl], base); return r.proven && r.checked }), (sl, then) => ({...sl, then}))
    if ('stuck' in out) return {proven: false, nodes: base.nodes, leaves: base.leaves, failed: {goal: 'witnesses', stuck: out.stuck}, checked: false}
    return {...proveStepLawsAsGiven(m, laws, out.items, base), ...(base.laws ? {laws} : {}), stepLaws: out.items}
  }
  return {...proveStepLawsAsGiven(m, laws, stepLaws, base), ...(base.laws ? {laws} : {})}
}
function proveStepLawsAsGiven(m: Machine, laws: Law[], stepLaws: StepLaw[], base: Report & {proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}}): Report & {proof?: StepProof} {
  if (!base.proof) return {proven: false, nodes: base.nodes, leaves: base.leaves, checked: false}
  const plain = m.history ? historyMachine(m).machine : m
  // Each step law its own instances, from its own goal: the keys the step and the laws read, and its own (a k-step
  // law's later frames read keys no other step law has); where positions shift or a law is about several keys, the
  // keys its goal reads a map at too. A frame's hypotheses read no name the run introduces later (kernel.ts's
  // stepZone), so a k-step law drops the keys that read one; but a flag that holds at every key holds at a later step's
  // key too: where these instances don't prove it, each flag at its own witness at every step is tried (keptAcross).
  const shared = [...readKeys(plain, laws), ...witnesses(plain)], named = [...laws, ...(plain.facts ?? [])], reads = shifts(plain) || laws.some(l => l.keys?.length) || pairFlags(plain)
  const own = (sl: StepLaw): E[] => [...[sl.then, ...(sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when])].flatMap(readKeysC),
    ...[sl.forall, ...(sl.keys ?? [])].flatMap(key => (key ? [{op: 'var', name: key} as E] : []))]
  const perStep: Record<string, Instances> = {}
  for (const sl of stepLaws) {
    const zone = stepZone(plain, sl.steps ?? 1), keep = (inst: Instances) => avoiding(inst, zone, named, plain)
    perStep[sl.name] = keep(instancesFor(plain, laws, inst => stepLawObligations(m, laws, keep(inst), sl),
      {seed: [...shared, ...own(sl)], focus: [sl.forall, ...(sl.keys ?? [])].flatMap(k => (k ? [k] : [])), reads}))
  }
  const instances = perStep[stepLaws[0]?.name ?? ''] ?? {}
  const trees: Record<string, Tree> = {}
  let nodes = base.nodes, leaves = base.leaves
  for (const sl of stepLaws) for (const goal of stepLawObligations(m, laws, perStep[sl.name] ?? instances, sl)) {
    let out = grow(goal)
    // A k-step law that reads a condition kept across its steps: each flag at its own witnesses, at every step.
    if (!('tree' in out)) for (const kept of keptAcross(plain, laws, perStep[sl.name] ?? instances, own(sl), sl.steps ?? 1)) {
      const again = grow(stepLawObligations(m, laws, kept, sl)[0]!)
      if ('tree' in again) { out = again; perStep[sl.name] = kept; break }
    }
    if (!('tree' in out)) return {proven: false, nodes, leaves, failed: {goal: goal.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {}), ...(out.why ? {why: out.why} : {})}, checked: false}
    trees[goal.name] = out.tree
    nodes += out.nodes
    leaves += countLeaves(out.tree)
  }
  const proof = {laws: base.proof, instances, ...(Object.keys(perStep).length ? {perStep} : {}), trees}
  return {proven: true, nodes, leaves, checked: checkStepLaws(m, laws, stepLaws, proof), proof}
}
// Progress (kernel.ts's progressObligations): the laws proven first, then each goal, the every-key laws assumed at every
// key the goals read a map at.
export function proveProgress(m: Machine, laws: Law[], p: {name: string, when: C, then: C, request: Record<string, E>}): Report & {instances?: Instances, trees?: Record<string, Tree>} {
  const base = proveLaws(m, laws)
  if (!base.proven || !base.checked) return {proven: false, nodes: base.nodes, leaves: base.leaves, ...(base.failed ? {failed: base.failed} : {}), checked: false}
  const ls = base.laws ?? laws
  const instances = instancesFor(m, ls, inst => progressObligations(m, ls, inst, p))
  const trees: Record<string, Tree> = {}
  let nodes = base.nodes, leaves = base.leaves
  for (const goal of progressObligations(m, ls, instances, p)) {
    const out = grow(goal)
    if (!('tree' in out)) return {proven: false, nodes, leaves, failed: {goal: goal.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {}), ...(out.why ? {why: out.why} : {})}, checked: false}
    trees[goal.name] = out.tree
    nodes += out.nodes
    leaves += countLeaves(out.tree)
  }
  return {proven: true, nodes, leaves, checked: progressObligations(m, ls, instances, p).every(g => check(g, trees[g.name]!)), instances, trees}
}
// Liveness (kernel.ts's livenessParts): its step laws, proven together. The claim needs no more (a run takes the
// request, so it is allowed); but a request never allowed would leave the claim about no run, so where a helpful request
// names every input a client sends and carries no maps, it is proven allowed in its region too.
export function proveLiveness(m: Machine, laws: Law[], l: Liveness): Report & {steps?: ReturnType<typeof proveStepLaws>} {
  const {stay, cover, helps} = livenessParts(m, l)
  const a = proveStepLaws(m, laws, [stay, cover, ...helps])
  if (!a.proven || !a.checked) return {proven: false, nodes: a.nodes, leaves: a.leaves, ...(a.failed ? {failed: a.failed} : {}), checked: false}
  const plain = m.history ? historyMachine(m).machine : m
  let nodes = a.nodes, leaves = a.leaves
  for (const [i, h] of livenessHelpful(l).entries()) {
    if (m.history || plain.inputMaps?.length || !plain.assume || !plain.inputs.every(inp => inp in h.request)) continue
    const b = proveProgress(plain, laws, {name: `${l.name}: helpful request ${i + 1} is allowed`, when: {op: 'and', xs: [l.from, {op: 'not', x: l.to}, h.when]}, then: trueC, request: h.request})
    nodes += b.nodes; leaves += b.leaves
    if (!b.proven || !b.checked) return {proven: false, nodes, leaves, ...(b.failed ? {failed: b.failed} : {}), checked: false}
  }
  return {proven: true, checked: true, nodes, leaves, steps: a}
}

// The key terms a condition reads maps at; a primed map's key is a key of the map before the step too.
function readKeysC(c: C): E[] {
  const out: E[] = []
  const inE = (e: E): void => { if (e.op === 'get') (out.push(e.key), inE(e.key)); else if (e.op === 'if') (inC(e.c), inE(e.then), inE(e.else)); else if (e.op === 'mul') inE(e.a); else if ('a' in e) (inE(e.a), inE(e.b)) }
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
      case 'get': return NaN
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
