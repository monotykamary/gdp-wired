// An untrusted prover for the kernel: grows a split tree until every leaf's constraints are refuted by solve(), splitting
// on whatever atom the hypotheses leave open (an if's condition, a min's or ∸'s comparison, a disjunction's atoms, two
// reads of one map at keys not yet known equal or apart). Its trees go to kernel.check; nothing it says is trusted.
import type {C, E, Law, Machine} from '../core/machine.ts'
import {type Lin, add, k, scale, solve, sub} from '../core/solver.ts'
import {type Goal, type Instances, type Path, type StepLaw, type Tree, canon, checkLaws, checkStepLaws, historyMachine, leafConstraints, linear, obligations, stepLawObligations, truth, unreachable, withProducts} from './kernel.ts'

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
      if (a && b && linear(e, path) === undefined) out.push(e.op === 'sub' ? sub(b, a) : sub(a, b))
      return
    }
    default: return unreachable(e)
  }
}
function openC(c: C, path: Path, out: Lin[]): void {
  if (truth(c, path) !== undefined) return
  if (c.op === 'flag') return
  if (c.op === 'not') return openC(c.x, path, out)
  if (c.op === 'and' || c.op === 'or') return c.xs.forEach(y => openC(y, path, out))
  openE(c.a, path, out), openE(c.b, path, out)
  const a = linear(c.a, path), b = linear(c.b, path)
  if (a && b) {
    const d = sub(a, b)
    if (c.op === '<=') out.push(d)
    else if (c.op === '<') out.push(add(d, k(1)))
    else out.push(d, scale(d, -1))
  }
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
  if (c.op === 'flag') return
  const before = out.length
  openE(c.a, path, out), openE(c.b, path, out)
  if (out.length === before && !positive && c.op === '=' && truth(c, path) === undefined) openC(c, path, out)
}

// Pairs of reads of one map whose keys the path doesn't yet compare.
function openCells(rows: {lin: Lin}[], path: Path): Lin[] {
  const names = [...new Set(rows.flatMap(r => Object.keys(r.lin)))].filter(n => n.includes('['))
  const out: Lin[] = []
  const keyText = (n: string) => n.slice(n.indexOf('[') + 1, -1)
  for (const [i, p] of names.entries()) for (const q of names.slice(i + 1)) {
    if (p.slice(0, p.indexOf('[')) !== q.slice(0, q.indexOf('['))) continue
    const d = sub(parse(keyText(p)), parse(keyText(q)))
    const dec = (lin: Lin) => path.get(canon(lin))?.holds ?? (path.has(canon(add(k(1), scale(lin, -1)))) ? !path.get(canon(add(k(1), scale(lin, -1))))!.holds : undefined)
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

export type Outcome = {tree: Tree, nodes: number} | {stuck: 'sat' | 'unknown', witness?: Record<string, number>, path: Path}

// The budget: 200,000 nodes and, by default, 20 seconds per goal; past either the goal is left `unknown`.
export function grow(goal: Goal, path: Path = new Map(), budget: {nodes: number, until?: number} = {nodes: 0, until: performance.now() + 20_000}): Outcome {
  if (++budget.nodes > 200_000 || (budget.until !== undefined && performance.now() > budget.until)) return {stuck: 'unknown', path}
  const rows = leafConstraints(goal, path)
  const verdict = solve(rows)
  if (verdict.kind === 'refuted') return {tree: {leaf: verdict.steps}, nodes: budget.nodes}
  const open: Lin[] = []
  for (const h of goal.hyps) openH(h, path, open)
  open.push(...openCells(rows, path))
  let split = open.find(lin => Object.keys(lin).some(key => key !== '1') && !path.has(canon(lin)) && !path.has(canon(add(k(1), scale(lin, -1)))))
    ?? (verdict.kind === 'unknown' ? bisect(rows, path) ?? fractional(verdict.point, path) : undefined)
  // Products: with monomials about, try every pair of rows multiplied; failing that, split a factor at zero.
  const monomials = rows.some(r => Object.keys(r.lin).some(key => key.includes('*')))
  // A witness that multiplies out (each monomial's value is its factors' product) is a real model: nothing to refute.
  if (!split && monomials && verdict.kind === 'sat') {
    const w = verdict.witness, value = (key: string) => w[key] ?? 0
    const real = rows.every(r => Object.keys(r.lin).every(key => !key.includes('*') || value(key) === key.split('*').reduce((acc, f) => acc * value(f), 1)))
    if (real) return {stuck: 'sat', witness: w, path}
  }
  if (!split && monomials && rows.length <= 40) {
    // Only rows about the factors (no map cells), each pair once: elimination over hundreds of products blows up.
    const factorSet = new Set(rows.flatMap(r => Object.keys(r.lin).filter(key => key.includes('*')).flatMap(key => key.split('*'))))
    const relevant = rows.flatMap((r, i) => (Object.keys(r.lin).every(key => key === '1' || (!key.includes('[') && key.split('*').every(f => factorSet.has(f)))) ? [i] : []))
    const pairs: [number, number][] = []
    for (const [a, i] of relevant.entries()) for (const j of relevant.slice(a)) pairs.push([i, j])
    pairs.splice(300)
    const product = solve(withProducts(rows, pairs))
    if (product.kind === 'refuted') return {tree: {leaf: product.steps, products: pairs}, nodes: budget.nodes}
    // Degree three: each row times each product of two variables (x·y >= 0 is the pair of -x <= 0 and -y <= 0).
    const degree = Math.max(...rows.flatMap(r => Object.keys(r.lin).map(key => (key === '1' ? 0 : key.split('*').length))))
    if (degree >= 3) {
      const signs = rows.flatMap((r, i) => (Object.keys(r.lin).length === 1 && Object.values(r.lin)[0]! < 0 && !Object.keys(r.lin)[0]!.includes('*') && !Object.keys(r.lin)[0]!.includes('[') ? [i] : []))
      const sq: [number, number][] = signs.flatMap((i, a) => signs.slice(a).map(j => [i, j] as [number, number])), cubes: [number, number][] = []
      for (let s = 0; s < sq.length; s++) for (let i = 0; i < rows.length; i++) cubes.push([rows.length + s, i])
      const third = solve(withProducts(rows, [...sq, ...cubes]))
      if (third.kind === 'refuted') return {tree: {leaf: third.steps, products: [...sq, ...cubes]}, nodes: budget.nodes}
    }
    const factors = [...new Set(rows.flatMap(r => Object.keys(r.lin).filter(key => key.includes('*')).flatMap(key => key.split('*'))))]
    const fresh = (lin: Lin) => !path.has(canon(lin)) && !path.has(canon(add(k(1), scale(lin, -1))))
    // Split a factor at zero, else two factors against each other (so (x - y)² >= 0 becomes a product of rows).
    const zero = factors.find(f => fresh({[f]: 1}))
    const apart = factors.flatMap((f, i) => factors.slice(i + 1).map(g => ({[f]: 1, [g]: -1}) as Lin)).find(fresh)
    if (zero) split = {[zero]: 1}
    else if (apart) split = apart
  }
  if (!split) return {stuck: verdict.kind === 'sat' ? 'sat' : 'unknown', ...(verdict.kind === 'sat' ? {witness: verdict.witness} : {}), path}
  const id = canon(split)
  const yes = grow(goal, new Map(path).set(id, {lin: split, holds: true}), budget)
  if (!('tree' in yes)) return yes
  const no = grow(goal, new Map(path).set(id, {lin: split, holds: false}), budget)
  if (!('tree' in no)) return no
  return {tree: {split, yes: yes.tree, no: no.tree}, nodes: budget.nodes}
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
      if (!path.has(canon(lin)) && !path.has(canon(add(k(1), scale(lin, -1))))) return lin
    }
  }
  return undefined
}

// Branch and bound for unbounded systems: split on a variable the rational solution puts between two integers.
function fractional(point: Record<string, number> | undefined, path: Path): Lin | undefined {
  for (const [x, value] of Object.entries(point ?? {})) {
    if (Math.abs(value - Math.round(value)) < 1e-9 || x.includes('*')) continue
    const c = Math.floor(value), lin: Lin = c === 0 ? {[x]: 1} : {[x]: 1, 1: -c}
    if (!path.has(canon(lin)) && !path.has(canon(add(k(1), scale(lin, -1))))) return lin
  }
  return undefined
}

// The keys a proof assumes the every-key laws at: every key the step and the laws read, and the fresh key of the goal.
function readKeys(m: Machine, laws: Law[]): E[] {
  const out = new Map<string, E>()
  const inE = (e: E): void => {
    if (e.op === 'get') (out.set(JSON.stringify(e.key), e.key), inE(e.key))
    else if (e.op === 'if') (inC(e.c), inE(e.then), inE(e.else))
    else if (e.op === 'mul') inE(e.a)
    else if ('a' in e) (inE(e.a), inE(e.b))
  }
  const inC = (c: C): void => (c.op === 'flag' ? undefined : c.op === 'not' ? inC(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.forEach(inC) : (inE(c.a), inE(c.b)))
  Object.values(m.step.state ?? {}).forEach(inE)
  Object.values(m.step.flags ?? {}).forEach(inC)
  for (const w of Object.values(m.step.maps ?? {})) (out.set(JSON.stringify(w.key), w.key), inE(w.key), inE(w.value))
  for (const l of laws.filter(l => !l.forall)) inC(l.holds)
  return [...out.values()]
}

export type Report = {proven: boolean, nodes: number, leaves: number, failed?: {goal: string, stuck: string, witness?: Record<string, number>}, checked: boolean}

export function proveLaws(m: Machine, laws: Law[]): Report & {proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}} {
  const keys = readKeys(m, laws)
  const instances: Record<string, Instances> = {}
  for (const law of laws) instances[law.name] = Object.fromEntries(laws.filter(l => l.forall).map(l => [l.name, [...keys, ...(law.forall ? [{op: 'var', name: `${law.forall}#`} as E] : [])]]))
  const trees: Record<string, Tree> = {}
  let nodes = 0, leaves = 0
  for (const goal of obligations(m, laws, instances)) {
    const out = grow(goal)
    if (!('tree' in out)) return {proven: false, nodes, leaves, failed: {goal: goal.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {})}, checked: false}
    trees[goal.name] = out.tree
    nodes += out.nodes
    leaves += countLeaves(out.tree)
  }
  const proof = {instances, trees}
  return {proven: true, nodes, leaves, checked: checkLaws(m, laws, proof), proof}
}
// Step laws (kernel.ts's stepLawObligations): the laws proven first (they are assumed), then one goal per step law, the
// every-key laws assumed at every key the step, the laws and the step laws read.
export function proveStepLaws(m: Machine, laws: Law[], stepLaws: StepLaw[]): Report & {proof?: {laws: {instances: Record<string, Instances>, trees: Record<string, Tree>}, instances: Instances, trees: Record<string, Tree>}} {
  const base = proveLaws(m, laws)
  if (!base.proven || !base.proof) return {proven: false, nodes: base.nodes, leaves: base.leaves, ...(base.failed ? {failed: base.failed} : {}), checked: false}
  const plain = m.history ? historyMachine(m).machine : m
  const keys = [...readKeys(plain, laws), ...stepLaws.flatMap(sl => [...readKeysC(sl.then), ...(sl.when ? readKeysC(sl.when) : [])])]
  const instances: Instances = Object.fromEntries(laws.filter(l => l.forall).map(l => [l.name, keys]))
  const trees: Record<string, Tree> = {}
  let nodes = base.nodes, leaves = base.leaves
  for (const sl of stepLaws) for (const goal of stepLawObligations(m, laws, instances, sl)) {
    const out = grow(goal)
    if (!('tree' in out)) return {proven: false, nodes, leaves, failed: {goal: goal.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {})}, checked: false}
    trees[goal.name] = out.tree
    nodes += out.nodes
    leaves += countLeaves(out.tree)
  }
  const proof = {laws: base.proof, instances, trees}
  return {proven: true, nodes, leaves, checked: checkStepLaws(m, laws, stepLaws, proof), proof}
}
// The key terms a condition reads maps at; a primed map's key is a key of the map before the step too.
function readKeysC(c: C): E[] {
  const out: E[] = []
  const inE = (e: E): void => { if (e.op === 'get') (out.push(e.key), inE(e.key)); else if (e.op === 'if') (inC(e.c), inE(e.then), inE(e.else)); else if (e.op === 'mul') inE(e.a); else if ('a' in e) (inE(e.a), inE(e.b)) }
  const inC = (x: C): void => (x.op === 'flag' ? undefined : x.op === 'not' ? inC(x.x) : x.op === 'and' || x.op === 'or' ? x.xs.forEach(inC) : (inE(x.a), inE(x.b)))
  inC(c)
  return out
}

export const countLeaves = (t: Tree): number => ('leaf' in t ? 1 : countLeaves(t.yes) + countLeaves(t.no))

// A real counterexample for a goal the prover couldn't close (with products, its witness may be abstract): the free
// variables over 0..bound, every hypothesis evaluated with true arithmetic. Goals that read maps are left to the
// machine searches (search/), which run whole histories.
export function concretize(goal: Goal, bound = 12): Record<string, number> | undefined {
  const names = new Set<string>()
  let reads = false
  const walkE = (e: E): void => { if (e.op === 'var') names.add(e.name); else if (e.op === 'get') reads = true; else if (e.op === 'if') (walkC(e.c), walkE(e.then), walkE(e.else)); else if ('a' in e) (walkE(e.a), 'b' in e && walkE(e.b)) }
  const walkC = (c: C): void => (c.op === 'flag' ? undefined : c.op === 'not' ? walkC(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.forEach(walkC) : (walkE(c.a), walkE(c.b)))
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
    : c.op === 'flag' ? false : c.op === '<' ? ev(c.a, env) < ev(c.b, env) : c.op === '<=' ? ev(c.a, env) <= ev(c.b, env) : ev(c.a, env) === ev(c.b, env)
  const vars = [...names]
  const total = (bound + 1) ** vars.length
  for (let i = 0; i < total; i++) {
    let rest = i
    const env = Object.fromEntries(vars.map(v => { const d = rest % (bound + 1); rest = Math.floor(rest / (bound + 1)); return [v, d] }))
    if (goal.hyps.every(h => holds(h, env))) return env
  }
  return undefined
}
