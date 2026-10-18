// An untrusted prover for the kernel: grows a split tree until every leaf's constraints are refuted by solve(), splitting
// on whatever atom the hypotheses leave open (an if's condition, a min's or ∸'s comparison, a disjunction's atoms, two
// reads of one map at keys not yet known equal or apart). Its trees go to kernel.check; nothing it says is trusted.
import type {C, E, Law, Machine} from '../core/machine.ts'
import {type Lin, add, k, scale, solve, sub} from '../core/solver.ts'
import {type Goal, type Instances, type Liveness, type Path, type StepLaw, type Tree, canon, check, checkLaws, checkStepLaws, historyMachine, leafConstraints, linear, livenessHelpful, livenessParts, obligations, plainKey, progressObligations, stepLawObligations, trueC, truth, unreachable, withProducts} from './kernel.ts'

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
  if (c.op === 'flag' || c.op === 'all') return
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
  if (c.op === 'flag' || c.op === 'all') return
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

// The budget: 200,000 nodes and, by default, a second per hypothesis (at least 20 seconds) per goal; past either the goal
// is left `unknown`. A goal with many instances (a law about two keys at its pairs) has that many more rows per leaf.
export function grow(goal: Goal, path: Path = new Map(), budget: {nodes: number, until?: number} = {nodes: 0, until: performance.now() + Math.max(20_000, 1_000 * goal.hyps.length)}): Outcome {
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
// A key bound by a quantified flag or a write at every key isn't one: those reads are at every key already.
function readKeys(m: Machine, laws: Law[]): E[] {
  const out = new Map<string, E>()
  const bound = new Set<string>([...Object.values(m.step.flags ?? {}).flatMap(c => (c.op === 'all' ? [c.key] : [])), ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [w.each] : []))])
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
    const n = l.keys.length + 1
    const reads = (e: E, x?: string) => x !== undefined && JSON.stringify(e).includes(`"name":${JSON.stringify(x)}`)
    const own = (i: number) => { const f = focus[i] ?? focus[0]; return keys.filter(e => reads(e, f) && focus.every(g => g === f || !reads(e, g))) }
    const R = keys.filter(e => !focus.some(f => reads(e, f)))
    const out = new Map<string, E[]>()
    for (let i = 0; i + n <= had.length; i += n) out.set(JSON.stringify(had.slice(i, i + n)), had.slice(i, i + n))
    const go = (i: number, tuple: E[], rest: boolean): void => {
      if (i === n) { out.set(JSON.stringify(tuple), tuple); return }
      for (const e of own(i)) go(i + 1, [...tuple, e], rest)
      if (!rest) for (const e of R) go(i + 1, [...tuple, e], true)
    }
    go(0, [], false)
    return [l.name, [...out.values()].flat()]
  }
  const seen = new Set(had.map(e => JSON.stringify(e)))
  return [l.name, [...had, ...keys.filter(e => { const id = JSON.stringify(e); return seen.has(id) ? false : (seen.add(id), true) })]]
}))})
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
  if (f.keys?.length) return [f.name, tuples(keys, f.keys.length + 1)]
  const had = inst[f.name] ?? [], seen = new Set(had.map(e => JSON.stringify(e)))
  const reads = fnKeys(m, [{name: '', hyps: [f.holds]}])
  const at = [...keys, ...reads.flatMap(pattern => keys.flatMap(key => { const b = match(pattern, key, f.forall!); return b ? [b] : [] }))]
  return [f.name, [...had, ...at.filter(e => { const id = JSON.stringify(e); return seen.has(id) ? false : (seen.add(id), true) })]]
}))})
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
// Each quantified flag's witness w?f: a key where its condition fails, when it does; every-key facts are wanted there too.
const witnesses = (m: Machine): E[] => Object.entries(m.step.flags ?? {}).flatMap(([f, c]) => (c.op === 'all' ? [{op: 'var', name: `w?${f}`} as E] : []))
// The keys each quantified flag is assumed at (instances under ?f).
const flagInstances = (m: Machine, keys: E[]): Instances => Object.fromEntries(Object.entries(m.step.flags ?? {}).flatMap(([f, c]) => (c.op === 'all' ? [[`?${f}`, keys]] : [])))

export type Report = {proven: boolean, nodes: number, leaves: number, failed?: {goal: string, stuck: string, witness?: Record<string, number>}, checked: boolean}

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
function proveLawsAsGiven(m: Machine, laws: Law[]): Report & {proof?: {instances: Record<string, Instances>, trees: Record<string, Tree>}} {
  const keys = [...readKeys(m, laws), ...witnesses(m)]
  const instances: Record<string, Instances> = {}
  for (const law of laws) {
    const at = [...keys, ...(law.forall ? [{op: 'var', name: `${law.forall}#`} as E] : []), ...(law.keys ?? []).map((name): E => ({op: 'var', name}))]
    instances[law.name] = {...Object.fromEntries(laws.filter(l => l.forall).map(l => [l.name, l.keys?.length ? [] : at])), ...flagInstances(m, at)}
  }
  // The facts about functions, at every key each law's goals read a function at (found from the goals, twice round).
  for (let round = 0; round < 2 && m.facts?.length; round++) {
    const goals = obligations(m, laws, instances)
    laws.forEach((law, i) => { instances[law.name] = withFacts(m, instances[law.name]!, fnKeys(m, goals.slice(2 * i, 2 * i + 2))) })
  }
  // Where positions shift (a write at every key reading its key at k ∸ 1 or k + 1) or a law is about two keys, the
  // every-key laws also at each key the goals read a map at, once round.
  if (shifts(m) || laws.some(l => l.keys?.length)) {
    const goals = obligations(m, laws, instances)
    laws.forEach((law, i) => { instances[law.name] = withReads(laws, instances[law.name]!, mapKeys(goals.slice(2 * i, 2 * i + 2)), [...(law.forall ? [`${law.forall}#`] : []), ...(law.keys ?? [])]) })
  }
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
  const keys = [...readKeys(plain, laws), ...witnesses(plain), ...stepLaws.flatMap(sl => [sl.then, ...(sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when])].flatMap(readKeysC)),
    ...stepLaws.flatMap(sl => [sl.forall, ...(sl.keys ?? [])].flatMap(key => (key ? [{op: 'var', name: key} as E] : [])))]
  let instances: Instances = {...Object.fromEntries(laws.filter(l => l.forall).map(l => [l.name, l.keys?.length ? [] : keys])), ...flagInstances(plain, keys)}
  for (let round = 0; round < 2 && plain.facts?.length; round++) instances = withFacts(plain, instances, fnKeys(plain, stepLaws.flatMap(sl => stepLawObligations(m, laws, instances, sl))))
  // Where positions shift or a law is about two keys, each step law gets its own instances, from its own goal.
  const perStep: Record<string, Instances> = {}
  if (shifts(plain) || laws.some(l => l.keys?.length)) for (const sl of stepLaws) perStep[sl.name] = withReads(laws, instances, mapKeys(stepLawObligations(m, laws, instances, sl)), [sl.forall, ...(sl.keys ?? [])].flatMap(k => (k ? [k] : [])))
  const trees: Record<string, Tree> = {}
  let nodes = base.nodes, leaves = base.leaves
  for (const sl of stepLaws) for (const goal of stepLawObligations(m, laws, perStep[sl.name] ?? instances, sl)) {
    const out = grow(goal)
    if (!('tree' in out)) return {proven: false, nodes, leaves, failed: {goal: goal.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {})}, checked: false}
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
  let instances: Instances = {...withReads(ls, {}, mapKeys(progressObligations(m, ls, {}, p)), []), ...flagInstances(m, mapKeys(progressObligations(m, ls, {}, p)))}
  instances = {...instances, ...withReads(ls, instances, mapKeys(progressObligations(m, ls, instances, p)), [])}
  if (m.facts?.length) instances = withFacts(m, instances, fnKeys(m, progressObligations(m, ls, instances, p)))
  const trees: Record<string, Tree> = {}
  let nodes = base.nodes, leaves = base.leaves
  for (const goal of progressObligations(m, ls, instances, p)) {
    const out = grow(goal)
    if (!('tree' in out)) return {proven: false, nodes, leaves, failed: {goal: goal.name, stuck: out.stuck, ...(out.witness ? {witness: out.witness} : {})}, checked: false}
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
// machine searches (search/), which run whole histories.
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

// A goal built from its instances (an exporter's goal, shaped as its Lean twin builds it): the every-key laws, the
// quantified flags and the facts assumed at every key it reads a map or function at, then a tree, checked.
export function proveBuilt(m: Machine, laws: Law[], build: (inst: Instances) => Goal): {proven: boolean, instances?: Instances, goal?: Goal, tree?: Tree} {
  let instances: Instances = {}
  for (let round = 0; round < 2; round++) {
    const g = build(instances), keys = mapKeys([g])
    instances = {...withReads(laws, instances, keys, []), ...flagInstances(m, keys)}
    if (m.facts?.length) instances = withFacts(m, instances, fnKeys(m, [build(instances)]))
  }
  const goal = build(instances), out = grow(goal)
  if (!('tree' in out) || !check(goal, out.tree)) return {proven: false}
  return {proven: true, instances, goal, tree: out.tree}
}
