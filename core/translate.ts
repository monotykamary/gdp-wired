// A usual proof's tree made a cyclic node's. Untrusted: kernel/cyclic.ts checks the proof it ends in.
//
// An instance's node after a step (core/cyclic.ts: a machine's law after a step from t − 1, a recurrence's lemma after
// a step to x, a fold's law from a node's children) is the usual rule's step goal read over the instance's cells: each
// state variable s as s@[t − 1], each map's cell M[k] as M@[(t − 1) + k·Ω], a fresh key k# as the node's own k. Its
// goal is built so that it holds every hypothesis of that goal read so (and more: the run's bounds, the naturals), and
// the usual goal's tree is then read over it: each column of the usual goal (a variable, a cell, a term column, a
// monomial) is a linear form of the node's goal (`renamer`), each split the renamed split, each leaf's rows found again
// among the node's rows at the renamed path. A leaf whose rows aren't all there (two cells the path proves equal, whose
// keys over Ω the node's path doesn't yet compare) is grown again on the node's goal at its path (`regrown`); a split the
// node's path already decides is followed, not made again.
import {type C, type E, walk} from './machine.ts'
import {type Lin, type Step, add, env, refuteFast, scale, solve} from './solver.ts'
import {checkRefutation} from './check.ts'
import {type Goal, type Path, type Subst, type Tree, canon, canonFlip, columnTerm, factorsOf, isCell, isMonomial, leafConstraintsReusing, linear, substE, truth, withProducts} from '../kernel/kernel.ts'
import {cellProducts, clock, grow} from '../kernel/prove.ts'

// How the usual goal's names read in the node's: `s`, a substitution of its variables and maps (which builds the node's
// goal from the usual one's hypotheses); `cells`, each map whose cell k is read at `at` + k·Ω in the node's goal (the
// substitution's map there), by its name there.
export type Rename = {s: Subst, cells?: Record<string, {to: string, at: E}>}
const omega = 'O$'
const debugOn = () => !!env.GDP_CYCLIC_DEBUG

// The kernel's product of two linear forms (kernel.ts's `times`): each monomial its factors sorted, joined by '*'.
function times(a: Lin, b: Lin): Lin | undefined {
  const out: Lin[] = []
  for (const [p, cp] of Object.entries(a)) for (const [q, cq] of Object.entries(b)) {
    if (p.includes('⟦') || q.includes('⟦')) return undefined
    const fs = [...(p === '1' ? [] : factorsOf(p)), ...(q === '1' ? [] : factorsOf(q))].sort()
    out.push({[fs.length ? fs.join('*') : '1']: cp * cq})
  }
  return add(...out)
}
// A cell's key, from its name (`M[key]`, the key's canonical text, whose names may be cells themselves).
function keyOf(cell: string): Lin {
  const text = cell.slice(cell.indexOf('[') + 1, -1), out: Lin = {}
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

// A linear form of the usual goal read in the node's, at the node's path: undefined where a column has no linear form
// there (a product of a term column).
export type Renamer = (lin: Lin, wp: Path) => Lin | undefined
export function renamer(r: Rename): Renamer {
  const terms = new Map<string, E>(), memo = new WeakMap<Path, Map<string, Lin | undefined>>(), cells = r.cells ?? {}
  const col = (name: string, wp: Path): Lin | undefined => {
    let m = memo.get(wp)
    if (!m) memo.set(wp, (m = new Map()))
    if (m.has(name)) return m.get(name)
    const out = colOf(name, wp)
    m.set(name, out)
    return out
  }
  const colOf = (name: string, wp: Path): Lin | undefined => {
    if (name.startsWith('⟦')) {
      let e = terms.get(name)
      if (!e) { const t = columnTerm(name); if (!t) return undefined; terms.set(name, (e = substE(t, r.s))) }
      return linear(e, wp)
    }
    if (isMonomial(name)) {
      let out: Lin | undefined = {1: 1}
      for (const f of factorsOf(name)) { const l = col(f, wp); out = out && l && times(out, l) }
      return out
    }
    if (isCell(name)) {
      const map = name.slice(0, name.indexOf('[')), key = lin(keyOf(name), wp)
      if (!key) return undefined
      const to = cells[map]
      if (!to) return {[`${map}[${canon(key)}]`]: 1}
      const u = linear(to.at, wp), ko = times(key, {[omega]: 1})
      return u && ko ? {[`${to.to}[${canon(add(u, ko))}]`]: 1} : undefined
    }
    const e = r.s.vars[name]
    return e ? linear(e, wp) : {[name]: 1}
  }
  const lin: Renamer = (l, wp) => {
    const parts: Lin[] = []
    for (const key in l) {
      if (key === '1') { parts.push({1: l[key]!}); continue }
      const c = col(key, wp)
      if (!c) return undefined
      parts.push(scale(c, l[key]!))
    }
    return add(...parts)
  }
  return lin
}

// What a translation did: its leaves, those grown again, the splits it made (`decide`, `carry`), the nodes `carry`
// made a tree for and those it didn't (then grown), and whether the proof was one made before (core/cyclic.ts).
export type TStats = {leaves: number, regrown: number, splits: number, carried: number, uncarried: number, cached: number}
export const tstats = (): TStats => ({leaves: 0, regrown: 0, splits: 0, carried: 0, uncarried: 0, cached: 0})
const known = (lin: Lin, wp: Path): boolean | undefined => {
  if (Object.keys(lin).every(key => key === '1')) return (lin['1'] ?? 0) <= 0
  const a = wp.get(canon(lin))
  if (a) return a.holds
  const b = wp.get(canonFlip(lin))
  return b ? !b.holds : undefined
}
// The node's goal grown at a path (cell products on, as every cyclic goal is), within the deadline.
function regrow(whole: Goal, wp: Path, until: number): Tree | undefined {
  const was = cellProducts.on
  cellProducts.on = true
  try { const o = grow(whole, wp, {nodes: 0, until}); return 'tree' in o ? o.tree : undefined } finally { cellProducts.on = was }
}

// The usual tree for `part` read as a tree for `whole` (whose hypotheses hold part's, renamed), from the paths given.
// `swaps`: usual keys read as others (a cell at the first read as the cell at the second): where the path has a write's
// key W equal to a key K the node's conclusion reads its map at, that conclusion reads at K what the usual one reads at
// W (a write's reads at its key read at the key read, as the step's facts have them), so the usual cells at W are read
// as the cells at K (`readsFirst` decides the two equal or apart first).
export function translate(part: Goal, whole: Goal, tree: Tree, ren0: Renamer, st: TStats, until: number, pp: Path = new Map(), wp: Path = new Map(), swaps: [string, string][] = []): Tree | undefined {
  const ren: Renamer = swaps.length ? (lin, p) => {
    const out: Lin = {}
    for (const key in lin) {
      let to = key
      if (isCell(key)) { const kt = canon(keyOf(key)), sw = swaps.find(x => x[0] === kt); if (sw) to = `${key.slice(0, key.indexOf('['))}[${sw[1]}]` }
      out[to] = (out[to] ?? 0) + lin[key]!
    }
    return ren0(out, p)
  } : ren0
  if (!('leaf' in tree)) {
    const id = canon(tree.split), wl = ren(tree.split, wp)
    if (!wl) return close(whole, wp, st, until)
    const k0 = known(wl, wp)
    if (k0 !== undefined) return translate(part, whole, k0 ? tree.yes : tree.no, ren0, st, until, new Map(pp).set(id, {lin: tree.split, holds: k0}), wp, swaps)
    const wid = canon(wl)
    const yes = translate(part, whole, tree.yes, ren0, st, until, new Map(pp).set(id, {lin: tree.split, holds: true}), new Map(wp).set(wid, {lin: wl, holds: true}), swaps)
    const no = yes && translate(part, whole, tree.no, ren0, st, until, new Map(pp).set(id, {lin: tree.split, holds: false}), new Map(wp).set(wid, {lin: wl, holds: false}), swaps)
    return yes && no ? {split: wl, yes, no} : undefined
  }
  const rp = leafConstraintsReusing(part, pp), rw = leafConstraintsReusing(whole, wp), at = new Map<string, number>()
  rw.forEach((r, i) => { const key = canon(r.lin); if (!at.has(key)) at.set(key, i) })
  // Two cells the usual path proves equal (a row of the leaf's from their pair) are cells over time here, at keys
  // (t − 1) + a·Ω and (t − 1) + b·Ω: the path has a = b, and the keys' difference (a − b)·Ω is split (each other side
  // refuted by (a − b)·Ω = 0, the product of a − b <= 0 or b − a <= 0 with Ω >= 0), the leaf then read again.
  const usedRows = [...tree.leaf.flatMap(x => (x.kind === 'input' ? [x.index] : [])), ...(tree.products ?? []).flat()].filter(i => i < rp.length)
  for (const i of usedRows) {
    const src = rp[i]!.src
    if (!src || !('pair' in src)) continue
    const a = ren({[src.pair[0]]: 1}, wp), b = ren({[src.pair[1]]: 1}, wp), [ca] = Object.keys(a ?? {}), [cb] = Object.keys(b ?? {})
    if (!ca || !cb || !isCell(ca) || !isCell(cb)) continue
    const d = add(keyOf(ca), scale(keyOf(cb), -1)), q0: Lin = {}
    if (!Object.keys(d).length || Object.keys(d).some(key => key === '1' || !factorsOf(key).includes(omega))) continue
    for (const key of Object.keys(d)) { const fs = [...factorsOf(key)]; fs.splice(fs.indexOf(omega), 1); q0[fs.length ? fs.join('*') : '1'] = (q0[fs.length ? fs.join('*') : '1'] ?? 0) + d[key]! }
    for (const [l, q] of [[d, q0], [scale(d, -1), scale(q0, -1)]] as const) {
      const kd = known(l, wp)
      if (kd === true) continue
      if (kd === false) return apart(whole, wp, l, q, st, until)
      st.splits++
      const id = canon(l), yes = translate(part, whole, tree, ren0, st, until, pp, new Map(wp).set(id, {lin: l, holds: true}), swaps)
      const no = yes && apart(whole, new Map(wp).set(id, {lin: l, holds: false}), l, q, st, until)
      return yes && no ? {split: l, yes, no} : undefined
    }
  }
  st.leaves++
  const map = (i: number): number | undefined => { if (i >= rp.length) return i - rp.length + rw.length; const l = ren(rp[i]!.lin, wp); return l && at.get(canon(l)) }
  const leaf: Step[] = [], products: [number, number][] = [], squares = (tree.squares ?? []).map(s => ren(s, wp))
  let ok = squares.every(Boolean)
  for (const s of ok ? tree.leaf : []) { if (s.kind !== 'input') { leaf.push(s); continue } const j = map(s.index); if (j === undefined) { ok = false; break } leaf.push({...s, index: j}) }
  for (const [i, j] of ok ? tree.products ?? [] : []) { const a = map(i), b = map(j); if (a === undefined || b === undefined) { ok = false; break } products.push([a, b]) }
  if (ok && checkRefutation(withProducts(rw, products, squares as Lin[]), leaf)) return {leaf, ...(tree.products ? {products} : {}), ...(tree.squares ? {squares: squares as Lin[]} : {})}
  if (debugOn()) {
    const missing = tree.leaf.flatMap(s => (s.kind === 'input' && s.index < rp.length && map(s.index) === undefined ? [s.index] : []))
    console.error(`[leaf] ${whole.name}: ${ok ? 'rows found, refutation refused' : `${missing.length} rows missing`}${missing.slice(0, 3).map(i => `; ${JSON.stringify(rp[i]!.lin)} as ${JSON.stringify(ren(rp[i]!.lin, wp) ?? 'no form')}${rp[i]!.src ? ` (${JSON.stringify(rp[i]!.src)})` : ''}`).join('')}`)
  }
  return close(whole, wp, st, until)
}

// A write's key W and a key K the node's conclusion reads its map at (each usual terms, `wl`/`kl` their forms in the
// node's goal): decided equal or apart first, each in turn (equal, the cells' keys over Ω decided equal too, each other
// side refuted by the product: `apart`), then `inner` with the usual cells at each W found equal read at its K.
export type Reads = {k: E, w: E}[]
export function readsFirst(whole: Goal, reads: Reads, ren: Renamer, inner: (wp: Path, swaps: [string, string][]) => Tree | undefined, st: TStats, until: number, wp: Path = new Map(), swaps: [string, string][] = []): Tree | undefined {
  if (!reads.length) return inner(wp, swaps)
  const [r, ...rest] = reads, ku = linear(r!.k, new Map()), wu = linear(r!.w, new Map()), kl = ku && ren(ku, wp), wl = wu && ren(wu, wp)
  if (!ku || !wu || !kl || !wl) return readsFirst(whole, rest, ren, inner, st, until, wp, swaps)
  const q = add(kl, scale(wl, -1))
  if (!Object.keys(q).some(key => key !== '1')) return readsFirst(whole, rest, ren, inner, st, until, wp, swaps)
  const dq = times(q, {[omega]: 1})
  // The cases in turn: q <= 0, then -q <= 0 (equal), then the keys over Ω.
  const steps: {l: Lin, q?: Lin}[] = [{l: q}, {l: scale(q, -1)}, ...(dq ? [{l: dq, q}, {l: scale(dq, -1), q: scale(q, -1)}] : [])]
  const go = (i: number, p: Path): Tree | undefined => {
    if (i === steps.length) return readsFirst(whole, rest, ren, inner, st, until, p, [...swaps, [canon(wu), canon(ku)]])
    const {l, q: qq} = steps[i]!, kd = known(l, p)
    if (kd === true) return go(i + 1, p)
    if (kd === false) return i < 2 ? readsFirst(whole, rest, ren, inner, st, until, p, swaps) : apart(whole, p, l, qq!, st, until)
    st.splits++
    const id = canon(l), yes = go(i + 1, new Map(p).set(id, {lin: l, holds: true})), no = new Map(p).set(id, {lin: l, holds: false})
    const n = yes && (i < 2 ? readsFirst(whole, rest, ren, inner, st, until, no, swaps) : apart(whole, no, l, qq!, st, until))
    return yes && n ? {split: l, yes, no: n} : undefined
  }
  return go(0, wp)
}

// A path where l >= 1 (two cells' keys apart by l = q·Ω) while q <= 0 is a row: refuted by q·Ω <= 0, the product of
// that row and Ω >= 0.
function apart(whole: Goal, wp: Path, l: Lin, q: Lin, st: TStats, until: number): Tree | undefined {
  const rows = leafConstraintsReusing(whole, wp), find = (x: Lin) => { const c = canon(x); return rows.findIndex(r => canon(r.lin) === c) }
  const iq = find(q), io = find({[omega]: -1}), ia = find(add({1: 1}, scale(l, -1)))
  if (iq >= 0 && io >= 0 && ia >= 0) {
    const leaf: Step[] = [{kind: 'input', index: ia}, {kind: 'input', index: rows.length}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}], products: [number, number][] = [[iq, io]]
    if (checkRefutation(withProducts(rows, products), leaf)) { st.leaves++; return {leaf, products} }
  }
  st.regrown++
  return regrow(whole, wp, until)
}

// The atoms that make a condition true at the path (a comparison's, each lin <= 0), or undefined where it is no plain
// comparison or conjunction.
function atomsOf(c: C, wp: Path): Lin[] | undefined {
  if (c.op === 'and') { const out: Lin[] = []; for (const x of c.xs) { const a = atomsOf(x, wp); if (!a) return undefined; out.push(...a) } return out }
  if (c.op !== '<' && c.op !== '<=' && c.op !== '=') return undefined
  const a = linear(c.a, wp), b = linear(c.b, wp)
  if (!a || !b) return undefined
  const d = add(a, scale(b, -1))
  return c.op === '<=' ? [d] : c.op === '<' ? [add(d, {1: 1})] : [d, scale(d, -1)]
}
// A tree for `whole` that first decides each condition true (a guard, the antecedent of a use's implication), each
// other side grown on the goal (the node's hypotheses refute it), then `inner` at the path where all hold.
export function decide(whole: Goal, conds: C[], inner: (wp: Path) => Tree | undefined, st: TStats, until: number, wp: Path = new Map()): Tree | undefined {
  for (const [i, c] of conds.entries()) {
    if (truth(c, wp) === true) continue
    const atoms = atomsOf(c, wp)?.filter(l => known(l, wp) === undefined)
    if (!atoms?.length) { if (truth(c, wp) === false) return undefined; continue }
    const lin = atoms[0]!, id = canon(lin)
    st.splits++
    const yes = decide(whole, conds.slice(i), inner, st, until, new Map(wp).set(id, {lin, holds: true}))
    // (the other side refuted by the node's rows as they are, a time below the steps before it say, before it is grown)
    const np = new Map(wp).set(id, {lin, holds: false}), no = yes && (leafAt(whole, np, true, st) ?? regrow(whole, np, until))
    return yes && no ? {split: lin, yes, no} : undefined
  }
  return inner(wp)
}

// A leaf of `g` at the path: a hypothesis false there (its row 1 <= 0), or with `solveIt` the rows refuted by the solver.
function leafAt(g: Goal, wp: Path, solveIt: boolean, st: TStats): Tree | undefined {
  const rows = leafConstraintsReusing(g, wp), absurd = rows.findIndex(r => Object.keys(r.lin).every(key => key === '1') && (r.lin['1'] ?? 0) > 0)
  if (absurd >= 0) { st.leaves++; return {leaf: [{kind: 'input', index: absurd}]} }
  if (!solveIt) return undefined
  const fast = rows.length > 60 ? refuteFast(rows) : undefined, v = fast?.kind === 'refuted' ? fast : solve(rows)
  if (v.kind === 'refuted') { st.leaves++; return {leaf: v.steps} }
  // With monomials about (a law about cap·n over a node's children): each equation about a factor (a cell given by
  // the facts) times each factor's sign, as the prover's search does (kernel/prove.ts).
  if (!rows.some(r => Object.keys(r.lin).some(isMonomial))) return undefined
  const factors = new Set(rows.flatMap(r => Object.keys(r.lin).filter(isMonomial).flatMap(factorsOf)))
  const byCanon = new Map(rows.map((r, i) => [canon(r.lin), i]))
  const eqs = rows.flatMap((r, i) => (Object.keys(r.lin).some(key => key !== '1' && factors.has(key)) && byCanon.has(canon(scale(r.lin, -1))) ? [i] : []))
  const signs = rows.flatMap((r, i) => { const keys = Object.keys(r.lin); return keys.length === 1 && factors.has(keys[0]!) && r.lin[keys[0]!]! < 0 ? [i] : [] })
  const products = eqs.flatMap(i => signs.map(j => [i, j] as [number, number])).slice(0, 200)
  if (!products.length) return undefined
  const w = solve(withProducts(rows, products))
  if (w.kind !== 'refuted') return undefined
  st.leaves++
  return {leaf: w.steps, products}
}
const open = (c: C, wp: Path): Lin | undefined => atomsOf(c, wp)?.find(l => known(l, wp) === undefined)
// Two reads of one function at keys the path doesn't yet prove equal or apart, keys linear (keys through a choice's
// column after the others: such a column is often one the path decides later).
function cellAtom(g: Goal, wp: Path): Lin | undefined {
  const rows = leafConstraintsReusing(g, wp), names = [...new Set(rows.flatMap(r => Object.keys(r.lin)))].filter(isCell)
  let later: Lin | undefined
  for (const [i, p] of names.entries()) for (const q of names.slice(i + 1)) {
    if (p.slice(0, p.indexOf('[')) !== q.slice(0, q.indexOf('['))) continue
    const d = add(keyOf(p), scale(keyOf(q), -1))
    if (Object.keys(d).some(key => key !== '1' && isMonomial(key))) continue
    const column = Object.keys(d).some(key => key.includes('⟦'))
    for (const l of [d, scale(d, -1)]) if (Object.keys(l).some(key => key !== '1') && known(l, wp) === undefined) { if (!column) return l; later ??= l }
  }
  return later
}
// A choice the rows read open (an if's condition: a map's write, read at a key that may be the written one).
// Then one the conclusion refuted reads where it gives no rows yet (a condition read through such a choice).
const choiceOf = (e: E, wp: Path): Lin | undefined => {
  if (e.op === 'if') return truth(e.c, wp) === undefined ? open(e.c, wp) : undefined
  if (e.op !== 'sub' && e.op !== 'min' && e.op !== 'max') return undefined
  const a = linear(e.a, wp), b = linear(e.b, wp)
  if (!a || !b) return undefined
  const d = e.op === 'sub' ? add(b, scale(a, -1)) : add(a, scale(b, -1))
  return Object.keys(d).some(key => key !== '1') && known(d, wp) === undefined ? d : undefined
}
function choiceAtom(g: Goal, wp: Path): Lin | undefined {
  const rows = leafConstraintsReusing(g, wp)
  for (const name of new Set(rows.flatMap(r => Object.keys(r.lin)))) {
    const e = name.startsWith('⟦') ? columnTerm(name) : undefined
    const l = e && e.op === 'if' ? choiceOf(e, wp) : undefined
    if (l) return l
  }
  let found: Lin | undefined
  const walk = (x: unknown): void => {
    if (found || !x || typeof x !== 'object') return
    const o = x as E
    if ((o.op === 'if' || o.op === 'sub' || o.op === 'min' || o.op === 'max') && (found = choiceOf(o, wp))) return
    for (const val of Object.values(o)) walk(val)
  }
  walk(g.hyps.at(-1))
  return found
}
// The cells of the conclusion refuted at the path (reads it gives no rows of yet among them).
function conclCells(g: Goal, wp: Path): string[] {
  const out: string[] = []
  walk(g.hyps.at(-1), x => {
    const o = x as E
    if (o.op === 'get' && o.map.endsWith('@')) { const l = linear(o, wp); if (l) out.push(...Object.keys(l)) }
  })
  return out
}
// Two cells over time at keys u + a·Ω and u + b·Ω: a = b decided first, then the keys' difference, its other side
// refuted by the product (`apart`).
function omegaPair(g: Goal, wp: Path): {l: Lin, q?: Lin} | undefined {
  const rows = leafConstraintsReusing(g, wp), names = [...new Set([...rows.flatMap(r => Object.keys(r.lin)), ...conclCells(g, wp)])].filter(isCell)
  for (const [i, p] of names.entries()) for (const q of names.slice(i + 1)) {
    if (p.slice(0, p.indexOf('[')) !== q.slice(0, q.indexOf('['))) continue
    const d = add(keyOf(p), scale(keyOf(q), -1)), q0: Lin = {}
    if (!Object.keys(d).length || Object.keys(d).some(key => key === '1' || !factorsOf(key).includes(omega))) continue
    for (const key of Object.keys(d)) { const fs = [...factorsOf(key)]; fs.splice(fs.indexOf(omega), 1); const f = fs.length ? fs.join('*') : '1'; q0[f] = (q0[f] ?? 0) + d[key]! }
    if (Object.keys(q0).some(key => key.includes('⟦'))) continue
    const a = known(q0, wp), b = known(scale(q0, -1), wp)
    if (a === undefined) return {l: q0}
    if (a && b === undefined) return {l: scale(q0, -1)}
    if (!(a && b)) continue
    for (const [l, qq] of [[d, q0], [scale(d, -1), scale(q0, -1)]] as const) if (known(l, wp) === undefined) return {l, q: qq}
  }
  return undefined
}
// A case of `g` closed: refuted by its rows, else an open choice, two reads of a function or two cells over time split
// (each then equal), else the goal grown at the path.
export function close(g: Goal, wp: Path, st: TStats, until: number): Tree | undefined {
  const l = leafAt(g, wp, true, st)
  if (l) return l
  const pick = choiceAtom(g, wp) ?? cellAtom(g, wp), om = pick ? undefined : omegaPair(g, wp), next = pick ?? om?.l
  if (next && clock() < until) {
    st.splits++
    const id = canon(next), y = close(g, new Map(wp).set(id, {lin: next, holds: true}), st, until)
    const no = new Map(wp).set(id, {lin: next, holds: false}), n = y && (om?.q ? apart(g, no, next, om.q, st, until) : close(g, no, st, until))
    return y && n ? {split: next, yes: y, no: n} : undefined
  }
  st.regrown++
  if (env.GDP_CYCLIC_DEBUG) console.error(`[close] ${g.name}: grown again at ${[...wp.values()].map(a => `${JSON.stringify(a.lin)} ${a.holds}`).join('; ')}`)
  return regrow(g, wp, until)
}

// The node at t's tree, made rather than searched (`carry`): its goal is the law at t refuted against the law at the
// start or after the step (a use each, under its guard) and the facts that give the cells at t (each under its guard).
// Splits first decide the uses' guards and the facts' guards (each other side refuted by the node's hypotheses: the
// time's bounds), then each comparison of the law at t and the same comparison of the law it is carried from, in
// turn; a case where the two differ is refuted by the facts' equations (the cells at t are the terms the step gives),
// one where both are decided by whichever of the two hypotheses is then false. A case none of that refutes is grown on
// the goal at its path.
// `nUses`: the uses' hypotheses, just before the conclusion refuted (mainGoal's order).
export function carry(g: Goal, nFacts: number, nUses: number, st: TStats, until: number): Tree | undefined {
  const last = g.hyps.length - 1, uses = g.hyps.slice(last - nUses, last), facts = g.hyps.slice(last - nUses - nFacts, last - nUses)
  const law = (g.hyps[last] as Extract<C, {op: 'not'}>).x
  const parts = uses.map(u => (u.op === 'or' && u.xs.length === 2 && u.xs[0]!.op === 'not' ? {guard: u.xs[0]!.x, concl: u.xs[1]!} : {guard: undefined, concl: u}))
  // The comparisons of two instances of one law, in order, paired; where the law at t is an implication the other isn't
  // (a law between two points, x <= y → ..., carried from y = x), its antecedent first, decided alone.
  const pairs = (a: C, b: C, out: [C, C | undefined][] = []): [C, C | undefined][] => {
    if ((a.op === 'and' || a.op === 'or') && b.op === a.op && a.xs.length === b.xs.length) a.xs.forEach((x, i) => pairs(x, b.xs[i]!, out))
    else if (a.op === 'not' && b.op === 'not') pairs(a.x, b.x, out)
    else if ((a.op === '<' || a.op === '<=' || a.op === '=') && b.op === a.op) out.push([a, b])
    else if (a.op === 'or' && a.xs.length === 2 && a.xs[0]!.op === 'not') { out.push([a.xs[0]!.x, undefined]); pairs(a.xs[1]!, b, out) }
    return out
  }
  const paired = parts.map(p => pairs(law, p.concl))
  // The times before (t ∸ 1, x ∸ 1, y ∸ 1, each a choice until c <= v is decided), decided after the guards: then the
  // cells at t − 1 and at (t − 1) + 1 are the same reads.
  const prev: C[] = [], seenPrev = new Set<string>()
  walk(g.hyps, x => {
    const o = x as E
    if (o.op === 'sub' && o.a.op === 'var' && o.b.op === 'const' && !seenPrev.has(`${o.a.name}-${o.b.value}`)) { seenPrev.add(`${o.a.name}-${o.b.value}`); prev.push({op: '<=', a: o.b, b: o.a}) }
  })
  const guardsIn = (c: C, wp: Path, out: C[]): void => {
    if (c.op === 'and') { for (const x of c.xs) guardsIn(x, wp, out); return }
    if (c.op === 'or' && c.xs.length === 2 && c.xs[0]!.op === 'not') { const t = truth(c.xs[0]!.x, wp); if (t === undefined) out.push(c.xs[0]!.x); else if (t) guardsIn(c.xs[1]!, wp, out) }
  }
  const leafOf = (wp: Path, solveIt: boolean) => leafAt(g, wp, solveIt, st), final = (wp: Path) => close(g, wp, st, until)
  const node = (wp: Path, guardsDone: boolean): Tree | undefined => {
    if (clock() > until) return undefined
    // A hypothesis false at the path: the law at t holds there, or a law it is carried from (its guard true) fails.
    if (truth(law, wp) === true || parts.some(p => (p.guard === undefined || truth(p.guard, wp) === true) && truth(p.concl, wp) === false)) return final(wp)
    let next: Lin | undefined
    if (!guardsDone) {
      const gs: C[] = []
      for (const p of parts) if (p.guard && truth(p.guard, wp) === undefined) gs.push(p.guard)
      gs.push(...prev)
      for (const f of facts) guardsIn(f, wp, gs)
      for (const c of gs) if ((next = open(c, wp))) break
      if (!next) return node(wp, true)
    } else {
      // (the rows first: a law whose instances give rows as they are, a single comparison or the conjunctions their
      // signs open, needs no split)
      const l = leafOf(wp, true)
      if (l) return l
      for (const [i, p] of parts.entries()) {
        if (p.guard && truth(p.guard, wp) !== true) continue
        for (const [a, b] of paired[i]!) {
          const ta = truth(a, wp), tb = b && truth(b, wp)
          if (!b) { if (ta === undefined && (next = open(a, wp))) break; continue }
          if (ta !== undefined && tb !== undefined) { if (ta !== tb) return final(wp); continue }
          if ((next = ta === undefined ? open(a, wp) : open(b, wp))) break
        }
        if (next) break
      }
      if (!next) return final(wp)
    }
    st.splits++
    const id = canon(next), yes = new Map(wp).set(id, {lin: next, holds: true}), no = new Map(wp).set(id, {lin: next, holds: false})
    // (a guard's other side is refuted by the bounds at once: tried before splitting further)
    const side = (p: Path) => (guardsDone ? node(p, true) : leafOf(p, false) ?? quick(p) ?? node(p, false))
    const y = side(yes), n = y && side(no)
    return y && n ? {split: next, yes: y, no: n} : undefined
  }
  const quick = (wp: Path): Tree | undefined => { const rows = leafConstraintsReusing(g, wp), v = refuteFast(rows); if (v?.kind !== 'refuted') return undefined; st.leaves++; return {leaf: v.steps} }
  return node(new Map(), false)
}
