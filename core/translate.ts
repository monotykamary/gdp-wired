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
import type {C, E} from './machine.ts'
import {type Lin, type Step, add, scale} from './solver.ts'
import {checkRefutation} from './check.ts'
import {type Goal, type Path, type Subst, type Tree, canon, canonFlip, columnTerm, factorsOf, isCell, isMonomial, leafConstraintsReusing, linear, substE, truth, withProducts} from '../kernel/kernel.ts'
import {cellProducts, grow} from '../kernel/prove.ts'

// How the usual goal's names read in the node's: `s`, a substitution of its variables and maps (which builds the node's
// goal from the usual one's hypotheses); `cells`, each map whose cell k is read at `at` + k·Ω in the node's goal (the
// substitution's map there), by its name there.
export type Rename = {s: Subst, cells?: Record<string, {to: string, at: E}>}
const omega = 'O$'

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

// What a translation did: its leaves, those grown again, and the splits made first (`decide`).
export type TStats = {leaves: number, regrown: number, splits: number}
export const tstats = (): TStats => ({leaves: 0, regrown: 0, splits: 0})
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
export function translate(part: Goal, whole: Goal, tree: Tree, ren: Renamer, st: TStats, until: number, pp: Path = new Map(), wp: Path = new Map()): Tree | undefined {
  if (!('leaf' in tree)) {
    const id = canon(tree.split), wl = ren(tree.split, wp)
    if (!wl) { st.regrown++; return regrow(whole, wp, until) }
    const k0 = known(wl, wp)
    if (k0 !== undefined) return translate(part, whole, k0 ? tree.yes : tree.no, ren, st, until, new Map(pp).set(id, {lin: tree.split, holds: k0}), wp)
    const wid = canon(wl)
    const yes = translate(part, whole, tree.yes, ren, st, until, new Map(pp).set(id, {lin: tree.split, holds: true}), new Map(wp).set(wid, {lin: wl, holds: true}))
    const no = yes && translate(part, whole, tree.no, ren, st, until, new Map(pp).set(id, {lin: tree.split, holds: false}), new Map(wp).set(wid, {lin: wl, holds: false}))
    return yes && no ? {split: wl, yes, no} : undefined
  }
  st.leaves++
  const rp = leafConstraintsReusing(part, pp), rw = leafConstraintsReusing(whole, wp), at = new Map<string, number>()
  rw.forEach((r, i) => { const key = canon(r.lin); if (!at.has(key)) at.set(key, i) })
  const map = (i: number): number | undefined => { if (i >= rp.length) return i - rp.length + rw.length; const l = ren(rp[i]!.lin, wp); return l && at.get(canon(l)) }
  const leaf: Step[] = [], products: [number, number][] = [], squares = (tree.squares ?? []).map(s => ren(s, wp))
  let ok = squares.every(Boolean)
  for (const s of ok ? tree.leaf : []) { if (s.kind !== 'input') { leaf.push(s); continue } const j = map(s.index); if (j === undefined) { ok = false; break } leaf.push({...s, index: j}) }
  for (const [i, j] of ok ? tree.products ?? [] : []) { const a = map(i), b = map(j); if (a === undefined || b === undefined) { ok = false; break } products.push([a, b]) }
  if (ok && checkRefutation(withProducts(rw, products, squares as Lin[]), leaf)) return {leaf, ...(tree.products ? {products} : {}), ...(tree.squares ? {squares: squares as Lin[]} : {})}
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
    const no = yes && regrow(whole, new Map(wp).set(id, {lin, holds: false}), until)
    return yes && no ? {split: lin, yes, no} : undefined
  }
  return inner(wp)
}
