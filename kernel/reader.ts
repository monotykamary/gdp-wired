// Untrusted: the kernel's reading of a goal (kernel.ts's linear, truth, facts, termRows and leaf rows; prove.ts's open
// atoms), done again for a search that keeps its decisions on a trail (kernel/cdcl.ts), each value with its reason:
// the decisions it needs (a conjunction false needs one false part, a disjunction's last open part needs the others
// false, a term's value the decisions its choices took). A value with no open read is final: it holds at any path that
// keeps its reason (Kleene truth is monotone in the path), so it is kept across the search's nodes for as long as the
// trail keeps the latest decision of its reason (one stamp a trail position: the trail is a stack, so the position's
// stamp unchanged means every position below it is too). A value with an open read is found again at each node.
// A value with an open read is also kept while nothing it read has changed: each value's reads are noted (the values
// and the atoms it read), and a change of the trail at an atom (`touch`, which the search calls at each decision and
// each one taken back) marks every value that read it, and every value that read those, to be found again. A value
// found again would be the same (it is a function of what it read), so the search is as it was, only faster.
// Nothing here is trusted: the rows it gives are the kernel's (the search's tree is checked by kernel.ts at the end,
// and each leaf's derivation is found again among kernel.ts's rows when the search's refutation is unfolded).
import type {C, E} from '../core/machine.ts'
import {type Lin, add, costs, env, k, scale, sub, v} from '../core/solver.ts'
import {type Goal, atomOf, canon, canonFlip, columnTerm, factorsOf, isCell, termColumn} from './kernel.ts'

export type W = ReadonlySet<string>
export const none: W = new Set<string>()
export const join = (a: W, b: W): W => {
  if (!a.size || a === b) return b
  if (!b.size) return a
  // (one inside the other, often: a reason with the parts it already has; the same set, not a copy)
  const [s, l] = a.size <= b.size ? [a, b] : [b, a]
  let inside = true
  for (const x of s) if (!l.has(x)) { inside = false; break }
  if (inside) return l
  const out = new Set(a)
  for (const x of b) out.add(x)
  return out
}
// A trail: each decided atom (by its variable's name, the canonical text of its stored form) with its value and its
// position; each position's stamp.
export type Trail = {get(name: string): {val?: boolean, at: number} | undefined, stamp(at: number): number, size(): number, lin(at: number): {name: string, lin: Lin, holds: boolean}}
// A reason, its latest position on the trail, and whether the value read nothing open.
type R = {w: W, pos: number, fin: boolean}
const R0: R = {w: none, pos: -1, fin: true}, R1: R = {w: none, pos: -1, fin: false}
const unfin = (r: R): R => (r.fin ? {w: r.w, pos: r.pos, fin: false} : r)
const both = (a: R, b: R): R => ({w: join(a.w, b.w), pos: Math.max(a.pos, b.pos), fin: a.fin && b.fin})
type Kept = {pos: number, stamp: number, node: number}
type TV = R & Kept & {t: boolean | undefined}
type LV = R & Kept & {lin: Lin | undefined}
type FV = Kept & {rows: Row[], fin: boolean}
export type Row = {lin: Lin, w: W, label: ''}

// The kernel's product of two linear forms (kernel.ts's `times`): each monomial its factors sorted, joined by '*'.
export function times(a: Lin, b: Lin): Lin | undefined {
  const out: Lin[] = []
  for (const [p, cp] of Object.entries(a)) for (const [q, cq] of Object.entries(b)) {
    if (p.includes('⟦') || q.includes('⟦')) return undefined
    const fs = [...(p === '1' ? [] : factorsOf(p)), ...(q === '1' ? [] : factorsOf(q))].sort()
    out.push({[fs.length ? fs.join('*') : '1']: cp * cq})
  }
  return add(...out)
}
const one = k(1)
const namePair = new WeakMap<Lin, [string, string]>()
const constantLin = (l: Lin) => Object.entries(l).every(([key, c]) => key === '1' || c === 0)

// The last value made from some parts, made again only when a part is a different object: a node's linear forms are
// then the same objects as the node's before wherever they are equal, so what is remembered per form (canonical texts,
// the simplex's slacks) is found again.
type Last = {a: unknown, b: unknown, c: unknown, out: unknown}
const lasts: WeakMap<object, Last>[] = Array.from({length: 8}, () => new WeakMap())
function same<T>(site: number, owner: object, a: unknown, b: unknown, c: unknown, make: () => T): T {
  const m = lasts[site]!, had = m.get(owner)
  if (had && had.a === a && had.b === b && had.c === c) return had.out as T
  const out = make()
  m.set(owner, {a, b, c, out})
  return out
}

// GDP_READER_CLEAN=0: values with an open read found again at every node, as before (for comparing).
export const keepClean = env.GDP_READER_CLEAN !== '0'
// The key of a part of the live rows (`sync`): a hypothesis' facts (0, its index), a term column's rows (1, the column's
// name id), a pair of cells' (2, their name ids), a hypothesis' part's facts (3, its index and the part's).
class Seg { constructor(readonly kind: number, readonly i: number, readonly j = -1) {} }
type Finding = {key: object}
export class Reader {
  private node = 0
  private natRows = new Map<string, Row>()
  private atomRows = new Map<string, Row>()
  private ls = new Map<E, LV>()
  private ts = new Map<C, TV>()
  private fs: (FV | undefined)[] = []
  private os: ({lins: Lin[], node: number} | undefined)[] = []
  constructor(readonly goal: Goal, readonly trail: Trail) {}
  // A new node: values with an open read are found again, unless nothing they read has changed.
  begin() { this.node++ }
  // The reads: a value's key (its term, condition, or a hypothesis' facts or open atoms) → the keys of the values that
  // read it; an atom's name → the keys of the values that read it. A clean key's value stands.
  private up = new Map<object, Map<object, Finding>>()
  private byAtom = new Map<string, Map<object, Finding>>()
  // (each key's latest finding: a read is an edge to a finding, and one to a finding not its key's latest is no read
  // any more, dropped when a change walks past it)
  private found = new Map<object, Finding>()
  private lastUp = new WeakMap<object, Finding>()
  private clean = new Set<object>()
  private factKeys: Seg[] = []
  private openKeys: object[] = []
  private finding: Finding | undefined
  private read(key: object) {
    const f = this.finding
    if (!f || this.lastUp.get(key) === f) return
    this.lastUp.set(key, f)
    let s = this.up.get(key)
    if (!s) this.up.set(key, (s = new Map()))
    s.set(f.key, f)
  }
  private readAtom(name: string) {
    const f = this.finding
    if (!f) return
    let s = this.byAtom.get(name)
    if (!s) this.byAtom.set(name, (s = new Map()))
    s.set(f.key, f)
  }
  private within<T>(key: object, f: () => T): T {
    const was = this.finding, now = {key}
    costs.values++
    this.found.set(key, now)
    this.finding = now
    try { return f() } finally { this.finding = was }
  }
  // The trail changed at this atom (decided, or taken back): every value that read it, and every reader of those, all
  // the way up (a value kept as final reads below it values that are not clean).
  touch(name: string) {
    const todo: object[] = [], seen = new Set<object>(), found = this.found
    const walk = (edges: Map<object, Finding> | undefined) => {
      if (edges) { costs.edges += edges.size; for (const [k, f] of edges) { if (found.get(k) === f) todo.push(k); else edges.delete(k) } }
    }
    walk(this.byAtom.get(name))
    while (todo.length) {
      const key = todo.pop()!
      if (seen.has(key)) continue
      seen.add(key)
      this.clean.delete(key)
      if (key instanceof Seg && this.syncing) this.dirty.add(key)
      walk(this.up.get(key))
    }
  }
  private ok(x: Kept & {fin: boolean}, key: object): boolean {
    if ((keepClean && this.clean.has(key)) || x.node === this.node) return true
    if (x.fin && (x.pos < 0 || (x.pos < this.trail.size() && this.trail.stamp(x.pos) === x.stamp))) { this.clean.add(key); return true }
    return false
  }
  private units = new Map<string, W>()
  private unit(name: string): W { let w = this.units.get(name); if (!w) this.units.set(name, (w = new Set([name]))); return w }
  // Whether lin <= 0 is decided, and by what.
  dec(lin: Lin): R & {t: boolean | undefined} {
    let constant = true
    for (const key in lin) if (key !== '1') { constant = false; break }
    if (constant) return {w: none, pos: -1, fin: true, t: (lin['1'] ?? 0) <= 0}
    let names = namePair.get(lin)
    if (!names) namePair.set(lin, (names = [canon(lin), canonFlip(lin)]))
    const [a, f] = names
    this.readAtom(a); this.readAtom(f)
    const x = this.trail.get(a)
    if (x && x.val !== undefined) return {t: x.val, w: this.unit(a), pos: x.at, fin: true}
    const y = this.trail.get(f)
    if (y && y.val !== undefined) return {t: !y.val, w: this.unit(f), pos: y.at, fin: true}
    return {t: undefined, w: none, pos: -1, fin: false}
  }
  linear(e: E): LV {
    this.read(e)
    const had = this.ls.get(e)
    if (had && this.ok(had, e)) return had
    return this.within(e, () => this.linear0(e))
  }
  private linear0(e: E): LV {
    let lin: Lin | undefined, r: R = R0
    switch (e.op) {
      case 'var': lin = e.name === '1' || /[*[\],:⟦]/.test(e.name) ? undefined : same(0, e, 0, 0, 0, () => v(e.name)); break
      case 'const': lin = same(0, e, 0, 0, 0, () => k(e.value)); break
      case 'mul': { const a = this.linear(e.a); lin = a.lin && same(0, e, a.lin, 0, 0, () => scale(a.lin!, e.k)); r = a; break }
      case 'prod': { const a = this.linear(e.a), b = this.linear(e.b); lin = a.lin && b.lin && same(0, e, a.lin, b.lin, 0, () => times(a.lin!, b.lin!)); r = both(a, b); break }
      case 'add': { const a = this.linear(e.a), b = this.linear(e.b); lin = a.lin && b.lin && same(0, e, a.lin, b.lin, 0, () => add(a.lin!, b.lin!)); r = both(a, b); break }
      case 'sub': case 'min': case 'max': {
        const a = this.linear(e.a), b = this.linear(e.b)
        if (!a.lin || !b.lin) { lin = undefined; r = both(a, b); break }
        const d = this.dec(same(1, e, a.lin, b.lin, 0, () => (e.op === 'sub' ? sub(b.lin!, a.lin!) : sub(a.lin!, b.lin!))))
        if (d.t === undefined) { lin = same(2, e, 0, 0, 0, () => v(termColumn(e))); r = {w: none, pos: -1, fin: false}; break } // (the column: no reason, but open)
        r = both(both(a, b), d)
        lin = e.op === 'sub' ? same(0, e, a.lin, b.lin, d.t, () => (d.t ? sub(a.lin!, b.lin!) : k(0))) : (e.op === 'min') === d.t ? a.lin : b.lin
        break
      }
      case 'if': {
        const c = this.truth(e.c)
        if (c.t === undefined) { lin = same(2, e, 0, 0, 0, () => v(termColumn(e))); r = {w: none, pos: -1, fin: false}; break }
        const x = this.linear(c.t ? e.then : e.else)
        lin = x.lin; r = both(c, x)
        break
      }
      case 'get': { const key = this.linear(e.key); lin = key.lin && same(0, e, key.lin, 0, 0, () => v(`${e.map}[${canon(key.lin!)}]`)); r = key; break }
    }
    // (an open value's reason is what its decided parts need: only the column's own value is open)
    const out: LV = {lin, w: r.w, fin: r.fin, pos: r.pos, stamp: r.pos < 0 ? 0 : this.trail.stamp(r.pos), node: this.node}
    this.ls.set(e, out)
    this.clean.add(e)
    return out
  }
  private atoms(c: Extract<C, {a: E}>): {when: Lin[], unless: Lin[][], r: R} | undefined {
    const a = this.linear(c.a), b = this.linear(c.b)
    if (!a.lin || !b.lin) return undefined
    const r = both(a, b), x = a.lin, y = b.lin
    const atoms = same(3, c, x, y, 0, () => {
      const ab = sub(x, y), ba = sub(y, x)
      if (c.op === '<=') return {when: [ab], unless: [[add(ba, k(1))]]}
      if (c.op === '<') return {when: [add(ab, k(1))], unless: [[ba]]}
      return {when: [ab, ba], unless: [[add(ab, k(1))], [add(ba, k(1))]]}
    })
    return {when: atoms.when, unless: atoms.unless, r}
  }
  truth(c: C): TV {
    this.read(c)
    const had = this.ts.get(c)
    if (had && this.ok(had, c)) return had
    return this.within(c, () => this.truth0(c))
  }
  private truth0(c: C): TV {
    let t: boolean | undefined, r: R
    switch (c.op) {
      case 'flag': throw new Error('flags are inlined before the kernel sees them')
      case 'all': t = undefined; r = R1; break
      case 'not': { const x = this.truth(c.x); t = x.t === undefined ? undefined : !x.t; r = x; break }
      case 'and': case 'or': {
        const dominant = c.op === 'or', xs = c.xs.map(y => this.truth(y))
        // One part with the dominant value decides it (the one that needs fewest decisions); else every part.
        let best: TV | undefined
        for (const x of xs) if (x.t === dominant && (!best || x.w.size < best.w.size || (x.w.size === best.w.size && x.fin && !best.fin))) best = x
        if (best) { t = dominant; r = best }
        else if (xs.every(x => x.t === !dominant)) { t = !dominant; r = xs.reduce<R>(both, R0) }
        else { t = undefined; r = R1 }
        break
      }
      case '<': case '<=': case '=': {
        const cmp = this.atoms(c)
        if (!cmp) { t = undefined; r = R1; break }
        const ds = cmp.when.map(lin => this.dec(lin))
        let best: R | undefined
        for (const d of ds) if (d.t === false && (!best || d.w.size < best.w.size)) best = d
        if (best) { t = false; const x = both(cmp.r, best); r = {w: x.w, pos: x.pos, fin: cmp.r.fin} }
        else if (ds.every(d => d.t === true)) { t = true; r = ds.reduce<R>(both, cmp.r) }
        else { t = undefined; r = unfin(cmp.r) }
        break
      }
    }
    // Final: decided, and every term its reason reads final too (a term column's atom on the trail reads differently
    // once the column's choice is decided, so a value through an open term is found again at each node).
    const out: TV = {t, w: r.w, fin: t !== undefined && r.fin, pos: r.pos, stamp: r.pos < 0 ? 0 : this.trail.stamp(r.pos), node: this.node}
    this.ts.set(c, out)
    this.clean.add(c)
    return out
  }
  // kernel.ts's facts, each row with its reason; final when nothing it read is open.
  private factsOf(c: C, positive: boolean, out: Row[]): R {
    switch (c.op) {
      case 'flag': throw new Error('flags are inlined before the kernel sees them')
      case 'all': return R0
      case 'not': return this.factsOf(c.x, !positive, out)
      case 'and': case 'or': {
        if ((c.op === 'and') === positive) return c.xs.reduce<R>((acc, y) => both(acc, this.factsOf(y, positive, out)), R0)
        let closed = R0
        const open: C[] = []
        for (const y of c.xs) { const t = this.truth(y); if (t.t === !positive) closed = both(closed, t); else open.push(y) }
        if (open.length === 0) { out.push({lin: one, w: closed.w, label: ''}); return closed }
        if (open.length > 1) return unfin(closed)
        const inner: Row[] = [], r = this.factsOf(open[0]!, positive, inner)
        for (const row of inner) out.push({lin: row.lin, w: join(row.w, closed.w), label: ''})
        // (the last open part's own value is a read: open while it is)
        const last = this.truth(open[0]!)
        // (and the facts are kept only while the part's own value is: its reason is theirs, though not their rows')
        const x = both(both(closed, r), last)
        return {w: x.w, pos: x.pos, fin: r.fin && last.t !== undefined && last.fin}
      }
      case '<': case '<=': case '=': {
        const cmp = this.atoms(c)
        if (!cmp) return R1
        if (positive) { for (const lin of cmp.when) out.push({lin, w: cmp.r.w, label: ''}); return cmp.r }
        let closed = cmp.r
        const open: Lin[][] = []
        for (const atoms of cmp.unless) {
          let shut: R | undefined
          for (const lin of atoms) { const d = this.dec(lin); if (d.t === false) { shut = d; break } }
          if (shut) closed = both(closed, shut); else open.push(atoms)
        }
        if (open.length === 0) { out.push({lin: one, w: closed.w, label: ''}); return closed }
        if (open.length > 1) return unfin(closed)
        for (const lin of open[0]!) out.push({lin, w: closed.w, label: ''})
        return unfin(closed)
      }
    }
  }
  // (a hypothesis' facts are its parts': each conjunct's, kept as a value is, so a change finds again only the parts
  // that read it)
  facts(i: number): FV {
    const key = (this.factKeys[i] ??= new Seg(0, i))
    this.read(key)
    const had = this.fs[i]
    if (had && this.ok(had, key)) return had
    return this.within(key, () => {
      const parts = this.parts(i)
      let rows: Row[] = [], pos = -1, fin = true
      if (parts.length === 1) { const f = this.part(parts[0]!); rows = f.rows; pos = f.pos; fin = f.fin }
      else for (const p of parts) { const f = this.part(p); for (const r of f.rows) rows.push(r); if (f.pos > pos) pos = f.pos; fin &&= f.fin }
      const out: FV = {rows, fin, pos, stamp: pos < 0 ? 0 : this.trail.stamp(pos), node: this.node}
      this.fs[i] = out
      this.clean.add(key)
      return out
    })
  }
  // Whether a hypothesis' facts are final (each part's).
  private factsFin(i: number): boolean { for (const p of this.parts(i)) if (!this.part(p).fin) return false; return true }
  // A hypothesis' conjuncts (a conjunction's parts, a negated disjunction's, flattened), each with its sign.
  private partsOf: {c: C, positive: boolean, key: Seg}[][] = []
  private ps = new Map<Seg, FV>()
  private parts(i: number): {c: C, positive: boolean, key: Seg}[] {
    let out = this.partsOf[i]
    if (out) return out
    const mine: {c: C, positive: boolean, key: Seg}[] = []
    const flat = (c: C, positive: boolean): void => {
      if (c.op === 'not') return flat(c.x, !positive)
      if ((c.op === 'and' && positive) || (c.op === 'or' && !positive)) { for (const y of c.xs) flat(y, positive); return }
      mine.push({c, positive, key: new Seg(3, i, mine.length)})
    }
    flat(this.goal.hyps[i]!, true)
    return (this.partsOf[i] = out = mine)
  }
  private part(p: {c: C, positive: boolean, key: Seg}): FV {
    this.read(p.key)
    const had = this.ps.get(p.key)
    if (had && this.ok(had, p.key)) return had
    return this.within(p.key, () => {
      const rows: Row[] = [], r = this.factsOf(p.c, p.positive, rows)
      const out: FV = {rows, fin: r.fin, pos: r.pos, stamp: r.pos < 0 ? 0 : this.trail.stamp(r.pos), node: this.node}
      this.ps.set(p.key, out)
      this.clean.add(p.key)
      return out
    })
  }
  // kernel.ts's termRows, each row with its reason (the forms made again only when a part's form is a new object).
  termRows(name: string): Row[] {
    const e = columnTerm(name)!, col = same(4, e, 0, 0, 0, () => v(name)), out: Row[] = []
    if (e.op === 'min' || e.op === 'max' || e.op === 'sub') {
      const a = this.linear(e.a), b = this.linear(e.b), w = join(a.w, b.w)
      if (a.lin && b.lin) {
        const x = a.lin, y = b.lin, lins = same(5, e, x, y, 0, () => e.op === 'min' ? [sub(col, x), sub(col, y)] : e.op === 'max' ? [sub(x, col), sub(y, col)] : [sub(sub(x, y), col), sub(col, x)])
        for (const lin of lins) out.push({lin, w, label: ''})
      }
    }
    if (e.op === 'if') {
      const a = this.linear(e.then), b = this.linear(e.else)
      if (a.lin && b.lin && constantLin(a.lin) && constantLin(b.lin)) { const x = a.lin, y = b.lin; out.push({lin: same(5, e, x, y, 0, () => sub(col, add(x, y))), w: join(a.w, b.w), label: ''}) }
    }
    if (this.decided(e)) {
      const r = this.linear(e)
      if (r.lin) { const x = r.lin, [p, q] = same(6, e, x, 0, 0, () => [sub(col, x), sub(x, col)]); out.push({lin: p!, w: r.w, label: ''}, {lin: q!, w: r.w, label: ''}) }
    }
    return out
  }
  private decided(e: E): boolean {
    if (e.op === 'if') return this.truth(e.c).t !== undefined
    if (e.op !== 'sub' && e.op !== 'min' && e.op !== 'max') return true
    const a = this.linear(e.a).lin, b = this.linear(e.b).lin
    return !!a && !!b && this.dec(same(1, e, a, b, 0, () => (e.op === 'sub' ? sub(b, a) : sub(a, b)))).t !== undefined
  }
  // kernel.ts's leaf rows at the trail (leafRows), each with its reason: the trail's atoms, every hypothesis' facts,
  // equal cells at keys the trail proves equal, each term column's rows (and those of the columns they bring), and a
  // natural's row for every name.
  rows(): Row[] {
    // One row per linear form, with the shortest reason any of its copies has (forms told apart by their ids, stamped).
    const out: Row[] = [], g = ++this.gen
    for (const r of this.leafRows()) {
      const id = this.form(r.lin).id
      if (this.formSeen[id] !== g) { this.formSeen[id] = g; this.formAt[id] = out.length; out.push(r) } else { const j = this.formAt[id]!; if (r.w.size < out[j]!.w.size) out[j] = r }
    }
    return out
  }
  // Each form's id (by its canonical text) and its names' ids, kept per reader; the stamps that tell a node's forms and
  // names apart without hashing their texts at every node.
  private forms = new WeakMap<Lin, {id: number, names: number[]}>()
  private formIds = new Map<string, number>()
  private nameIds = new Map<string, number>()
  private nameText: string[] = []
  private nameKind: number[] = [] // 1: a term column, 2: a cell, 0: else
  private formSeen: number[] = []
  private formAt: number[] = []
  private nameSeen: number[] = []
  private termSeen: number[] = []
  private gen = 0
  form(lin: Lin): {id: number, names: number[]} {
    let f = this.forms.get(lin)
    if (f) return f
    const text = canon(lin)
    let id = this.formIds.get(text)
    if (id === undefined) { id = this.formIds.size; this.formIds.set(text, id); this.formSeen.push(0); this.formAt.push(0) }
    const names = namesOf(lin).map(n => {
      let j = this.nameIds.get(n)
      if (j === undefined) { j = this.nameText.length; this.nameIds.set(n, j); this.nameText.push(n); this.nameKind.push(n.startsWith('⟦') ? 1 : isCell(n) ? 2 : 0); this.nameSeen.push(0); this.termSeen.push(0) }
      return j
    })
    this.forms.set(lin, (f = {id, names}))
    return f
  }
  // Whether a form reads a term column; a cell; a name's text by its id.
  readsColumn(lin: Lin): boolean { for (const j of this.form(lin).names) if (this.nameKind[j] === 1) return true; return false }
  readsCell(lin: Lin): boolean { for (const j of this.form(lin).names) if (this.nameKind[j] === 2) return true; return false }
  nameOf(j: number): string { return this.nameText[j]! }
  // The trail's atom rows, by position, kept while the position's stamp is.
  private trailRows: Row[] = []
  private trailStamps: number[] = []
  private pairs = new Map<string, {d: Lin, neg: Lin, pq: Lin, qp: Lin}>()
  // The rows in kernel.ts's order, copies kept (a leaf's derivation indexes these).
  leafRows(): Row[] {
    const rows: Row[] = []
    for (let i = 0; i < this.trail.size(); i++) {
      const s = this.trail.stamp(i)
      let r = this.trailStamps[i] === s ? this.trailRows[i] : undefined
      if (!r) {
        const a = this.trail.lin(i), key = `${a.name}=${a.holds}`
        r = this.atomRows.get(key)
        if (!r) this.atomRows.set(key, (r = {lin: atomOf(a.lin, a.holds).lin, w: new Set([a.name]), label: ''}))
        this.trailRows[i] = r; this.trailStamps[i] = s
      }
      rows.push(r)
    }
    for (let i = 0; i < this.goal.hyps.length; i++) for (const r of this.facts(i).rows) rows.push(r)
    // (each name once, in the order first read, as a set of texts would keep them)
    const g = ++this.gen, names: number[] = [], seen = this.nameSeen, kind = this.nameKind
    for (const r of rows) for (const j of this.form(r.lin).names) if (seen[j] !== g) { seen[j] = g; names.push(j) }
    const cells = names.filter(j => kind[j] === 2).map(j => cellOf(this.nameText[j]!))
    for (const [i, p] of cells.entries()) for (const q of cells.slice(i + 1)) {
      if (p.map !== q.map) continue
      const f = this.pair(p, q), x = this.dec(f.d), y = this.dec(f.neg)
      if (x.t === true && y.t === true) { const w = join(x.w, y.w); rows.push({lin: f.pq, w, label: ''}, {lin: f.qp, w, label: ''}) }
    }
    const done = this.termSeen, todo = names.filter(j => kind[j] === 1)
    while (todo.length) {
      const j = todo.pop()!
      if (done[j] === g) continue
      done[j] = g
      for (const r of this.termRows(this.nameText[j]!)) {
        rows.push(r)
        for (const n of this.form(r.lin).names) { if (seen[n] !== g) { seen[n] = g; names.push(n) } if (kind[n] === 1 && done[n] !== g) todo.push(n) }
      }
    }
    for (const j of names) { const name = this.nameText[j]!; let r = this.natRows.get(name); if (!r) this.natRows.set(name, (r = {lin: {[name]: -1}, w: none, label: ''})); rows.push(r) }
    return rows
  }
  // --- The live rows: kept from one node to the next (kernel/cdcl.ts's search) ---------------------------------------
  // The same rows as rows() gives at the trail, found from what changed since the last sync: the trail's atom rows by
  // position, the facts of each hypothesis whose key a change touched (and of those new since), and the rows these bring
  // as the names they read come and go: a natural's row a name, each term column's rows (a part kept like the facts, by
  // a key of its own), each pair of cells' (the cells the trail's atoms and the facts read). `live` has one row a form,
  // the first of its copies with the shortest reason, in no set order; `entered` and `left` the forms (by id) that came
  // and went in the last sync.
  live: Row[] = []
  entered: number[] = []
  left: number[] = []
  private syncing = false
  private dirty = new Set<Seg>()
  private slot: number[] = []
  private copies: Row[][] = []
  private c12: number[] = [] // by name id: the copies from the trail and the facts that read it
  private cT: number[] = [] // and from term rows (a column's own rows not counted for it)
  private inTrail: (Row | undefined)[] = []
  private inParts = new Map<Seg, FV>()
  private hypsIn = 0
  // (the hypothesis each live copy of a fact came from)
  private src = new WeakMap<Row, number>()
  // The hypotheses some rows came from, as the live rows have them.
  hypsOf(rows: Row[]): number[] { const out = new Set<number>(); for (const r of rows) { const i = this.src.get(r); if (i !== undefined) out.add(i) } return [...out] }
  private inSeg = new Map<Seg, Row[]>()
  private cached = new Map<Seg, Row[]>()
  private termKeys: Seg[] = []
  private pairKeys = new Map<number, Map<number, Seg>>()
  private liveCells = new Map<string, Set<number>>()
  private inNat: (Row | undefined)[] = []
  private syncN = 0
  private markN: number[] = []
  private wasLive: boolean[] = []
  private changed: number[] = []
  // A live form's place in `live`, by its id; whether any cell is read.
  slotOf(id: number): number { return this.slot[id]! }
  hasCells(): boolean { return this.cellsOn > 0 }
  private cellsOn = 0
  // The live cells' names by map (every cell a live row reads), and a count of their changes.
  readonly cells = new Map<string, Set<string>>()
  cellsChanged = 0
  sync(): void {
    this.syncing = true
    this.syncN++
    this.changed = []
    const n = this.trail.size()
    for (let i = 0; i < Math.max(n, this.inTrail.length); i++) {
      const r = i < n ? this.trailRow(i) : undefined, had = this.inTrail[i]
      if (r === had) continue
      if (r) this.addCopy(r, 1)
      if (had) this.removeCopy(had, 1)
      this.inTrail[i] = r
    }
    this.inTrail.length = n
    for (; this.hypsIn < this.goal.hyps.length; this.hypsIn++) for (const p of this.parts(this.hypsIn)) this.dirty.add(p.key)
    for (const key of [...this.dirty]) {
      if (key.kind === 0) continue
      if (key.kind === 3) {
        const fv = this.part(this.partsOf[key.i]![key.j]!), had = this.inParts.get(key)
        if (fv === had) continue
        for (const r of fv.rows) { this.src.set(r, key.i); this.addCopy(r, 1) }
        if (had) for (const r of had.rows) this.removeCopy(r, 1)
        this.inParts.set(key, fv)
      } else if (this.inSeg.has(key)) {
        const had = this.inSeg.get(key)!, now = this.segRows(key)
        if (now === had) continue
        this.inSeg.set(key, now)
        for (const r of now) this.addCopy(r, key.kind === 1 ? 2 : 0, key.kind === 1 ? key.i : -1)
        for (const r of had) this.removeCopy(r, key.kind === 1 ? 2 : 0, key.kind === 1 ? key.i : -1)
      }
    }
    this.dirty.clear()
    this.entered = []; this.left = []
    for (const id of this.changed) {
      const now = this.copies[id]!.length > 0
      if (now && !this.wasLive[id]) this.entered.push(id)
      else if (!now && this.wasLive[id]) this.left.push(id)
    }
  }
  private trailRow(i: number): Row {
    const s = this.trail.stamp(i)
    let r = this.trailStamps[i] === s ? this.trailRows[i] : undefined
    if (!r) {
      const a = this.trail.lin(i), key = `${a.name}=${a.holds}`
      r = this.atomRows.get(key)
      if (!r) this.atomRows.set(key, (r = {lin: atomOf(a.lin, a.holds).lin, w: new Set([a.name]), label: ''}))
      this.trailRows[i] = r; this.trailStamps[i] = s
    }
    return r
  }
  // A part's rows: kept while its key is clean, else found again (its reads noted, as a value's).
  private segRows(key: Seg): Row[] {
    const had = this.cached.get(key)
    if (had && this.clean.has(key)) return had
    const rows = this.within(key, (): Row[] => {
      if (key.kind === 1) return this.termRows(this.nameText[key.i]!)
      const p = cellOf(this.nameText[key.i]!), q = cellOf(this.nameText[key.j]!), f = this.pair(p, q)
      const x = this.dec(f.d), y = this.dec(f.neg)
      if (x.t !== true || y.t !== true) return []
      const w = join(x.w, y.w)
      return [{lin: f.pq, w, label: ''}, {lin: f.qp, w, label: ''}]
    })
    this.cached.set(key, rows)
    this.clean.add(key)
    return rows
  }
  // (each pair's forms made once: the same objects at every node, so what is kept per form is found again)
  private pair(p: {name: string, key: Lin}, q: {name: string, key: Lin}) {
    const key = `${p.name}\u0000${q.name}`
    let f = this.pairs.get(key)
    if (!f) { if (this.pairs.size > 200_000) this.pairs.clear(); const d = sub(p.key, q.key); this.pairs.set(key, (f = {d, neg: scale(d, -1), pq: sub(v(p.name), v(q.name)), qp: sub(v(q.name), v(p.name))})) }
    return f
  }
  private mark(id: number, live: boolean) {
    if (this.markN[id] === this.syncN) return
    this.markN[id] = this.syncN; this.wasLive[id] = live; this.changed.push(id)
  }
  // A copy of a row in (kind 1: from the trail or the facts, 2: a column's term rows, its own name not counted; 0: a
  // natural's or a pair of cells', whose names it doesn't count).
  private addCopy(r: Row, kind: number, self = -1) {
    const f = this.form(r.lin), id = f.id, cs = (this.copies[id] ??= [])
    costs.copies++
    if (!cs.length) { this.mark(id, false); this.slot[id] = this.live.length; this.live.push(r) } else { const at = this.slot[id]!; if (r.w.size < this.live[at]!.w.size) this.live[at] = r }
    cs.push(r)
    if (kind) for (const j of f.names) if (j !== self) this.countUp(j, kind)
  }
  private removeCopy(r: Row, kind: number, self = -1) {
    const f = this.form(r.lin), id = f.id, cs = this.copies[id]!
    costs.copies++
    cs.splice(cs.indexOf(r), 1)
    const at = this.slot[id]!
    if (!cs.length) {
      this.mark(id, true)
      const last = this.live.pop()!
      if (at < this.live.length) { this.live[at] = last; this.slot[this.form(last.lin).id] = at }
      this.slot[id] = -1
    } else if (this.live[at] === r) { let best = cs[0]!; for (const c of cs) if (c.w.size < best.w.size) best = c; this.live[at] = best }
    if (kind) for (const j of f.names) if (j !== self) this.countDown(j, kind)
  }
  private countUp(j: number, kind: number) {
    const before = (this.c12[j] ?? 0) + (this.cT[j] ?? 0)
    if (kind === 1) this.c12[j] = (this.c12[j] ?? 0) + 1; else this.cT[j] = (this.cT[j] ?? 0) + 1
    if (before === 0) this.nameOn(j)
    if (kind === 1 && this.c12[j] === 1 && this.nameKind[j] === 2) this.cellOn(j)
  }
  private countDown(j: number, kind: number) {
    if (kind === 1) this.c12[j]!--; else this.cT[j]!--
    if (kind === 1 && this.c12[j] === 0 && this.nameKind[j] === 2) this.cellOff(j)
    if ((this.c12[j] ?? 0) + (this.cT[j] ?? 0) === 0) this.nameOff(j)
  }
  private nameOn(j: number) {
    const name = this.nameText[j]!
    let r = this.natRows.get(name)
    if (!r) this.natRows.set(name, (r = {lin: {[name]: -1}, w: none, label: ''}))
    this.inNat[j] = r
    this.addCopy(r, 0)
    if (this.nameKind[j] === 2) {
      this.cellsOn++; this.cellsChanged++
      const c = cellOf(name)
      let same = this.cells.get(c.map)
      if (!same) this.cells.set(c.map, (same = new Set()))
      same.add(name)
    }
    if (this.nameKind[j] === 1) this.segOn((this.termKeys[j] ??= new Seg(1, j)))
  }
  private nameOff(j: number) {
    this.removeCopy(this.inNat[j]!, 0)
    this.inNat[j] = undefined
    if (this.nameKind[j] === 2) { this.cellsOn--; this.cellsChanged++; this.cells.get(cellOf(this.nameText[j]!).map)!.delete(this.nameText[j]!) }
    if (this.nameKind[j] === 1) this.segOff(this.termKeys[j]!)
  }
  private segOn(key: Seg) {
    const rows = this.segRows(key)
    this.inSeg.set(key, rows)
    for (const r of rows) this.addCopy(r, key.kind === 1 ? 2 : 0, key.kind === 1 ? key.i : -1)
  }
  private segOff(key: Seg) {
    const rows = this.inSeg.get(key)!
    this.inSeg.delete(key)
    for (const r of rows) this.removeCopy(r, key.kind === 1 ? 2 : 0, key.kind === 1 ? key.i : -1)
  }
  private pairKey(a: number, b: number): Seg {
    const [p, q] = a < b ? [a, b] : [b, a]
    let m = this.pairKeys.get(p)
    if (!m) this.pairKeys.set(p, (m = new Map()))
    let key = m.get(q)
    if (!key) m.set(q, (key = new Seg(2, p, q)))
    return key
  }
  private cellOn(j: number) {
    const c = cellOf(this.nameText[j]!)
    let same = this.liveCells.get(c.map)
    if (!same) this.liveCells.set(c.map, (same = new Set()))
    for (const q of same) this.segOn(this.pairKey(j, q))
    same.add(j)
  }
  private cellOff(j: number) {
    const same = this.liveCells.get(cellOf(this.nameText[j]!).map)!
    same.delete(j)
    for (const q of same) this.segOff(this.pairKey(j, q))
  }
  // prove.ts's open atoms of a hypothesis (openH), in its order; none for a hypothesis whose facts are final.
  open(i: number, out: Lin[]): void { for (const lin of this.openList(i)) out.push(lin) }
  // (the list itself, the same array while it stands)
  openList(i: number): Lin[] {
    const key = (this.openKeys[i] ??= {}), had = this.os[i]
    if (had && ((keepClean && this.clean.has(key)) || had.node === this.node)) return had.lins
    const lins = this.within(key, () => {
      const mine: Lin[] = []
      if (!this.factsFin(i)) this.openH(this.goal.hyps[i]!, mine, true)
      return mine
    })
    this.os[i] = {lins, node: this.node}
    this.clean.add(key)
    return lins
  }
  private openE(e: E, out: Lin[]): void {
    switch (e.op) {
      case 'var': case 'const': return
      case 'mul': return this.openE(e.a, out)
      case 'prod': return (this.openE(e.a, out), this.openE(e.b, out))
      case 'get': return this.openE(e.key, out)
      case 'if': { const t = this.truth(e.c); if (t.t === undefined) this.openC(e.c, out); else this.openE(t.t ? e.then : e.else, out); return }
      case 'add': case 'sub': case 'min': case 'max': {
        if (this.linear(e).fin) return
        this.openE(e.a, out), this.openE(e.b, out)
        const a = this.linear(e.a).lin, b = this.linear(e.b).lin
        if (a && b && !this.decided(e)) out.push(same(1, e, a, b, 0, () => (e.op === 'sub' ? sub(b, a) : sub(a, b))))
        return
      }
    }
  }
  private openC(c: C, out: Lin[]): void {
    if (this.truth(c).t !== undefined) return
    if (c.op === 'flag' || c.op === 'all') return
    if (c.op === 'not') return this.openC(c.x, out)
    if (c.op === 'and' || c.op === 'or') return c.xs.forEach(y => this.openC(y, out))
    const a = this.linear(c.a).lin, b = this.linear(c.b).lin
    const own: Lin[] = a && b ? same(7, c, a, b, 0, () => { const d = sub(a, b); return c.op === '<=' ? [d] : c.op === '<' ? [add(d, k(1))] : [d, scale(d, -1)] }) : []
    this.openE(c.a, out), this.openE(c.b, out)
    for (const x of own) out.push(x)
  }
  private openH(c: C, out: Lin[], positive: boolean): void {
    if (c.op === 'not') return this.openH(c.x, out, !positive)
    if ((c.op === 'and' && positive) || (c.op === 'or' && !positive)) return c.xs.forEach(y => this.openH(y, out, positive))
    if (c.op === 'and' || c.op === 'or') {
      if (this.truth(c).t !== undefined) return
      const open = c.xs.filter(y => this.truth(y).t !== !positive)
      if (open.length === 1) this.openH(open[0]!, out, positive)
      else this.openC(c, out)
      return
    }
    if (c.op === 'flag' || c.op === 'all') return
    const before = out.length
    this.openE(c.a, out), this.openE(c.b, out)
    if (out.length === before && !positive && c.op === '=' && this.truth(c).t === undefined) this.openC(c, out)
  }
}

// A form's variables, and a cell's map and key, remembered (read at every node).
const nameMemo = new WeakMap<Lin, string[]>()
export const namesOf = (lin: Lin): string[] => {
  let out = nameMemo.get(lin)
  if (!out) nameMemo.set(lin, (out = Object.keys(lin).filter(key => key !== '1')))
  return out
}
const cellMemo = new Map<string, {name: string, map: string, key: Lin}>()
const cellOf = (name: string) => {
  let out = cellMemo.get(name)
  if (!out) { if (cellMemo.size > 100_000) cellMemo.clear(); cellMemo.set(name, (out = {name, map: name.slice(0, name.indexOf('[')), key: keyLin(name)})) }
  return out
}
export const keyLin = (cell: string): Lin => {
  const inner = cell.slice(cell.indexOf('[') + 1, -1), out: Lin = {}
  let depth = 0, start = 0
  for (let i = 0; i <= inner.length; i++) {
    const ch = inner[i]
    if (ch === '[') depth++
    else if (ch === ']') depth--
    else if ((ch === ',' && depth === 0) || i === inner.length) {
      if (i > start) { const part = inner.slice(start, i), at = part.lastIndexOf(':'); out[part.slice(0, at)] = Number(part.slice(at + 1)) }
      start = i + 1
    }
  }
  return out
}
