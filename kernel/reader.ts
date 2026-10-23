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
import {type Lin, add, k, scale, sub, v} from '../core/solver.ts'
import {type Goal, atomOf, canon, canonFlip, columnTerm, factorsOf, isCell, termColumn} from './kernel.ts'

export type W = ReadonlySet<string>
export const none: W = new Set<string>()
export const join = (a: W, b: W): W => {
  if (!a.size || a === b) return b
  if (!b.size) return a
  const out = new Set(a)
  for (const x of b) out.add(x)
  return out
}
// A trail: each decided atom (by its variable's name, the canonical text of its stored form) with its value and its
// position; each position's stamp.
export type Trail = {get(name: string): {val?: boolean, at: number} | undefined, stamp(at: number): number, size(): number, lin(at: number): {name: string, lin: Lin, holds: boolean}}
// A reason, its latest position on the trail, and whether the value read nothing open.
type R = {w: W, pos: number, fin: boolean}
const R0: R = {w: none, pos: -1, fin: true}
const both = (a: R, b: R): R => ({w: join(a.w, b.w), pos: Math.max(a.pos, b.pos), fin: a.fin && b.fin})
type Kept = {pos: number, stamp: number, node: number}
type TV = R & Kept & {t: boolean | undefined}
type LV = R & Kept & {lin: Lin | undefined}
type FV = Kept & {rows: Row[], fin: boolean}
export type Row = {lin: Lin, w: W, label: ''}

function times(a: Lin, b: Lin): Lin | undefined {
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
const keepClean = (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env?.GDP_READER_CLEAN !== '0'
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
  private up = new Map<object, Set<object>>()
  private byAtom = new Map<string, Set<object>>()
  private clean = new Set<object>()
  private frame: object | undefined
  private factKeys: object[] = []
  private openKeys: object[] = []
  private lastUp = new WeakMap<object, object>()
  private read(key: object) {
    if (!this.frame || this.lastUp.get(key) === this.frame) return
    this.lastUp.set(key, this.frame)
    let s = this.up.get(key)
    if (!s) this.up.set(key, (s = new Set()))
    s.add(this.frame)
  }
  private readAtom(name: string) {
    if (!this.frame) return
    let s = this.byAtom.get(name)
    if (!s) this.byAtom.set(name, (s = new Set()))
    s.add(this.frame)
  }
  private within<T>(key: object, f: () => T): T {
    const was = this.frame
    this.frame = key
    try { return f() } finally { this.frame = was }
  }
  // The trail changed at this atom (decided, or taken back): every value that read it, and every reader of those, all
  // the way up (a value kept as final reads below it values that are not clean).
  touch(name: string) {
    const todo = [...(this.byAtom.get(name) ?? [])], seen = new Set<object>()
    while (todo.length) {
      const key = todo.pop()!
      if (seen.has(key)) continue
      seen.add(key)
      this.clean.delete(key)
      for (const p of this.up.get(key) ?? []) todo.push(p)
    }
  }
  private ok(x: Kept & {fin: boolean}, key: object): boolean {
    if ((keepClean && this.clean.has(key)) || x.node === this.node) return true
    if (x.fin && (x.pos < 0 || (x.pos < this.trail.size() && this.trail.stamp(x.pos) === x.stamp))) { this.clean.add(key); return true }
    return false
  }
  private kept(r: R): Kept { return {pos: r.pos, stamp: r.pos < 0 ? 0 : this.trail.stamp(r.pos), node: this.node} }
  private units = new Map<string, W>()
  private unit(name: string): W { let w = this.units.get(name); if (!w) this.units.set(name, (w = new Set([name]))); return w }
  // Whether lin <= 0 is decided, and by what.
  dec(lin: Lin): R & {t: boolean | undefined} {
    let constant = true
    for (const key in lin) if (key !== '1') { constant = false; break }
    if (constant) return {...R0, t: (lin['1'] ?? 0) <= 0}
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
    const out: LV = {lin, w: r.w, fin: r.fin, ...this.kept(r)}
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
    return {...atoms, r}
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
      case 'all': t = undefined; r = {...R0, fin: false}; break
      case 'not': { const x = this.truth(c.x); t = x.t === undefined ? undefined : !x.t; r = x; break }
      case 'and': case 'or': {
        const dominant = c.op === 'or', xs = c.xs.map(y => this.truth(y))
        // One part with the dominant value decides it (the one that needs fewest decisions); else every part.
        let best: TV | undefined
        for (const x of xs) if (x.t === dominant && (!best || x.w.size < best.w.size || (x.w.size === best.w.size && x.fin && !best.fin))) best = x
        if (best) { t = dominant; r = best }
        else if (xs.every(x => x.t === !dominant)) { t = !dominant; r = xs.reduce<R>(both, R0) }
        else { t = undefined; r = {...R0, fin: false} }
        break
      }
      case '<': case '<=': case '=': {
        const cmp = this.atoms(c)
        if (!cmp) { t = undefined; r = {...R0, fin: false}; break }
        const ds = cmp.when.map(lin => this.dec(lin))
        let best: R | undefined
        for (const d of ds) if (d.t === false && (!best || d.w.size < best.w.size)) best = d
        if (best) { t = false; r = {...both(cmp.r, best), fin: cmp.r.fin} }
        else if (ds.every(d => d.t === true)) { t = true; r = ds.reduce<R>(both, cmp.r) }
        else { t = undefined; r = {...cmp.r, fin: false} }
        break
      }
    }
    // Final: decided, and every term its reason reads final too (a term column's atom on the trail reads differently
    // once the column's choice is decided, so a value through an open term is found again at each node).
    const out: TV = {t, w: r.w, fin: t !== undefined && r.fin, ...this.kept(r)}
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
        if (open.length > 1) return {...closed, fin: false}
        const inner: Row[] = [], r = this.factsOf(open[0]!, positive, inner)
        for (const row of inner) out.push({lin: row.lin, w: join(row.w, closed.w), label: ''})
        // (the last open part's own value is a read: open while it is)
        const last = this.truth(open[0]!)
        // (and the facts are kept only while the part's own value is: its reason is theirs, though not their rows')
        return {...both(both(closed, r), last), fin: r.fin && last.t !== undefined && last.fin}
      }
      case '<': case '<=': case '=': {
        const cmp = this.atoms(c)
        if (!cmp) return {...R0, fin: false}
        if (positive) { for (const lin of cmp.when) out.push({lin, w: cmp.r.w, label: ''}); return cmp.r }
        let closed = cmp.r
        const open: Lin[][] = []
        for (const atoms of cmp.unless) {
          let shut: R | undefined
          for (const lin of atoms) { const d = this.dec(lin); if (d.t === false) { shut = d; break } }
          if (shut) closed = both(closed, shut); else open.push(atoms)
        }
        if (open.length === 0) { out.push({lin: one, w: closed.w, label: ''}); return closed }
        if (open.length > 1) return {...closed, fin: false}
        for (const lin of open[0]!) out.push({lin, w: closed.w, label: ''})
        return {...closed, fin: false}
      }
    }
  }
  facts(i: number): FV {
    const key = (this.factKeys[i] ??= {})
    this.read(key)
    const had = this.fs[i]
    if (had && this.ok(had, key)) return had
    return this.within(key, () => {
      const rows: Row[] = [], r = this.factsOf(this.goal.hyps[i]!, true, rows)
      const out: FV = {rows, fin: r.fin, ...this.kept(r)}
      this.fs[i] = out
      this.clean.add(key)
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
    return !!a && !!b && this.dec(e.op === 'sub' ? sub(b, a) : sub(a, b)).t !== undefined
  }
  // kernel.ts's leaf rows at the trail (leafRows), each with its reason: the trail's atoms, every hypothesis' facts,
  // equal cells at keys the trail proves equal, each term column's rows (and those of the columns they bring), and a
  // natural's row for every name.
  rows(): Row[] {
    // One row per linear form, with the shortest reason any of its copies has.
    const out: Row[] = [], at = new Map<string, number>()
    for (const r of this.leafRows()) {
      const id = canon(r.lin), j = at.get(id)
      if (j === undefined) { at.set(id, out.length); out.push(r) } else if (r.w.size < out[j]!.w.size) out[j] = r
    }
    return out
  }
  // The rows in kernel.ts's order, copies kept (a leaf's derivation indexes these).
  leafRows(): Row[] {
    const rows: Row[] = []
    for (let i = 0; i < this.trail.size(); i++) {
      const a = this.trail.lin(i), key = `${a.name}=${a.holds}`
      let r = this.atomRows.get(key)
      if (!r) this.atomRows.set(key, (r = {lin: atomOf(a.lin, a.holds).lin, w: new Set([a.name]), label: ''}))
      rows.push(r)
    }
    for (let i = 0; i < this.goal.hyps.length; i++) for (const r of this.facts(i).rows) rows.push(r)
    const names = new Set<string>()
    for (const r of rows) for (const key of namesOf(r.lin)) names.add(key)
    const cells = [...names].filter(isCell).map(cellOf)
    for (const [i, p] of cells.entries()) for (const q of cells.slice(i + 1)) {
      if (p.map !== q.map) continue
      const d = sub(p.key, q.key), x = this.dec(d), y = this.dec(scale(d, -1))
      if (x.t === true && y.t === true) { const w = join(x.w, y.w); rows.push({lin: sub(v(p.name), v(q.name)), w, label: ''}, {lin: sub(v(q.name), v(p.name)), w, label: ''}) }
    }
    const seen = new Set<string>(), todo = [...names].filter(n => n.startsWith('⟦'))
    while (todo.length) {
      const name = todo.pop()!
      if (seen.has(name)) continue
      seen.add(name)
      for (const r of this.termRows(name)) {
        rows.push(r)
        for (const key of namesOf(r.lin)) { names.add(key); if (key.startsWith('⟦') && !seen.has(key)) todo.push(key) }
      }
    }
    for (const name of names) { let r = this.natRows.get(name); if (!r) this.natRows.set(name, (r = {lin: {[name]: -1}, w: none, label: ''})); rows.push(r) }
    return rows
  }
  // prove.ts's open atoms of a hypothesis (openH), in its order; none for a hypothesis whose facts are final.
  open(i: number, out: Lin[]): void {
    const key = (this.openKeys[i] ??= {}), had = this.os[i]
    if (had && ((keepClean && this.clean.has(key)) || had.node === this.node)) { for (const lin of had.lins) out.push(lin); return }
    const lins = this.within(key, () => {
      const mine: Lin[] = []
      if (!this.facts(i).fin) this.openH(this.goal.hyps[i]!, mine, true)
      return mine
    })
    this.os[i] = {lins, node: this.node}
    this.clean.add(key)
    for (const lin of lins) out.push(lin)
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
