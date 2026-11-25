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
import {completeWorkProfile} from '../core/work-profile.ts'
import {checkWorkEndpoint} from './prove.ts'
import {startWork} from '../core/work-admission.ts'
import {shareTerms} from './share.ts'
import {type Lin, costs, env} from '../core/solver.ts'
import {fundedAdd as add,fundedConstant as k,fundedScale as scale,fundedSub as sub,fundedVariable as v,admittedLinearProduct,everyLinearCell} from '../core/linear-admission.ts'
import {workConcat,workStrings,workJoin} from '../core/work-collections.ts'
import {type Goal, atomOf, canon, canonFlip, cellParts, plainMap, columnTerm, factorsOf, isCell, termColumn, tupleAnd} from './kernel.ts'

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
// `quiet`: a position whose atom brings no row (kernel/cdcl.ts's gates and selectors, read only as decisions).
export type Trail = {get(name: string): {val?: boolean, at: number} | undefined, stamp(at: number): number, size(): number, lin(at: number): {name: string, lin: Lin, holds: boolean}, quiet?(at: number): boolean}
// A reason, its latest position on the trail, and whether the value read nothing open.
type R = {w: W, pos: number, fin: boolean}
const R0: R = {w: none, pos: -1, fin: true}, R1: R = {w: none, pos: -1, fin: false}
const unfin = (r: R): R => (r.fin ? {w: r.w, pos: r.pos, fin: false} : r)
const both = (a: R, b: R): R => ({w: join(a.w, b.w), pos: Math.max(a.pos, b.pos), fin: a.fin && b.fin})
type Kept = {pos: number, stamp: number, node: number}
type TV = R & Kept & {t: boolean | undefined, kid: number}
type LV = R & Kept & {lin: Lin | undefined, kid: number}
type FV = Kept & {rows: Row[], fin: boolean}
export type Row = {lin: Lin, w: W, label: ''}

// The kernel's product of two linear forms (kernel.ts's `times`): each monomial its factors sorted, joined by '*'.
export function times(a: Lin, b: Lin): Lin | undefined {
  if(completeWorkProfile.enabled)return admittedLinearProduct(a,b,(p,q)=>{
    if(p.includes('⟦')||q.includes('⟦'))return undefined
    const fs=workStrings(workConcat(p==='1'?[]:factorsOf(p),q==='1'?[]:factorsOf(q),'reader product:factors'),'reader product:sort')
    return fs.length?workJoin(fs,'*','reader product:join'):'1'
  },'reader product',false)
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
const constantLin = (l: Lin) => everyLinearCell(l,(key,c)=>key==='1'||c===0,'reader constant branch')

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
class Seg { cached?: Row[]; constructor(readonly kind: number, readonly i: number, readonly j = -1, readonly kid = 0) {} }
type EdgeSet = number[] | Map<number, number>
export class Reader {
  private static readonly emptyLins: Lin[] = []
  private node = 0
  private share = shareTerms()
  private natRows = new Map<string, Row>()
  private atomRows = new Map<string, Row>()
  private leafAtomRows = new WeakMap<Lin, Row[]>()
  private ls = new Map<E, LV>()
  private ts = new Map<C, TV>()
  private fs: (FV | undefined)[] = []
  private os: ({lins: Lin[], node: number} | undefined)[] = []
  constructor(readonly goal: Goal, readonly trail: Trail) {}
  // A new node: values with an open read are found again, unless nothing they read has changed.
  begin() { this.node++ }
  // The reads: each tracked value (term, condition, facts, seg, or open list) gets a dense integer key id (`kid`);
  // `up[kid]` and `byAtom.get(name)` hold its readers as flat `[readerKid, findingGen, ...]` pairs up to 16 entries
  // and promote to Map<number, number> past 16. Insertion order and live-edge counts match Map verbatim so touch()
  // visits the same keys and charges the exact same costs.edges; `clean`, `foundGen`, `lastUpGen`, `keySeg`, and
  // stamped `touchSeen` replace per-key Sets/Maps without changing which values stay clean.
  private up: (EdgeSet | undefined)[] = []
  private byAtom = new Map<string, EdgeSet>()
  // (each key's latest finding generation: a read is an edge to a generation, and one not matching foundGen[k] is stale)
  private foundGen: number[] = []
  private lastUpGen: number[] = []
  private clean: number[] = []
  private keySeg: (Seg | undefined)[] = []
  private touchSeen: number[] = []
  private touchTodo: number[] = []
  private touchStamp = 0
  private factKeys: Seg[] = []
  private openIds: number[] = []
  private findingKid = -1
  private findingGen = 0
  private findingCur = 0
  private allocKey(seg?: Seg): number {
    const kid = this.clean.length
    this.clean.push(0); this.foundGen.push(0); this.lastUpGen.push(0)
    this.up.push(undefined); this.keySeg.push(seg); this.touchSeen.push(0)
    return kid
  }
  private newSeg(kind: number, i: number, j = -1): Seg {
    const kid = this.allocKey()
    const seg = new Seg(kind, i, j, kid)
    this.keySeg[kid] = seg
    return seg
  }
  private addEdge(u: EdgeSet | undefined, fk: number, fg: number): EdgeSet {
    if (!u) return [fk, fg]
    if (Array.isArray(u)) {
      const len = u.length
      for (let i = 0; i < len; i += 2) if (u[i] === fk) { u[i + 1] = fg; return u }
      if (len < 32) { u.push(fk, fg); return u }
      const m = new Map<number, number>()
      for (let i = 0; i < len; i += 2) m.set(u[i]!, u[i + 1]!)
      m.set(fk, fg)
      return m
    }
    u.set(fk, fg)
    return u
  }
  private readId(kid: number) {
    const fg = this.findingCur
    if (!fg || this.lastUpGen[kid] === fg) return
    this.lastUpGen[kid] = fg
    const u = this.up[kid], next = this.addEdge(u, this.findingKid, fg)
    if (next !== u) this.up[kid] = next
  }
  private readAtom(name: string) {
    const fg = this.findingCur
    if (!fg) return
    const u = this.byAtom.get(name), next = this.addEdge(u, this.findingKid, fg)
    if (next !== u) this.byAtom.set(name, next)
  }
  private withinId<T>(kid: number, f: () => T): T {
    if (completeWorkProfile.enabled) startWork('values', 1, 'reader value')
    const wasKid = this.findingKid, wasCur = this.findingCur, now = ++this.findingGen
    if (!completeWorkProfile.enabled) costs.values++
    this.foundGen[kid] = now
    this.findingKid = kid; this.findingCur = now
    try { return f() } finally { this.findingKid = wasKid; this.findingCur = wasCur }
  }
  // The trail changed at this atom (decided, or taken back): every value that read it, and every reader of those, all
  // the way up (a value kept as final reads below it values that are not clean).
  touch(name: string) {
    const todo = this.touchTodo, seen = this.touchSeen, foundGen = this.foundGen, stamp = ++this.touchStamp
    todo.length = 0
    const walk = (edges: EdgeSet | undefined) => {
      if (!edges) return
      if (Array.isArray(edges)) {
        const len = edges.length
        if (!completeWorkProfile.enabled) costs.edges += len >> 1
        let w = 0
        for (let i = 0; i < len; i += 2) {
          if (completeWorkProfile.enabled) startWork('edges', 1, 'reader dependency')
          const k = edges[i]!, fg = edges[i + 1]!
          if (foundGen[k] === fg) { todo.push(k); edges[w++] = k; edges[w++] = fg }
        }
        edges.length = w
      } else {
        if (!completeWorkProfile.enabled) costs.edges += edges.size
        for (const [k, fg] of edges) {
          if (completeWorkProfile.enabled) startWork('edges', 1, 'reader dependency')
          if (foundGen[k] === fg) todo.push(k); else edges.delete(k)
        }
      }
    }
    walk(this.byAtom.get(name))
    while (todo.length) {
      const kid = todo.pop()!
      if (seen[kid] === stamp) continue
      seen[kid] = stamp
      this.clean[kid] = 0
      const seg = this.keySeg[kid]
      if (seg && this.syncing) this.dirty.add(seg)
      walk(this.up[kid])
    }
  }
  private okId(x: Kept & {fin: boolean}, kid: number): boolean {
    if ((keepClean && this.clean[kid] === 1) || x.node === this.node) return true
    if (x.fin && (x.pos < 0 || (x.pos < this.trail.size() && this.trail.stamp(x.pos) === x.stamp))) { this.clean[kid] = 1; return true }
    return false
  }
  private units = new Map<string, W>()
  private unit(name: string): W { let w = this.units.get(name); if (!w) this.units.set(name, (w = new Set([name]))); return w }
  // Whether lin <= 0 is decided, and by what.
  dec(lin: Lin): R & {t: boolean | undefined} {
    if (completeWorkProfile.enabled) checkWorkEndpoint('reader decision')
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
    if (completeWorkProfile.enabled) checkWorkEndpoint('reader expression')
    let had = this.ls.get(e)
    if (!had) { e = this.share(e); had = this.ls.get(e) }
    if (had) {
      this.readId(had.kid)
      if (this.okId(had, had.kid)) return had
      return this.withinId(had.kid, () => this.linear0(e, had.kid))
    }
    const kid = this.allocKey()
    this.readId(kid)
    return this.withinId(kid, () => this.linear0(e, kid))
  }
  private linear0(e: E, kid: number): LV {
    let lin: Lin | undefined, r: R = R0
    switch (e.op) {
      case 'var': lin = e.name === '1' || /[*[\],:⟦⟨⟩|]/.test(e.name) ? undefined : same(0, e, 0, 0, 0, () => v(e.name)); break
      case 'const': lin = same(0, e, 0, 0, 0, () => k(e.value)); break
      case 'mul': { const a = this.linear(e.a); lin = a.lin && Number.isSafeInteger(e.k) ? same(0, e, a.lin, 0, 0, () => scale(a.lin!, e.k)) : undefined; r = a; break }
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
      case 'get': {
        if (!plainMap(e.map)) { lin = undefined; break } // (kernel.ts's: no column a map's name could spell)
        // (a tuple key: its parts' forms, the cell M[⟨k1|k2|…⟩], kernel.ts's keyParts)
        if (e.key.op === 'tup' || e.key.op === 'proj') {
          const ps = this.tparts(e.key)
          // (kept by the cell's name: the read's parts change with the path, Src[p] where a column stood, and a form kept
          // by the read alone named the first path's cell at every later one, a cell kernel.ts doesn't read there)
          if (ps.lins) { r = ps.r; const name = `${e.map}[⟨${ps.lins.map(canon).join('|')}⟩]`; lin = same(0, e, name, 0, 0, () => v(name)); break }
          if (e.key.op === 'tup') { lin = undefined; r = ps.r; break }
        }
        const key = this.linear(e.key); lin = key.lin && same(0, e, key.lin, 0, 0, () => v(`${e.map}[${canon(key.lin!)}]`)); r = key; break
      }
      case 'tup': lin = undefined; break
      case 'proj': { const ps = this.tparts(e.a); r = ps.r; lin = !ps.lins ? undefined : e.k === 0 ? ps.lins[0] : ps.lins.length === 2 ? ps.lins[1] : undefined; break }
    }
    // Match kernel.ts's linearOf: an unsafe intermediate form is no form,
    // even if later arithmetic would cancel it back into the safe range.
    if (lin && !everyLinearCell(lin, (_key, coefficient) => Number.isSafeInteger(coefficient), 'reader linear safety')) lin = undefined
    // (an open value's reason is what its decided parts need: only the column's own value is open)
    const out: LV = {lin, w: r.w, fin: r.fin, pos: r.pos, stamp: r.pos < 0 ? 0 : this.trail.stamp(r.pos), node: this.node, kid}
    this.ls.set(e, out)
    this.clean[kid] = 1
    return out
  }
  // kernel.ts's keyParts: a tuple's parts' forms (proj 1 of one its rest, two or more), with their reason.
  private tparts(e: E): {lins?: Lin[], r: R} {
    if (e.op === 'proj') { if (e.k === 0) return {r: R0}; const ps = this.tparts(e.a); return ps.lins && ps.lins.length >= 3 ? {lins: ps.lins.slice(1), r: ps.r} : {r: ps.r} }
    if (e.op !== 'tup') return {r: R0}
    const a = this.linear(e.a)
    if (!a.lin) return {r: a}
    if (e.b.op !== 'tup') { const b = this.linear(e.b); return b.lin ? {lins: [a.lin, b.lin], r: both(a, b)} : {r: both(a, b)} }
    const rest = this.tparts(e.b)
    return rest.lins ? {lins: [a.lin, ...rest.lins], r: both(a, rest.r)} : {r: both(a, rest.r)}
  }
  private atoms(c: Extract<C, {a: E}>): {when: Lin[], unless: Lin[][], r: R} | undefined {
    if (c.a.op === 'tup' || c.b.op === 'tup') return undefined
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
    if (completeWorkProfile.enabled) checkWorkEndpoint('reader condition')
    let had = this.ts.get(c)
    if (!had) { c = this.share(c); had = this.ts.get(c) }
    if (had) {
      this.readId(had.kid)
      if (this.okId(had, had.kid)) return had
      return this.withinId(had.kid, () => this.truth0(c, had.kid))
    }
    const kid = this.allocKey()
    this.readId(kid)
    return this.withinId(kid, () => this.truth0(c, kid))
  }
  private truth0(c: C, kid: number): TV {
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
        const and = tupleAnd(c)
        if (and) { const x = this.truth(and); t = x.t; r = x; break }
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
    const out: TV = {t, w: r.w, fin: t !== undefined && r.fin, pos: r.pos, stamp: r.pos < 0 ? 0 : this.trail.stamp(r.pos), node: this.node, kid}
    this.ts.set(c, out)
    this.clean[kid] = 1
    return out
  }
  // kernel.ts's facts, each row with its reason; final when nothing it read is open.
  private factsOf(c: C, positive: boolean, out: Row[]): R {
    if (completeWorkProfile.enabled) checkWorkEndpoint('reader fact')
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
        // (and the facts are kept only while the part's own value is: its reason is theirs, though not their rows'; and
        // while the closed parts' are: one closed through an open term column opens when the column's choice is decided)
        const x = both(both(closed, r), last)
        return {w: x.w, pos: x.pos, fin: x.fin && last.t !== undefined}
      }
      case '<': case '<=': case '=': {
        const and = tupleAnd(c)
        if (and) return this.factsOf(and, positive, out)
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
    const key = (this.factKeys[i] ??= this.newSeg(0, i))
    this.readId(key.kid)
    const had = this.fs[i]
    if (had && this.okId(had, key.kid)) return had
    return this.withinId(key.kid, () => {
      const parts = this.parts(i)
      let rows: Row[] = [], pos = -1, fin = true
      if (parts.length === 1) { const f = this.part(parts[0]!); rows = f.rows; pos = f.pos; fin = f.fin }
      else for (const p of parts) { const f = this.part(p); for (const r of f.rows) rows.push(r); if (f.pos > pos) pos = f.pos; fin &&= f.fin }
      const out: FV = {rows, fin, pos, stamp: pos < 0 ? 0 : this.trail.stamp(pos), node: this.node}
      this.fs[i] = out
      this.clean[key.kid] = 1
      return out
    })
  }
  // Whether a hypothesis' facts are final (each part's).
  private factsFin(i: number): boolean { for (const p of this.parts(i)) if (!this.part(p).fin) return false; return true }
  // A hypothesis' conjuncts (a conjunction's parts, a negated disjunction's, flattened), each with its sign.
  private partsOf: {c: C, positive: boolean, key: Seg, fv?: FV}[][] = []
  private parts(i: number): {c: C, positive: boolean, key: Seg, fv?: FV}[] {
    let out = this.partsOf[i]
    if (out) return out
    const mine: {c: C, positive: boolean, key: Seg, fv?: FV}[] = []
    const flat = (c: C, positive: boolean): void => {
      if (c.op === 'not') return flat(c.x, !positive)
      if ((c.op === 'and' && positive) || (c.op === 'or' && !positive)) { for (const y of c.xs) flat(y, positive); return }
      mine.push({c, positive, key: this.newSeg(3, i, mine.length)})
    }
    flat(this.goal.hyps[i]!, true)
    return (this.partsOf[i] = out = mine)
  }
  private part(p: {c: C, positive: boolean, key: Seg, fv?: FV}): FV {
    const kid = p.key.kid
    this.readId(kid)
    const had = p.fv
    if (had && this.okId(had, kid)) return had
    return this.withinId(kid, () => {
      const rows: Row[] = [], r = this.factsOf(p.c, p.positive, rows)
      const out: FV = {rows, fin: r.fin, pos: r.pos, stamp: r.pos < 0 ? 0 : this.trail.stamp(r.pos), node: this.node}
      p.fv = out
      this.clean[kid] = 1
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
    if (completeWorkProfile.enabled) checkWorkEndpoint('reader form')
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
  // Whether a form reads a term column.
  readsColumn(lin: Lin): boolean { for (const j of this.form(lin).names) if (this.nameKind[j] === 1) return true; return false }
  // The trail's atom rows, by position, kept while the position's stamp is.
  private trailRows: Row[] = []
  private trailStamps: number[] = []
  private pairs = new Map<string, {parts?: [Lin, Lin][], pq: Lin, qp: Lin}>()
  // The rows in kernel.ts's order, copies kept (a leaf's derivation indexes these).
  // With `src`, each row's source beside it: the hypothesis whose facts it is, the pair of cells it equates, else -1.
  leafRows(src?: (number | [string, string])[], beforeRow?: (count: number) => void): Row[] {
    const rows: Row[] = []
    for (let i = 0; i < this.trail.size(); i++) {
      if (this.trail.quiet?.(i)) continue
      beforeRow?.(1)
      const s = this.trail.stamp(i)
      let r = this.trailStamps[i] === s ? this.trailRows[i] : undefined
      if (!r) {
        // (by the atom's own form, not its name: kernel.ts reads the names in a form's own order, which two forms of
        // one atom may not share, and the names' order is the order of the rows past the facts)
        const a = this.trail.lin(i), own = this.leafAtomRows.get(a.lin) ?? this.leafAtomRows.set(a.lin, []).get(a.lin)!, k = a.holds ? 1 : 0
        r = own[k] ?? (own[k] = {lin: atomOf(a.lin, a.holds).lin, w: new Set([a.name]), label: ''})
        this.trailRows[i] = r; this.trailStamps[i] = s
      }
      rows.push(r)
      src?.push(-1)
    }
    for (let i = 0; i < this.goal.hyps.length; i++) for (const r of this.facts(i).rows) { beforeRow?.(1); rows.push(r); src?.push(i) }
    // (each name once, in the order first read, as a set of texts would keep them)
    const g = ++this.gen, names: number[] = [], seen = this.nameSeen, kind = this.nameKind
    for (const r of rows) for (const j of this.form(r.lin).names) if (seen[j] !== g) { seen[j] = g; names.push(j) }
    const cells = names.filter(j => kind[j] === 2).map(j => cellOf(this.nameText[j]!))
    for (const [i, p] of cells.entries()) for (const q of cells.slice(i + 1)) {
      if (p.map !== q.map) continue
      const f = this.pair(p, q), w = this.equal(f)
      if (w) { beforeRow?.(1); rows.push({lin: f.pq, w, label: ''}); src?.push([p.name, q.name]); beforeRow?.(1); rows.push({lin: f.qp, w, label: ''}); src?.push([p.name, q.name]) }
    }
    const done = this.termSeen, todo = names.filter(j => kind[j] === 1)
    while (todo.length) {
      const j = todo.pop()!
      if (done[j] === g) continue
      done[j] = g
      for (const r of this.termRows(this.nameText[j]!)) {
        beforeRow?.(1); rows.push(r); src?.push(-1)
        for (const n of this.form(r.lin).names) { if (seen[n] !== g) { seen[n] = g; names.push(n) } if (kind[n] === 1 && done[n] !== g) todo.push(n) }
      }
    }
    for (const j of names) { beforeRow?.(1); const name = this.nameText[j]!; let r = this.natRows.get(name); if (!r) this.natRows.set(name, (r = {lin: completeWorkProfile.enabled?scale(v(name),-1):{[name]:-1}, w: none, label: ''})); rows.push(r); src?.push(-1) }
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
  // The hypothesis a live row came from (undefined for the trail's atoms, the naturals and the term columns' rows).
  srcOf(r: Row): number | undefined { return this.src.get(r) }
  private inSeg = new Map<Seg, Row[]>()
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
  // Per-cell enter/leave delta log for kernel/cdcl.ts's incremental openCellsLive (opt-in via `trackCells`):
  // parallel arrays record each Set.add (`1`) in nameOn and Set.delete (`0`) in nameOff in exact mutation order, so
  // replaying them reproduces `this.cells`'s exact map membership and Set insertion order without rescanning.
  trackCells = false
  readonly cellOpMap: string[] = []
  readonly cellOpName: string[] = []
  readonly cellOpOn: number[] = []
  // (`from`: the trail's first position that may have changed since the last sync, where the caller knows it)
  sync(from = 0): void {
    if (completeWorkProfile.enabled) checkWorkEndpoint('reader sync')
    this.syncing = true
    this.syncN++
    this.changed = []
    const n = this.trail.size()
    for (let i = from; i < Math.max(n, this.inTrail.length); i++) {
      const r = i < n && !this.trail.quiet?.(i) ? this.trailRow(i) : undefined, had = this.inTrail[i]
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
    const had = key.cached
    if (had && this.clean[key.kid] === 1) return had
    const rows = this.withinId(key.kid, (): Row[] => {
      if (key.kind === 1) return this.termRows(this.nameText[key.i]!)
      const p = cellOf(this.nameText[key.i]!), q = cellOf(this.nameText[key.j]!), f = this.pair(p, q), w = this.equal(f)
      if (!w) return []
      return [{lin: f.pq, w, label: ''}, {lin: f.qp, w, label: ''}]
    })
    key.cached = rows
    this.clean[key.kid] = 1
    return rows
  }
  // (each pair's forms made once: the same objects at every node, so what is kept per form is found again)
  // (two tuples: each part's difference; a plain key and a tuple, or tuples of different lengths: none, never equal)
  private pair(p: {name: string, key?: Lin, keys?: Lin[]}, q: {name: string, key?: Lin, keys?: Lin[]}) {
    const key = `${p.name}\u0000${q.name}`
    let f = this.pairs.get(key)
    if (!f) {
      if (this.pairs.size > 200_000) this.pairs.clear()
      const ds = p.key && q.key ? [sub(p.key, q.key)] : p.keys && q.keys && p.keys.length === q.keys.length ? p.keys.map((x, i) => sub(x, q.keys![i]!)) : undefined
      this.pairs.set(key, (f = {parts: ds?.map(d => [d, scale(d, -1)] as [Lin, Lin]), pq: sub(v(p.name), v(q.name)), qp: sub(v(q.name), v(p.name))}))
    }
    return f
  }
  // The reason the trail proves a pair's keys equal (every part's difference 0 both ways), or none.
  private equal(f: {parts?: [Lin, Lin][]}): W | undefined {
    if (!f.parts) return undefined
    let w = none
    for (const [d, neg] of f.parts) { const x = this.dec(d), y = this.dec(neg); if (x.t !== true || y.t !== true) return undefined; w = join(w, join(x.w, y.w)) }
    return w
  }
  private mark(id: number, live: boolean) {
    if (this.markN[id] === this.syncN) return
    this.markN[id] = this.syncN; this.wasLive[id] = live; this.changed.push(id)
  }
  // A copy of a row in (kind 1: from the trail or the facts, 2: a column's term rows, its own name not counted; 0: a
  // natural's or a pair of cells', whose names it doesn't count).
  private addCopy(r: Row, kind: number, self = -1) {
    const f = this.form(r.lin), id = f.id
    if (completeWorkProfile.enabled) startWork('copies', 1, 'reader add copy')
    const cs = (this.copies[id] ??= [])
    if (!completeWorkProfile.enabled) costs.copies++
    if (!cs.length) { this.mark(id, false); this.slot[id] = this.live.length; this.live.push(r) } else { const at = this.slot[id]!; if (r.w.size < this.live[at]!.w.size) this.live[at] = r }
    cs.push(r)
    if (kind) for (const j of f.names) if (j !== self) this.countUp(j, kind)
  }
  private removeCopy(r: Row, kind: number, self = -1) {
    const f = this.form(r.lin), id = f.id, cs = this.copies[id]!
    if (completeWorkProfile.enabled) startWork('copies', 1, 'reader remove copy'); else costs.copies++
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
    if (!r) this.natRows.set(name, (r = {lin: completeWorkProfile.enabled?scale(v(name),-1):{[name]:-1}, w: none, label: ''}))
    this.inNat[j] = r
    this.addCopy(r, 0)
    if (this.nameKind[j] === 2) {
      this.cellsOn++; this.cellsChanged++
      const c = cellOf(name)
      let same = this.cells.get(c.map)
      if (!same) this.cells.set(c.map, (same = new Set()))
      same.add(name)
      if (this.trackCells) { this.cellOpMap.push(c.map); this.cellOpName.push(name); this.cellOpOn.push(1) }
    }
    if (this.nameKind[j] === 1) this.segOn((this.termKeys[j] ??= this.newSeg(1, j)))
  }
  private nameOff(j: number) {
    this.removeCopy(this.inNat[j]!, 0)
    this.inNat[j] = undefined
    if (this.nameKind[j] === 2) {
      this.cellsOn--; this.cellsChanged++
      const name = this.nameText[j]!, map = cellOf(name).map
      this.cells.get(map)!.delete(name)
      if (this.trackCells) { this.cellOpMap.push(map); this.cellOpName.push(name); this.cellOpOn.push(0) }
    }
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
    if (!key) m.set(q, (key = this.newSeg(2, p, q)))
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
  // (the same array while it stands)
  private openShared: (boolean | undefined)[] = []
  private openStamp = 0
  private openP?: Map<object, number>
  private openN?: Map<object, number>
  private openT?: Map<object, number>
  openList(i: number): Lin[] {
    let kid = this.openIds[i]
    if (kid === undefined) this.openIds[i] = kid = this.allocKey()
    const had = this.os[i]
    if (had && ((keepClean && this.clean[kid] === 1) || had.node === this.node)) return had.lins
    const lins = this.withinId(kid, () => {
      if (this.factsFin(i)) return Reader.emptyLins
      const mine: Lin[] = []
      const h = this.goal.hyps[i]!
      let dag = this.openShared[i]
      if (dag === undefined) this.openShared[i] = dag = hasDagBlowup(h)
      if (dag) {
        const p = (this.openP ??= new Map()), n = (this.openN ??= new Map()), t = (this.openT ??= new Map())
        this.openHDag(h, mine, true, ++this.openStamp, p, n, t)
      } else {
        this.openHPlain(h, mine, true)
      }
      return mine.length ? mine : Reader.emptyLins
    })
    if (had) { had.lins = lins; had.node = this.node } else this.os[i] = {lins, node: this.node}
    this.clean[kid] = 1
    return lins
  }
  private openEPlain(e: E, out: Lin[]): void {
    switch (e.op) {
      case 'var': case 'const': return
      case 'mul': return this.openEPlain(e.a, out)
      case 'prod': return (this.openEPlain(e.a, out), this.openEPlain(e.b, out))
      case 'get': return this.openEPlain(e.key, out)
      case 'tup': return (this.openEPlain(e.a, out), this.openEPlain(e.b, out))
      case 'proj': return this.openEPlain(e.a.op === 'tup' ? (e.k === 0 ? e.a.a : e.a.b) : e.a, out)
      case 'if': { const t = this.truth(e.c); if (t.t === undefined) this.openCPlain(e.c, out); else this.openEPlain(t.t ? e.then : e.else, out); return }
      case 'add': case 'sub': case 'min': case 'max': {
        if (this.linear(e).fin) return
        this.openEPlain(e.a, out), this.openEPlain(e.b, out)
        const a = this.linear(e.a).lin, b = this.linear(e.b).lin
        if (a && b && !this.decided(e)) out.push(same(1, e, a, b, 0, () => (e.op === 'sub' ? sub(b, a) : sub(a, b))))
        return
      }
    }
  }
  private openCPlain(c: C, out: Lin[]): void {
    if (this.truth(c).t !== undefined) return
    if (c.op === 'flag' || c.op === 'all') return
    if (c.op === 'not') return this.openCPlain(c.x, out)
    if (c.op === 'and' || c.op === 'or') return c.xs.forEach(y => this.openCPlain(y, out))
    const and = tupleAnd(c)
    if (and) return this.openCPlain(and, out)
    const a = this.linear(c.a).lin, b = this.linear(c.b).lin
    const own: Lin[] = a && b ? same(7, c, a, b, 0, () => { const d = sub(a, b); return c.op === '<=' ? [d] : c.op === '<' ? [add(d, k(1))] : [d, scale(d, -1)] }) : []
    this.openEPlain(c.a, out), this.openEPlain(c.b, out)
    for (const x of own) out.push(x)
  }
  private openHPlain(c: C, out: Lin[], positive: boolean): void {
    if (c.op === 'not') return this.openHPlain(c.x, out, !positive)
    if ((c.op === 'and' && positive) || (c.op === 'or' && !positive)) return c.xs.forEach(y => this.openHPlain(y, out, positive))
    if (c.op === 'and' || c.op === 'or') {
      if (this.truth(c).t !== undefined) return
      const open = c.xs.filter(y => this.truth(y).t !== !positive)
      if (open.length === 1) this.openHPlain(open[0]!, out, positive)
      else this.openCPlain(c, out)
      return
    }
    if (c.op === 'flag' || c.op === 'all') return
    const and = tupleAnd(c)
    if (and) return this.openHPlain(and, out, positive)
    const before = out.length
    this.openEPlain(c.a, out), this.openEPlain(c.b, out)
    if (out.length === before && !positive && c.op === '=' && this.truth(c).t === undefined) this.openCPlain(c, out)
  }
  private openEDag(e: E, out: Lin[], stamp: number, tMap: Map<object, number>): boolean {
    if (e.op === 'var' || e.op === 'const') return false
    const tag = stamp * 2
    const hit = tMap.get(e)
    if (hit !== undefined && (hit === tag || hit === tag + 1)) return hit === tag + 1
    tMap.set(e, tag)
    const before = out.length
    let had = false
    switch (e.op) {
      case 'mul': had = this.openEDag(e.a, out, stamp, tMap); break
      case 'prod': case 'tup': { const a = this.openEDag(e.a, out, stamp, tMap), b = this.openEDag(e.b, out, stamp, tMap); had = a || b; break }
      case 'get': had = this.openEDag(e.key, out, stamp, tMap); break
      case 'proj': had = this.openEDag(e.a.op === 'tup' ? (e.k === 0 ? e.a.a : e.a.b) : e.a, out, stamp, tMap); break
      case 'if': { const t = this.truth(e.c); had = t.t === undefined ? this.openCDag(e.c, out, stamp, tMap) : this.openEDag(t.t ? e.then : e.else, out, stamp, tMap); break }
      case 'add': case 'sub': case 'min': case 'max': {
        if (this.linear(e).fin) return false
        const ea = this.openEDag(e.a, out, stamp, tMap), eb = this.openEDag(e.b, out, stamp, tMap)
        const a = this.linear(e.a).lin, b = this.linear(e.b).lin
        if (a && b && !this.decided(e)) out.push(same(1, e, a, b, 0, () => (e.op === 'sub' ? sub(b, a) : sub(a, b))))
        had = ea || eb || out.length > before
        break
      }
    }
    had = had || out.length > before
    if (had) tMap.set(e, tag + 1)
    return had
  }
  private openCDag(c: C, out: Lin[], stamp: number, tMap: Map<object, number>): boolean {
    if (c.op === 'flag' || c.op === 'all') return false
    const tag = stamp * 2
    const hit = tMap.get(c)
    if (hit !== undefined && (hit === tag || hit === tag + 1)) return hit === tag + 1
    tMap.set(c, tag)
    if (this.truth(c).t !== undefined) return false
    const before = out.length
    let had = false
    if (c.op === 'not') had = this.openCDag(c.x, out, stamp, tMap)
    else if (c.op === 'and' || c.op === 'or') { for (const y of c.xs) if (this.openCDag(y, out, stamp, tMap)) had = true }
    else {
      const and = tupleAnd(c)
      if (and) had = this.openCDag(and, out, stamp, tMap)
      else {
        const a = this.linear(c.a).lin, b = this.linear(c.b).lin
        const own: Lin[] = a && b ? same(7, c, a, b, 0, () => { const d = sub(a, b); return c.op === '<=' ? [d] : c.op === '<' ? [add(d, k(1))] : [d, scale(d, -1)] }) : []
        const ea = this.openEDag(c.a, out, stamp, tMap), eb = this.openEDag(c.b, out, stamp, tMap)
        for (const x of own) out.push(x)
        had = ea || eb || out.length > before
      }
    }
    had = had || out.length > before
    if (had) tMap.set(c, tag + 1)
    return had
  }
  private openHDag(c: C, out: Lin[], positive: boolean, stamp: number, pMap: Map<object, number>, nMap: Map<object, number>, tMap: Map<object, number>): void {
    const bag = positive ? pMap : nMap
    if (bag.get(c) === stamp) return
    bag.set(c, stamp)
    if (c.op === 'not') return this.openHDag(c.x, out, !positive, stamp, pMap, nMap, tMap)
    if ((c.op === 'and' && positive) || (c.op === 'or' && !positive)) return c.xs.forEach(y => this.openHDag(y, out, positive, stamp, pMap, nMap, tMap))
    if (c.op === 'and' || c.op === 'or') {
      if (this.truth(c).t !== undefined) return
      const open = c.xs.filter(y => this.truth(y).t !== !positive)
      if (open.length === 1) this.openHDag(open[0]!, out, positive, stamp, pMap, nMap, tMap)
      else this.openCDag(c, out, stamp, tMap)
      return
    }
    if (c.op === 'flag' || c.op === 'all') return
    const and = tupleAnd(c)
    if (and) return this.openHDag(and, out, positive, stamp, pMap, nMap, tMap)
    const ea = this.openEDag(c.a, out, stamp, tMap), eb = this.openEDag(c.b, out, stamp, tMap)
    if (!ea && !eb && !positive && c.op === '=' && this.truth(c).t === undefined) this.openCDag(c, out, stamp, tMap)
  }
}

export type HypAstInfo = {nodes: number, dag: boolean}
const hypAstMemo = new WeakMap<C, HypAstInfo>()
const UNFOLD_CAP = 1_000_000

// Counts distinct AST nodes in `root` and checks whether unrolling shared
// subtrees exceeds max(4096, 2 * nodes). Cached per `C` so repeated goals in
// invariant search pay O(1) WeakMap hits and linear-size trees keep zero-Map
// traversal in Reader.openList, prove.ts openH, and treeKey.
export function hypAstInfo(root: C): HypAstInfo {
  const hit = hypAstMemo.get(root)
  if (hit !== undefined) return hit
  const seen = new Set<object>()
  const stack: (C | E)[] = [root]
  let shared = false
  while (stack.length) {
    const n = stack.pop()!
    if (seen.has(n)) {
      if (n.op !== 'var' && n.op !== 'const' && n.op !== 'flag') shared = true
      continue
    }
    seen.add(n)
    switch (n.op) {
      case 'var': case 'const': case 'flag': break
      case 'all': stack.push(n.c); break
      case 'not': stack.push(n.x); break
      case 'and': case 'or': for (let i = 0; i < n.xs.length; i++) stack.push(n.xs[i]!); break
      case 'mul': case 'proj': stack.push(n.a); break
      case 'get': stack.push(n.key); break
      case 'if': stack.push(n.c, n.then, n.else); break
      case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup':
      case '<': case '<=': case '=': stack.push(n.a, n.b); break
    }
  }
  const nodes = seen.size
  let dag = false
  if (shared) {
    const sizes = new Map<object, number>()
    const post: (C | E)[] = [root]
    const expanded = new Set<object>()
    while (post.length) {
      const n = post[post.length - 1]!
      if (sizes.has(n)) { post.pop(); continue }
      if (!expanded.has(n)) {
        expanded.add(n)
        switch (n.op) {
          case 'var': case 'const': case 'flag': sizes.set(n, 1); post.pop(); break
          case 'all': post.push(n.c); break
          case 'not': post.push(n.x); break
          case 'and': case 'or': for (let i = 0; i < n.xs.length; i++) post.push(n.xs[i]!); break
          case 'mul': case 'proj': post.push(n.a); break
          case 'get': post.push(n.key); break
          case 'if': post.push(n.c, n.then, n.else); break
          case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup':
          case '<': case '<=': case '=': post.push(n.a, n.b); break
        }
      } else {
        post.pop()
        let s = 1
        switch (n.op) {
          case 'var': case 'const': case 'flag': break
          case 'all': s += sizes.get(n.c) ?? 1; break
          case 'not': s += sizes.get(n.x) ?? 1; break
          case 'and': case 'or': for (let i = 0; i < n.xs.length; i++) { s += sizes.get(n.xs[i]!) ?? 1; if (s >= UNFOLD_CAP) { s = UNFOLD_CAP; break } } break
          case 'mul': case 'proj': s += sizes.get(n.a) ?? 1; break
          case 'get': s += sizes.get(n.key) ?? 1; break
          case 'if': s += (sizes.get(n.c) ?? 1) + (sizes.get(n.then) ?? 1) + (sizes.get(n.else) ?? 1); break
          case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup':
          case '<': case '<=': case '=': s += (sizes.get(n.a) ?? 1) + (sizes.get(n.b) ?? 1); break
        }
        sizes.set(n, s > UNFOLD_CAP ? UNFOLD_CAP : s)
      }
    }
    // Below 4096, the plain walk is cheap and keeps the exact open list (repeats included) that the search's counted budget reads.
    const unrolled = sizes.get(root) ?? nodes
    dag = unrolled >= UNFOLD_CAP || unrolled > Math.max(4096, nodes * 2)
  }
  const info: HypAstInfo = {nodes, dag}
  hypAstMemo.set(root, info)
  return info
}
export const hasDagBlowup = (root: C): boolean => hypAstInfo(root).dag

// A form's variables, and a cell's map and key, remembered (read at every node).
const nameMemo = new WeakMap<Lin, string[]>()
export const namesOf = (lin: Lin): string[] => {
  let out = nameMemo.get(lin)
  if (!out) nameMemo.set(lin, (out = Object.keys(lin).filter(key => key !== '1')))
  return out
}
const cellMemo = new Map<string, {name: string, map: string, key?: Lin, keys?: Lin[]}>()
const cellOf = (name: string) => {
  let out = cellMemo.get(name)
  if (!out) { if (cellMemo.size > 100_000) cellMemo.clear(); cellMemo.set(name, (out = {name, ...cellParts(name)})) }
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

// --- The clausal reading (kernel/cdcl.ts's clausal mode, for a model alone) ------------------------------------------
// A goal's hypotheses as clauses over literals: an atom (lin <= 0, held or not) or a fresh yes/no τ<h>_<n> (a gate: a
// subformula's truth, read only as a decision, never a row). A term's choices (if, min, max, ∸) are lifted out of the
// comparison that reads them: each case its conditions' literals and its linear form, the comparison of that case under
// them; a term of more than `maxCases` cases is a fresh natural ϰ<h>_<n>, each case's form under its conditions. A gate
// is written for the polarities it is read in (Plaisted and Greenbaum: read true, it implies its formula; read false, the
// formula implies it), so a partial assignment that satisfies every clause is a model of the goal at any point of the
// atoms it assigns (the literals left open are read by satisfied clauses only). Gates and columns are kept per side
// (`sideOf` a hypothesis, which interpolation colors them by; h in the name is the hypothesis that first wrote them).
// `add` is false where a hypothesis reads what the kernel reads otherwise (a product, a map, a flag, a quantifier, a
// name that is no plain variable): the caller then reads the goal as the kernel does.
export type Lit = {lin: Lin, holds: boolean}
type Case = {g: Lit[], lin: Lin}
const notLit = (l: Lit): Lit => ({lin: l.lin, holds: !l.holds})
const litIds = new WeakMap<Lin, [string, boolean]>()
// A literal's variable (the smaller of its atom's texts, as kernel/cdcl.ts names it) and value.
export const litVar = (l: Lit): [string, boolean] => {
  let x = litIds.get(l.lin)
  if (!x) { const a = canon(l.lin), f = canonFlip(l.lin); litIds.set(l.lin, (x = f < a ? [f, false] : [a, true])) }
  return [x[0], x[1] === l.holds]
}
const isConst = (lin: Lin) => { for (const key in lin) if (key !== '1' && lin[key] !== 0) return false; return true }
class Unread extends Error {}
export class Clausal {
  // The clauses made since the caller last took them (each a disjunction, with the hypothesis it is for; `own`: a gate's,
  // its first literal the gate's, so the clause is needed only where that literal is false; `out`: its last literal a
  // case's atom, which the clause's other literals false imply, so a search need never decide it for this clause).
  made: {lits: Lit[], hyp: number, own: boolean, out: boolean}[] = []
  private n = 0
  private hyp = 0
  private gm = new Map<number, Map<object, {l: Lit | boolean, done: number}>>()
  private cm = new Map<number, Map<object, Case[]>>()
  constructor(readonly sideOf: (hyp: number) => number = () => 0, readonly maxCases = 16) {}
  add(c: C, hyp: number): boolean {
    this.hyp = hyp
    try { this.top(c, true); return true } catch (e) { if (e instanceof Unread) return false; throw e }
  }
  private memo<T>(m: Map<number, Map<object, T>>): Map<object, T> {
    const s = this.sideOf(this.hyp)
    let out = m.get(s)
    if (!out) m.set(s, (out = new Map()))
    return out
  }
  private fresh(kind: string): string { return `${kind}${this.hyp}_${this.n++}` }
  private clause(lits: Lit[], own = false, last = false) {
    const seen = new Map<string, boolean>(), out: Lit[] = []
    for (const l of lits) {
      const [x, val] = litVar(l), had = seen.get(x)
      if (had === undefined) { seen.set(x, val); out.push(l) } else if (had !== val) return
    }
    this.made.push({lits: out, hyp: this.hyp, own, out: last && out.at(-1) === lits.at(-1)})
  }
  private top(c: C, positive: boolean): void {
    switch (c.op) {
      case 'not': return this.top(c.x, !positive)
      case 'and': case 'or': {
        if ((c.op === 'and') === positive) { for (const y of c.xs) this.top(y, positive); return }
        const lits: Lit[] = []
        for (const y of c.xs) { const l = this.lit(y, positive ? 1 : 2), m = typeof l === 'boolean' ? l === positive : positive ? l : notLit(l); if (m === true) return; if (m !== false) lits.push(m) }
        return this.clause(lits)
      }
      case '<': case '<=': case '=':
        for (const cs of this.cmpCases(c)) {
          const not = cs.g.map(notLit)
          if (positive) { if (cs.atoms === false) this.clause(not); else if (cs.atoms !== true) for (const a of cs.atoms) this.clause([...not, a], false, true) }
          else if (cs.atoms === true) this.clause(not)
          else if (cs.atoms !== false) this.clause([...not, ...cs.atoms.map(notLit)])
        }
        return
      case 'flag': case 'all': throw new Unread()
    }
  }
  // A condition's literal (or its constant truth), its gate written for `pol` (1: read true, 2: read false, 3: both).
  private lit(c: C, pol: number): Lit | boolean {
    switch (c.op) {
      case 'not': { const x = this.lit(c.x, ((pol & 1) << 1) | ((pol & 2) >> 1)); return typeof x === 'boolean' ? !x : notLit(x) }
      case 'and': case 'or': case '<': case '<=': case '=': break
      case 'flag': case 'all': throw new Unread()
    }
    const m = this.memo(this.gm), had = m.get(c)
    if (had && (typeof had.l === 'boolean' || !(pol & ~had.done))) return had.l
    const need = had ? pol & ~had.done : pol
    let g: Lit | undefined = had?.l as Lit | undefined, out: Lit | boolean
    const gate = () => (g ??= {lin: v(this.fresh('τ')), holds: true})
    if (c.op === 'and' || c.op === 'or') {
      const dominant = c.op === 'or', kids: Lit[] = []
      let fold: boolean | undefined
      for (const y of c.xs) { const l = this.lit(y, need); if (typeof l === 'boolean') { if (l === dominant) { fold = dominant; break } } else kids.push(l) }
      if (fold !== undefined || !kids.length) out = fold ?? !dominant
      else if (kids.length === 1) out = kids[0]!
      else {
        const t = gate()
        if (need & 1) { if (dominant) this.clause([notLit(t), ...kids], true); else for (const x of kids) this.clause([notLit(t), x], true) }
        if (need & 2) { if (dominant) for (const x of kids) this.clause([t, notLit(x)], true); else this.clause([t, ...kids.map(notLit)], true) }
        out = t
      }
    } else {
      const cases = this.cmpCases(c)
      if (cases.length === 1 && !cases[0]!.g.length && (typeof cases[0]!.atoms === 'boolean' || cases[0]!.atoms.length === 1)) out = typeof cases[0]!.atoms === 'boolean' ? cases[0]!.atoms : cases[0]!.atoms[0]!
      else {
        const t = gate()
        for (const cs of cases) {
          const not = cs.g.map(notLit)
          if (need & 1) { if (cs.atoms === false) this.clause([notLit(t), ...not], true); else if (cs.atoms !== true) for (const a of cs.atoms) this.clause([notLit(t), ...not, a], true, true) }
          if (need & 2) { if (cs.atoms === true) this.clause([t, ...not], true); else if (cs.atoms !== false) this.clause([t, ...not, ...cs.atoms.map(notLit)], true) }
        }
        out = t
      }
    }
    m.set(c, {l: out, done: (had?.done ?? 0) | need})
    return out
  }
  // A comparison's cases: each its conditions and its atoms (true or false where they are constant).
  private cmpCases(c: Extract<C, {a: E}>): {g: Lit[], atoms: Lit[] | boolean}[] {
    return this.cross(this.cases(c.a), this.cases(c.b), sub).map(({g, lin: d}) => {
      const lins = c.op === '<=' ? [d] : c.op === '<' ? [add(d, k(1))] : [d, scale(d, -1)], atoms: Lit[] = []
      for (const lin of lins) { if (!isConst(lin)) atoms.push({lin, holds: true}); else if ((lin['1'] ?? 0) > 0) return {g, atoms: false} }
      return {g, atoms: atoms.length ? atoms : true}
    })
  }
  // A guard joined to a case's: undefined where it contradicts it.
  private join(g: Lit[], more: Lit[]): Lit[] | undefined {
    if (!more.length) return g
    if (!g.length) return more
    const out = [...g], ids = new Map(g.map(l => litVar(l)))
    for (const l of more) { const [x, val] = litVar(l), had = ids.get(x); if (had === undefined) { ids.set(x, val); out.push(l) } else if (had !== val) return undefined }
    return out
  }
  private cross(xs: Case[], ys: Case[], f: (a: Lin, b: Lin) => Lin): Case[] {
    const out: Case[] = []
    for (const x of xs) for (const y of ys) { const g = this.join(x.g, y.g); if (g) out.push({g, lin: f(x.lin, y.lin)}) }
    return out
  }
  // A case split on a literal: `yes` where it holds, `no` where it doesn't.
  private split(c: Case, l: Lit | boolean, yes: Lin, no: Lin): Case[] {
    if (typeof l === 'boolean') return [{g: c.g, lin: l ? yes : no}]
    const out: Case[] = []
    for (const [m, lin] of [[l, yes], [notLit(l), no]] as const) { const g = this.join(c.g, [m]); if (g) out.push({g, lin}) }
    return out
  }
  private cases(e: E): Case[] {
    const m = this.memo(this.cm), had = m.get(e)
    if (had) return had
    let out: Case[]
    switch (e.op) {
      case 'var': if (e.name === '1' || /[*[\],:⟦⟨⟩|]/.test(e.name)) throw new Unread(); out = [{g: [], lin: v(e.name)}]; break
      case 'const': out = [{g: [], lin: k(e.value)}]; break
      case 'add': out = this.cross(this.cases(e.a), this.cases(e.b), add); break
      case 'mul': out = this.cases(e.a).map(c => ({g: c.g, lin: scale(c.lin, e.k)})); break
      case 'sub': case 'min': case 'max': {
        // (∸: a − b where b <= a, else 0; min: a where a <= b, else b; max the other way)
        out = []
        for (const x of this.cases(e.a)) for (const y of this.cases(e.b)) {
          const g = this.join(x.g, y.g)
          if (!g) continue
          const a = x.lin, b = y.lin, d = e.op === 'sub' ? sub(b, a) : sub(a, b)
          out.push(...this.split({g, lin: a}, isConst(d) ? (d['1'] ?? 0) <= 0 : {lin: d, holds: true}, e.op === 'sub' ? sub(a, b) : e.op === 'min' ? a : b, e.op === 'sub' ? {} : e.op === 'min' ? b : a))
        }
        break
      }
      case 'get': {
        // (a division or remainder by a constant, core/machine.ts's div$c and mod$c: a fresh natural q per case of its
        // key x with c·q <= x <= c·q + c − 1, the remainder x − c·q)
        const f = /^(div|mod)\$(\d+)$/.exec(e.map)
        if (!f) throw new Unread()
        const c = Number(f[2]!)
        out = []
        for (const x of this.cases(e.key)) {
          const q = v(this.fresh('ϰ')), cq = scale(q, c), not = x.g.map(notLit)
          for (const lin of [sub(cq, x.lin), add(sub(x.lin, cq), k(1 - c))]) this.clause([...not, {lin, holds: true}])
          out.push({g: x.g, lin: f[1] === 'div' ? q : sub(x.lin, cq)})
        }
        break
      }
      case 'if': {
        const l = this.lit(e.c, 3)
        if (typeof l === 'boolean') { out = this.cases(l ? e.then : e.else); break }
        out = []
        for (const [m2, x] of [[l, e.then], [notLit(l), e.else]] as const) for (const c of this.cases(x)) { const g = this.join(c.g, [m2]); if (g) out.push({g, lin: c.lin}) }
        break
      }
      case 'prod': case 'tup': case 'proj': throw new Unread()
    }
    if (out.length > this.maxCases) {
      const col = v(this.fresh('ϰ'))
      for (const c of out) { const not = c.g.map(notLit); for (const lin of [sub(col, c.lin), sub(c.lin, col)]) if (!isConst(lin)) this.clause([...not, {lin, holds: true}], false, true); else if ((lin['1'] ?? 0) > 0) this.clause(not) }
      out = [{g: [], lin: col}]
    }
    m.set(e, out)
    return out
  }
}
