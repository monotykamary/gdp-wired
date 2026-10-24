// Untrusted: an incremental simplex over the rows a search reads at its nodes (each row lin <= 0), in floating point,
// as an SMT solver's arithmetic does it (Dutertre and de Moura's general form). A row of one variable is a bound on
// it; any other row is a bound on a slack, one per linear form up to a factor (each slack a basic variable of the
// tableau, its form over the nonbasic ones). `load` makes a node's rows the bounds (the tableau and the basis are kept
// from the node before, so a node that differs a little from the last costs a few pivots, not an elimination);
// `check` pivots until every basic variable is within its bounds (Bland's rule) or a row can't be: its explanation,
// the rows whose bounds it reads, is a rational refutation's support. Floating point only picks the rows: the caller
// refutes them exactly (core/solver.ts) and the kernel checks that; a verdict the floats misjudge costs a fallback.
// Bounds are rounded to integers (every variable is a natural, every form an integer combination): what a cut of the
// row by its coefficients' divisor gives, which the exact elimination makes as well. Over the rationals (`integral`
// false) nothing is rounded, and a strict row's bound is moved in by a hair (1e-7, relative): the floats only pick a
// conflict's rows, which the exact elimination then refutes, strictness and all, or doesn't.
import {type Lin, gcd} from '../core/solver.ts'

const eps = 1e-9
// A bound's tolerance: relative past 1 (values drift by a few ulps a pivot).
const tol = (b: number) => 1e-7 * Math.max(1, Math.abs(b))
type Form = {slack: string, g: number, terms: [string, number][]} // the row's variable part is g · (the slack's form)
const formMemo = new WeakMap<Lin, Form | {single: string, c: number} | null>()
function formOf(lin: Lin): Form | {single: string, c: number} | null {
  let out = formMemo.get(lin)
  if (out !== undefined) return out
  const keys = Object.keys(lin).filter(key => key !== '1' && lin[key] !== 0).sort()
  if (!keys.length) out = null
  else if (keys.length === 1) out = {single: keys[0]!, c: lin[keys[0]!]!}
  else {
    let g = 0
    for (const key of keys) g = gcd(g, lin[key]!)
    if (lin[keys[0]!]! < 0) g = -g
    const terms = keys.map(key => [key, lin[key]! / g] as [string, number])
    out = {slack: `σ(${terms.map(([key, c]) => `${key}:${c}`).join(',')})`, g, terms}
  }
  formMemo.set(lin, out)
  return out
}

export type SimplexVerdict = {kind: 'sat'} | {kind: 'conflict', rows: number[]} | {kind: 'unknown'}

export class Simplex {
  // `boundsOnly`: only the bounds are kept (assert, retract and their versions; no settle or check).
  constructor(readonly integral = true, readonly boundsOnly = false) {}
  private index = new Map<string, number>()
  private lo: number[] = []
  private hi: number[] = []
  private loWhy: number[] = []
  private hiWhy: number[] = []
  private val: number[] = []
  // A basic variable's row: basic = Σ coef · nonbasic. rowOf[x] its row, or -1 for a nonbasic one; colOf[x] the rows
  // a nonbasic x appears in.
  private rowOf: number[] = []
  private rows: {basic: number, coef: Map<number, number>}[] = []
  private colOf: Set<number>[] = []
  pivots = 0
  private nnzN = 0
  private at = new WeakMap<Lin, {j: number, c: number} | null>()
  // (a row's variable and coefficient, kept per form)
  private place(lin: Lin): {j: number, c: number} | null {
    let at = this.at.get(lin)
    if (at === undefined) {
      const f = formOf(lin)
      at = f === null ? null : 'single' in f ? {j: this.varOf(f.single), c: f.c} : {j: this.slackOf(f), c: f.g}
      this.at.set(lin, at)
    }
    return at
  }
  private varOf(name: string): number {
    let j = this.index.get(name)
    if (j !== undefined) return j
    j = this.val.length
    this.index.set(name, j)
    this.lo.push(-Infinity); this.hi.push(Infinity); this.loWhy.push(-1); this.hiWhy.push(-1)
    this.val.push(0); this.rowOf.push(-1); this.colOf.push(new Set())
    return j
  }
  // A slack for a form: basic, its row the form with each basic variable in it replaced by that one's row.
  private slackOf(f: Form): number {
    const had = this.index.get(f.slack)
    if (had !== undefined) return had
    const coef = new Map<number, number>()
    const addTo = (j: number, c: number) => { const x = (coef.get(j) ?? 0) + c; if (Math.abs(x) < eps) coef.delete(j); else coef.set(j, x) }
    for (const [name, c] of f.terms) {
      const j = this.varOf(name), r = this.rowOf[j]!
      if (r < 0) addTo(j, c)
      else for (const [k, a] of this.rows[r]!.coef) addTo(k, c * a)
    }
    const s = this.varOf(f.slack), r = this.rows.length
    this.rows.push({basic: s, coef})
    this.nnzN += coef.size
    this.rowOf[s] = r
    for (const j of coef.keys()) this.colOf[j]!.add(r)
    let value = 0
    for (const [j, c] of coef) value += c * this.val[j]!
    this.val[s] = value
    return s
  }
  // A node's rows as the bounds (a natural's own row x >= 0 among them). A pair of bounds that cross is a conflict at
  // once.
  load(rows: {lin: Lin, strict?: boolean}[]): SimplexVerdict {
    for (let j = 0; j < this.val.length; j++) { this.lo[j] = -Infinity; this.hi[j] = Infinity; this.loWhy[j] = -1; this.hiWhy[j] = -1 }
    const tighten = (j: number, upper: boolean, b: number, why: number) => {
      if (upper) { if (b < this.hi[j]!) { this.hi[j] = b; this.hiWhy[j] = why } }
      else if (b > this.lo[j]!) { this.lo[j] = b; this.loWhy[j] = why }
    }
    const integral = this.integral
    // c·x + k <= 0: x <= −k/c (c > 0) or x >= k/−c (c < 0); rounded to integers, or over the rationals moved in when
    // strict.
    const bound = (c: number, j: number, k: number, i: number, strict: boolean | undefined) => {
      const b = c > 0 ? -k / c : k / -c
      if (integral) { if (c > 0) tighten(j, true, Math.floor(b + eps), i); else tighten(j, false, Math.ceil(b - eps), i); return }
      const d = strict ? 1e-7 * Math.max(1, Math.abs(b)) : 0
      if (c > 0) tighten(j, true, b - d, i); else tighten(j, false, b + d, i)
    }
    for (let i = 0; i < rows.length; i++) {
      const r = rows[i]!, k = r.lin['1'] ?? 0
      const at = this.place(r.lin)
      if (at === null) { if (k > 0 || (!integral && r.strict && k >= 0)) return {kind: 'conflict', rows: [i]}; continue }
      // c·x + k <= 0 (a slack's: g·form + k <= 0)
      bound(at.c, at.j, k, i, !integral && r.strict)
    }
    for (let j = 0; j < this.val.length; j++) if (this.lo[j]! > this.hi[j]! + eps) return {kind: 'conflict', rows: [this.loWhy[j]!, this.hiWhy[j]!].filter(x => x >= 0)}
    // Nonbasic variables into their bounds, then each basic one computed afresh from its row (no drift from the shifts
    // of earlier nodes).
    for (let j = 0; j < this.val.length; j++) {
      if (this.rowOf[j]! >= 0) continue
      const x = this.val[j]!
      this.val[j] = x < this.lo[j]! ? this.lo[j]! : x > this.hi[j]! ? this.hi[j]! : x
    }
    for (const row of this.rows) {
      let value = 0
      for (const [j, c] of row.coef) value += c * this.val[j]!
      this.val[row.basic] = value
    }
    return {kind: 'sat'}
  }
  // Incremental use, a node's rows as the last node's with some in and some out (kernel/cdcl.ts's search): each row's
  // bound asserted and retracted by an id, a variable's bounds the tightest of those in (the first asserted among
  // equals); `settle` then finds a conflict among them (a constant row that is false, two bounds that cross: the least
  // such variable) or moves each nonbasic value whose bounds changed into them, and `check` goes on as after `load`, a
  // conflict's rows given by their ids. The basic values are computed afresh from their rows every 16 settles.
  private ins = new Map<number, {j: number, upper: boolean, b: number} | null>()
  private inLo: [number, number][][] = []
  private inHi: [number, number][][] = []
  private falseIn = new Set<number>()
  private crossing = new Set<number>()
  private moved: number[] = []
  private movedAt: number[] = []
  private settles = 0
  assert(id: number, lin: Lin, strict?: boolean): void {
    const at = this.place(lin), k = lin['1'] ?? 0
    if (at === null) { this.ins.set(id, null); if (k > 0 || (!this.integral && strict && k >= 0)) this.falseIn.add(id); return }
    const {j, c} = at, b0 = c > 0 ? -k / c : k / -c, upper = c > 0, d = !this.integral && strict ? 1e-7 * Math.max(1, Math.abs(b0)) : 0
    const b = this.integral ? (upper ? Math.floor(b0 + eps) : Math.ceil(b0 - eps)) : upper ? b0 - d : b0 + d
    this.ins.set(id, {j, upper, b});
    ((upper ? this.inHi : this.inLo)[j] ??= []).push([b, id])
    if (upper ? b < this.hi[j]! : b > this.lo[j]!) { if (upper) { this.hi[j] = b; this.hiWhy[j] = id } else { this.lo[j] = b; this.loWhy[j] = id } this.move(j) }
  }
  retract(id: number): void {
    const a = this.ins.get(id)
    this.ins.delete(id)
    if (a === undefined) return
    if (a === null) { this.falseIn.delete(id); return }
    const {j, upper} = a, list = (upper ? this.inHi : this.inLo)[j]!
    list.splice(list.findIndex(x => x[1] === id), 1)
    if ((upper ? this.hiWhy : this.loWhy)[j] !== id) return
    let b = upper ? Infinity : -Infinity, why = -1
    for (const [x, i] of list) if (upper ? x < b : x > b) { b = x; why = i }
    if (upper) { this.hi[j] = b; this.hiWhy[j] = why } else { this.lo[j] = b; this.loWhy[j] = why }
    this.move(j)
  }
  private move(j: number) {
    this.vers[j] = (this.vers[j] ?? 0) + 1
    if (!this.boundsOnly && this.movedAt[j] !== this.settles + 1) { this.movedAt[j] = this.settles + 1; this.moved.push(j) }
  }
  private vers: number[] = []
  // How many times a variable's bounds have changed.
  version(j: number): number { return this.vers[j] ?? 0 }
  value(j: number): number { return this.val[j]! }
  settle(): SimplexVerdict {
    for (const id of this.falseIn) return {kind: 'conflict', rows: [id]}
    for (const j of this.moved) { if (this.lo[j]! > this.hi[j]! + eps) this.crossing.add(j); else this.crossing.delete(j) }
    if (this.crossing.size) {
      let j = Infinity
      for (const x of this.crossing) if (x < j) j = x
      return {kind: 'conflict', rows: [this.loWhy[j]!, this.hiWhy[j]!].filter(x => x >= 0)}
    }
    for (const j of this.moved) {
      if (this.rowOf[j]! >= 0) continue
      const x = this.val[j]!, to = x < this.lo[j]! ? this.lo[j]! : x > this.hi[j]! ? this.hi[j]! : x
      if (to !== x) this.shift(j, to - x)
    }
    this.moved = []
    if (++this.settles % 16 === 0) for (const row of this.rows) { let value = 0; for (const [j, c] of row.coef) value += c * this.val[j]!; this.val[row.basic] = value }
    return {kind: 'sat'}
  }
  // A variable's index by name (undefined where no row has read it); its bounds and the ids that give them.
  indexOf(name: string): number | undefined { return this.index.get(name) }
  low(j: number): number { return this.lo[j]! }
  high(j: number): number { return this.hi[j]! }
  lowWhy(j: number): number { return this.loWhy[j]! }
  highWhy(j: number): number { return this.hiWhy[j]! }
  private shift(j: number, d: number) {
    this.val[j]! += d
    for (const r of this.colOf[j]!) { const row = this.rows[r]!; this.val[row.basic]! += row.coef.get(j)! * d }
  }
  check(maxPivots = 5_000): SimplexVerdict {
    for (let n = 0; n < maxPivots; n++) {
      // Bland: the violated basic variable of least index, then the nonbasic one of least index that can move.
      let b = -1
      for (const row of this.rows) {
        const j = row.basic, x = this.val[j]!
        if ((x < this.lo[j]! - tol(this.lo[j]!) || x > this.hi[j]! + tol(this.hi[j]!)) && (b < 0 || j < b)) b = j
      }
      if (b < 0) return {kind: 'sat'}
      const row = this.rows[this.rowOf[b]!]!, below = this.val[b]! < this.lo[b]!
      let e = -1
      for (const [j, a] of row.coef) {
        if (e >= 0 && j > e) continue
        const up = below === a > 0 // whether x_j must rise
        if (up ? this.val[j]! < this.hi[j]! - eps : this.val[j]! > this.lo[j]! + eps) e = j
      }
      if (e < 0) {
        const why = [below ? this.loWhy[b]! : this.hiWhy[b]!]
        for (const [j, a] of row.coef) why.push(below === a > 0 ? this.hiWhy[j]! : this.loWhy[j]!)
        return {kind: 'conflict', rows: [...new Set(why)].filter(x => x >= 0)}
      }
      const target = below ? this.lo[b]! : this.hi[b]!
      this.pivot(b, e, target)
      this.pivots++
    }
    return {kind: 'unknown'}
  }
  // x_b leaves the basis for x_e, x_b set to `target`.
  private pivot(b: number, e: number, target: number) {
    const r = this.rowOf[b]!, row = this.rows[r]!, a = row.coef.get(e)!
    // x_e = (x_b − Σ_{j≠e} c_j x_j) / a
    const theta = (target - this.val[b]!) / a
    this.shift(e, theta) // moves x_b to target and every other basic variable with x_e
    const ecoef = new Map<number, number>()
    for (const [j, c] of row.coef) if (j !== e) ecoef.set(j, -c / a)
    ecoef.set(b, 1 / a)
    for (const j of row.coef.keys()) this.colOf[j]!.delete(r)
    this.nnzN += ecoef.size - row.coef.size
    row.basic = e; row.coef = ecoef
    this.rowOf[e] = r; this.rowOf[b] = -1
    for (const j of ecoef.keys()) this.colOf[j]!.add(r)
    // Every other row reading x_e: substitute.
    for (const q of [...this.colOf[e]!]) {
      if (q === r) continue
      const other = this.rows[q]!, c = other.coef.get(e)!, before = other.coef.size
      other.coef.delete(e); this.colOf[e]!.delete(q)
      for (const [j, d] of ecoef) {
        const x = (other.coef.get(j) ?? 0) + c * d
        if (Math.abs(x) < eps) { if (other.coef.delete(j)) this.colOf[j]!.delete(q) } else { if (!other.coef.has(j)) this.colOf[j]!.add(q); other.coef.set(j, x) }
      }
      this.nnzN += other.coef.size - before
    }
    this.colOf[e]!.delete(r)
    for (const j of ecoef.keys()) this.colOf[j]!.add(r)
  }
  // Whether a row (lin <= 0) holds at the current point, or undefined where it reads a variable the tableau hasn't met.
  holds(lin: Lin): boolean | undefined {
    let x = lin['1'] ?? 0
    for (const key in lin) {
      if (key === '1') continue
      const j = this.index.get(key)
      if (j === undefined) return undefined
      x += lin[key]! * this.val[j]!
    }
    return x <= tol(x)
  }
  get size(): number { return this.rows.length }
  get nnz(): number { return this.nnzN }
  get vars(): number { return this.val.length }
}
