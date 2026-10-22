// The observation table: a grammar of terms evaluated on samples (rows: reachable states, transition pairs, argument
// tuples; columns: terms), and five queries over it. Exact throughout (bigint values, rationals where a query solves
// for coefficients). No gdp-wired code: the drivers beside this file (chc.ts, term.ts, tip.ts, frontier.ts) feed it
// samples and check what it answers with an outside oracle.
//
//   Q1 equalities      the affine relations Σ c·t + d = 0 every row meets (the null space of [columns | 1], over Q)
//   Q2 bounds          lo ≤ t ≤ hi for each column t (the template's inequalities: one column per direction)
//   Q3 rank            coefficients c, d with c·(pre − post) ≥ 1 on strict rows, ≥ 0 on the others, c·pre + d ≥ 0
//                      on strict rows (an exact LP, rows added as they're violated)
//   Q4 equal columns   the groups of columns equal on every row (equations between terms)
//   Q5 split           the rows split by an atom column (depth 1) or two (depth 2), Q1 and Q2 per part, kept where
//                      tighter than the parent's

// --- rationals --------------------------------------------------------------------------------------------------------
export const gcd = (a: bigint, b: bigint): bigint => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a }
export type Q = {n: bigint, d: bigint}
export const q = (n: bigint, d = 1n): Q => { if (d < 0n) { n = -n; d = -d } const g = gcd(n, d) || 1n; return {n: n / g, d: d / g} }
export const Z: Q = {n: 0n, d: 1n}, ONE: Q = {n: 1n, d: 1n}
export const add = (a: Q, b: Q): Q => (a.d === b.d ? q(a.n + b.n, a.d) : q(a.n * b.d + b.n * a.d, a.d * b.d))
export const sub = (a: Q, b: Q): Q => add(a, {n: -b.n, d: b.d})
export const mul = (a: Q, b: Q): Q => (a.n === 0n || b.n === 0n ? Z : q(a.n * b.n, a.d * b.d))
export const div = (a: Q, b: Q): Q => q(a.n * b.d, a.d * b.n)
export const cmp = (a: Q, b: Q): number => { const x = a.n * b.d - b.n * a.d; return x < 0n ? -1 : x > 0n ? 1 : 0 }
// a rational vector scaled to coprime integers
export function integral(v: Q[]): bigint[] {
  let l = 1n
  for (const x of v) l = l / gcd(l, x.d) * x.d
  const w = v.map(x => x.n * (l / x.d))
  const g = w.reduce((a, b) => gcd(a, b), 0n) || 1n
  return w.map(x => x / g)
}

// --- terms ------------------------------------------------------------------------------------------------------------
// A row is a sample: a value for each variable (booleans as 0/1). A term is evaluated on a row; `fn` calls a function
// the driver gives (a user function's values, a built-in).
export type Row = Record<string, bigint>
export type Term =
  | {k: 'var', name: string}
  | {k: 'lin', terms: [string, bigint][]}             // Σ c·x over variables
  | {k: 'mul', a: string, b: string}                  // x·y (a square when a = b)
  | {k: 'mod', a: Term, m: bigint}                    // t mod m, the remainder never negative
  | {k: 'fn', name: string, args: Term[]}
export type Fns = Record<string, (args: bigint[]) => bigint>
const emod = (a: bigint, m: bigint) => ((a % m) + m) % m
export function evalTerm(t: Term, row: Row, fns: Fns = {}): bigint {
  switch (t.k) {
    case 'var': return row[t.name]!
    case 'lin': { let s = 0n; for (const [x, c] of t.terms) s += c * row[x]!; return s }
    case 'mul': return row[t.a]! * row[t.b]!
    case 'mod': return emod(evalTerm(t.a, row, fns), t.m)
    case 'fn': return fns[t.name]!(t.args.map(a => evalTerm(a, row, fns)))
  }
}
export function showTerm(t: Term): string {
  switch (t.k) {
    case 'var': return t.name
    case 'lin': return t.terms.map(([x, c], i) => `${c < 0n ? (i ? ' - ' : '-') : i ? ' + ' : ''}${c === 1n || c === -1n ? '' : `${c < 0n ? -c : c}·`}${x}`).join('')
    case 'mul': return t.a === t.b ? `${t.a}²` : `${t.a}·${t.b}`
    case 'mod': return `(${showTerm(t.a)}) mod ${t.m}`
    case 'fn': return `${t.name}(${t.args.map(showTerm).join(', ')})`
  }
}
// SMT-LIB text of a term, each variable named by `name`
export function smtTerm(t: Term, name: (x: string) => string): string {
  const k = (c: bigint) => (c < 0n ? `(- ${-c})` : `${c}`)
  switch (t.k) {
    case 'var': return name(t.name)
    case 'lin': { const ps = t.terms.map(([x, c]) => (c === 1n ? name(x) : `(* ${k(c)} ${name(x)})`)); return ps.length === 1 ? ps[0]! : `(+ ${ps.join(' ')})` }
    case 'mul': return `(* ${name(t.a)} ${name(t.b)})`
    case 'mod': return `(mod ${smtTerm(t.a, name)} ${t.m})`
    case 'fn': return `(${t.name} ${t.args.map(a => smtTerm(a, name)).join(' ')})`
  }
}

// The grammar: variables, sums and differences of up to `upTo` of them (coefficients ±1), pairs with coefficients up
// to `coef`, products of two, remainders mod each of `mods`. Each part is skipped past its variable cap (`caps`), so
// the column count stays modest; the driver states the count it got.
export type Grammar = {upTo?: number, coef?: number, products?: boolean, mods?: bigint[], caps?: {pairs?: number, three?: number, four?: number, coefPairs?: number, products?: number, mods?: number}}
export function grammar(ints: string[], bools: string[], g: Grammar = {}): Term[] {
  const n = ints.length, caps = {pairs: 80, three: 12, four: 8, coefPairs: 12, products: 8, mods: 20, ...g.caps}, upTo = g.upTo ?? 2
  const out: Term[] = [...ints, ...bools].map(name => ({k: 'var', name}))
  const signs = (m: number): bigint[][] => (m === 0 ? [[]] : signs(m - 1).flatMap(s => [[...s, 1n], [...s, -1n]]))
  const choose = (m: number, from = 0): number[][] => (m === 0 ? [[]] : Array.from({length: n - from}, (_, i) => from + i).flatMap(i => choose(m - 1, i + 1).map(r => [i, ...r])))
  for (let m = 2; m <= upTo; m++) {
    if (n > (m === 2 ? caps.pairs : m === 3 ? caps.three : caps.four)) continue
    // the first coefficient +1 (its negation is the same column, bounds swapped)
    for (const idx of choose(m)) for (const s of signs(m - 1)) out.push({k: 'lin', terms: idx.map((i, j) => [ints[i]!, j ? s[j - 1]! : 1n])})
  }
  const coef = g.coef ?? 1
  if (coef > 1 && n <= caps.coefPairs) for (const [i, j] of choose(2) as [number, number][]) for (let a = 1; a <= coef; a++) for (let b = -coef; b <= coef; b++) {
    if (b === 0 || (Math.abs(a) === 1 && Math.abs(b) === 1) || gcd(BigInt(a), BigInt(b)) !== 1n) continue
    out.push({k: 'lin', terms: [[ints[i]!, BigInt(a)], [ints[j]!, BigInt(b)]]})
    if (a !== 1 || Math.abs(b) !== 1) out.push({k: 'lin', terms: [[ints[i]!, BigInt(b)], [ints[j]!, BigInt(a)]]})
  }
  if (g.products && n <= caps.products) for (let i = 0; i < n; i++) for (let j = i; j < n; j++) out.push({k: 'mul', a: ints[i]!, b: ints[j]!})
  if (g.mods && n <= caps.mods) for (const m of g.mods) for (const x of ints) out.push({k: 'mod', a: {k: 'var', name: x}, m})
  return out
}

// --- the table --------------------------------------------------------------------------------------------------------
export type Table = {terms: Term[], rows: number, cols: bigint[][]}
export function observe(terms: Term[], samples: Row[], fns: Fns = {}): Table {
  return {terms, rows: samples.length, cols: terms.map(t => samples.map(r => evalTerm(t, r, fns)))}
}
// the table restricted to some rows (a part of a split)
export const part = (t: Table, idx: number[]): Table => ({terms: t.terms, rows: idx.length, cols: t.cols.map(c => idx.map(i => c[i]!))})

// A relation found: Σ c·term (+ k) = 0 or ≤ 0, guarded by atoms (Q5) where it holds only on a part.
export type Lin = {coefs: [number, bigint][], k: bigint, op: '=' | '<='}
export type Atom = {col: number, op: '=' | '<=', c: bigint, neg: boolean}  // term[col] op c, or its negation
export type Rel = {guard: Atom[], rel: Lin, query: 'Q1' | 'Q2' | 'Q4' | 'Q5'}

// Q1: the affine relations every row meets, among the columns `use` (default all): the null space of [cols | 1].
// Exact, by an echelon basis of the row space built row by row (a row in the span adds nothing).
export function equalities(t: Table, use?: number[]): Lin[] {
  const cs = use ?? t.terms.map((_, i) => i), w = cs.length + 1
  const basis: {piv: number, v: Q[]}[] = []
  const seen = new Set<string>()
  for (let r = 0; r < t.rows; r++) {
    const raw = cs.map(c => t.cols[c]![r]!), key = raw.join(',')
    if (seen.has(key)) continue
    seen.add(key)
    let v: Q[] = [...raw.map(x => q(x)), ONE]
    for (const b of basis) { const f = v[b.piv]!; if (f.n !== 0n) v = v.map((x, i) => sub(x, mul(f, b.v[i]!))) }
    const piv = v.findIndex(x => x.n !== 0n)
    if (piv < 0) continue
    const inv = div(ONE, v[piv]!)
    v = v.map(x => mul(x, inv))
    for (const b of basis) { const f = b.v[piv]!; if (f.n !== 0n) b.v = b.v.map((x, i) => sub(x, mul(f, v[i]!))) }
    basis.push({piv, v})
    if (basis.length === w) break
  }
  if (!t.rows) return []
  // the null space of the row space: one vector per free column
  const pivs = new Set(basis.map(b => b.piv)), out: Lin[] = []
  for (let f = 0; f < w; f++) {
    if (pivs.has(f)) continue
    const x: Q[] = Array.from({length: w}, () => Z)
    x[f] = ONE
    for (const b of basis) x[b.piv] = q(-b.v[f]!.n, b.v[f]!.d)
    const z = integral(x)
    const coefs: [number, bigint][] = []
    for (let i = 0; i < cs.length; i++) if (z[i] !== 0n) coefs.push([cs[i]!, z[i]!])
    if (coefs.length) out.push({coefs, k: z[w - 1]!, op: '='})
  }
  return out
}

// Q2: each column's bounds over the rows (skipped where the column is constant: Q1 has it).
export function bounds(t: Table, use?: number[]): {col: number, lo: bigint, hi: bigint}[] {
  const out: {col: number, lo: bigint, hi: bigint}[] = []
  for (const c of use ?? t.terms.map((_, i) => i)) {
    const col = t.cols[c]!
    if (!col.length) continue
    let lo = col[0]!, hi = col[0]!
    for (const v of col) { if (v < lo) lo = v; if (v > hi) hi = v }
    out.push({col: c, lo, hi})
  }
  return out
}
export const boundRels = (bs: {col: number, lo: bigint, hi: bigint}[]): Lin[] => bs.flatMap((b): Lin[] => (b.lo === b.hi
  ? [{coefs: [[b.col, 1n]], k: -b.lo, op: '='}]
  : [{coefs: [[b.col, -1n]], k: b.lo, op: '<='}, {coefs: [[b.col, 1n]], k: -b.hi, op: '<='}]))

// Q4: groups of columns equal on every row (two or more each), and the columns constant on every row
export function equalColumns(t: Table, use?: number[]): number[][] {
  const groups = new Map<string, number[]>()
  for (const c of use ?? t.terms.map((_, i) => i)) { const key = t.cols[c]!.join(','); const g = groups.get(key); if (g) g.push(c); else groups.set(key, [c]) }
  return [...groups.values()].filter(g => g.length > 1)
}

// Q5: the rows split by atoms. Atom columns: each 0/1 column (b, ¬b), each column with at most `values` distinct
// values (t = c, for each c), and the given extra atoms. Depth 1: per atom, its two parts; depth 2: per pair of the
// first `depth2` atoms, the four parts. Each part's Q1 (over `eqCols`) and Q2 (over `boundCols`); a part's relation is
// kept where the parent's relations don't already state it (a bound strictly tighter, an equality of higher rank).
export function atomsOf(t: Table, cols: number[], values = 6): Atom[] {
  const out: Atom[] = []
  for (const c of cols) {
    const vs = [...new Set(t.cols[c]!)].sort((a, b) => (a < b ? -1 : a > b ? 1 : 0))
    if (vs.length < 2 || vs.length > values) continue
    if (vs.length === 2) { out.push({col: c, op: '=', c: vs[1]!, neg: false}); continue }
    for (const v of vs) out.push({col: c, op: '=', c: v, neg: false})
  }
  return out
}
// Values a column skips inside its range (at most `per` a column, the range at most `span`): the atom t = c never
// holds on a row, so ¬(t = c) does (a disequality, as a Q5 part with no row)
export function holes(t: Table, cols: number[], per = 4, span = 64n): Rel[] {
  const out: Rel[] = []
  for (const c of cols) {
    const vs = new Set(t.cols[c]!)
    if (vs.size < 2) continue
    let lo = t.cols[c]![0]!, hi = lo
    for (const v of vs) { if (v < lo) lo = v; if (v > hi) hi = v }
    if (hi - lo > span) continue
    let k = 0
    for (let v = lo + 1n; v < hi && k < per; v++) if (!vs.has(v)) { out.push({guard: [{col: c, op: '=', c: v, neg: false}], rel: {coefs: [], k: 1n, op: '<='}, query: 'Q5'}); k++ }
  }
  return out
}
export const holds = (t: Table, a: Atom, r: number): boolean => { const v = t.cols[a.col]![r]!, h = a.op === '=' ? v === a.c : v <= a.c; return a.neg ? !h : h }
const tighter = (parent: Map<number, {lo: bigint, hi: bigint}>, b: {col: number, lo: bigint, hi: bigint}): Lin[] => {
  const p = parent.get(b.col)
  if (!p) return boundRels([b])
  if (b.lo === b.hi && p.lo !== p.hi) return boundRels([b])
  const out: Lin[] = []
  if (b.lo > p.lo) out.push({coefs: [[b.col, -1n]], k: b.lo, op: '<='})
  if (b.hi < p.hi) out.push({coefs: [[b.col, 1n]], k: -b.hi, op: '<='})
  return out
}
// the equalities of `sub` that `base` doesn't span (checked on the coefficient vectors' rank)
function newEqs(base: Lin[], more: Lin[], cols: number[]): Lin[] {
  const at = new Map(cols.map((c, i) => [c, i])), width = cols.length
  const vec = (l: Lin): Q[] => { const v: Q[] = Array.from({length: width + 1}, () => Z); for (const [c, x] of l.coefs) v[at.get(c)!] = q(x); v[width] = q(l.k); return v }
  const basis: {piv: number, v: Q[]}[] = []
  const reduce = (v: Q[]) => { for (const b of basis) { const f = v[b.piv]!; if (f.n !== 0n) v = v.map((x, i) => sub_(x, mul(f, b.v[i]!))) } return v }
  const sub_ = (a: Q, b: Q) => sub(a, b)
  const addVec = (v: Q[]): boolean => {
    v = reduce(v)
    const piv = v.findIndex(x => x.n !== 0n)
    if (piv < 0) return false
    const inv = div(ONE, v[piv]!)
    v = v.map(x => mul(x, inv))
    for (const b of basis) { const f = b.v[piv]!; if (f.n !== 0n) b.v = b.v.map((x, i) => sub_(x, mul(f, v[i]!))) }
    basis.push({piv, v})
    return true
  }
  for (const l of base) addVec(vec(l))
  return more.filter(l => addVec(vec(l)))
}
export function split(t: Table, atoms: Atom[], opts: {eqCols: number[], boundCols: number[], depth2?: number, minRows?: number}): {depth1: Rel[], depth2: Rel[]} {
  const all = Array.from({length: t.rows}, (_, i) => i), minRows = opts.minRows ?? 1
  const rootEq = equalities(t, opts.eqCols), rootB = new Map(bounds(t, opts.boundCols).map(b => [b.col, b]))
  const partRels = (rows: number[], guard: Atom[], parentEq: Lin[], parentB: Map<number, {lo: bigint, hi: bigint}>, query: 'Q5'): {rels: Rel[], eq: Lin[], b: Map<number, {lo: bigint, hi: bigint}>} => {
    if (rows.length < minRows) return {rels: [], eq: parentEq, b: parentB}
    const p = part(t, rows), eq = equalities(p, opts.eqCols), bs = bounds(p, opts.boundCols)
    const rels: Rel[] = []
    for (const l of newEqs(parentEq, eq, opts.eqCols)) rels.push({guard, rel: l, query})
    for (const b of bs) for (const l of tighter(parentB, b)) rels.push({guard, rel: l, query})
    return {rels, eq: [...parentEq, ...eq], b: new Map(bs.map(b => [b.col, b]))}
  }
  const neg = (a: Atom): Atom => ({...a, neg: !a.neg})
  const akey = (a: Atom) => `${a.col}|${a.op}|${a.c}|${a.neg}`
  const depth1: Rel[] = [], depth2: Rel[] = []
  const memo = new Map<string, {eq: Lin[], b: Map<number, {lo: bigint, hi: bigint}>}>()
  for (const a of atoms) for (const lit of [a, neg(a)]) {
    const rows = all.filter(r => holds(t, lit, r))
    if (!rows.length || rows.length === t.rows) continue
    const r = partRels(rows, [lit], rootEq, rootB, 'Q5')
    depth1.push(...r.rels)
    memo.set(akey(lit), r)
  }
  const top = atoms.slice(0, opts.depth2 ?? 0)
  for (let i = 0; i < top.length; i++) for (let j = i + 1; j < top.length; j++) for (const x of [top[i]!, neg(top[i]!)]) for (const y of [top[j]!, neg(top[j]!)]) {
    if (x.col === y.col) continue
    const rows = all.filter(r => holds(t, x, r) && holds(t, y, r))
    if (!rows.length) continue
    const px = memo.get(akey(x)), py = memo.get(akey(y))
    if (!px || !py) continue
    // the parent: both depth-1 parts' relations (their bounds the tighter of the two)
    const pb = new Map(px.b)
    for (const [c, b] of py.b) { const o = pb.get(c); pb.set(c, o ? {lo: o.lo > b.lo ? o.lo : b.lo, hi: o.hi < b.hi ? o.hi : b.hi} : b) }
    depth2.push(...partRels(rows, [x, y], [...px.eq, ...py.eq], pb, 'Q5').rels)
  }
  return {depth1, depth2}
}

// --- Q3: an exact LP ----------------------------------------------------------------------------------------------------
// Minimize Σ|c_j| subject to rows a·c + a0·d ≥ b (c free, d free): a dense two-phase simplex over the rationals,
// Bland's rule. Small by design: the driver gives it a few hundred rows at most (and adds violated ones after).
export type LpRow = {a: bigint[], a0: bigint, b: bigint}
export function lp(rows: LpRow[], n: number, maxPivots = 5000): {c: Q[], d: Q} | undefined {
  // variables: c⁺ (n), c⁻ (n), d⁺, d⁻, slacks s (m), artificials (m); row: a·(c⁺ − c⁻) + a0·(d⁺ − d⁻) − s = b
  const m = rows.length, nv = 2 * n + 2 + 2 * m
  if (!m) return {c: Array.from({length: n}, () => Z), d: Z}
  const T: Q[][] = rows.map((r, i) => {
    const row: Q[] = Array.from({length: nv + 1}, () => Z), sgn = r.b < 0n ? -1n : 1n
    for (let j = 0; j < n; j++) { row[j] = q(sgn * r.a[j]!); row[n + j] = q(-sgn * r.a[j]!) }
    row[2 * n] = q(sgn * r.a0); row[2 * n + 1] = q(-sgn * r.a0)
    row[2 * n + 2 + i] = q(-sgn)
    row[2 * n + 2 + m + i] = ONE
    row[nv] = q(sgn * r.b)
    return row
  })
  const basis = rows.map((_, i) => 2 * n + 2 + m + i)
  const pivot = (r: number, c: number) => {
    const inv = div(ONE, T[r]![c]!)
    T[r] = T[r]!.map(x => mul(x, inv))
    for (let i = 0; i < m; i++) { if (i === r) continue; const f = T[i]![c]!; if (f.n !== 0n) T[i] = T[i]!.map((x, j) => sub(x, mul(f, T[r]![j]!))) }
    basis[r] = c
  }
  const run = (cost: Q[], allowed: (j: number) => boolean): boolean => {
    for (let it = 0; it < maxPivots; it++) {
      // reduced costs: cost_j − Σ cost_basis · T[i][j]
      let enter = -1
      for (let j = 0; j < nv && enter < 0; j++) {
        if (!allowed(j) || basis.includes(j)) continue
        let rc = cost[j]!
        for (let i = 0; i < m; i++) { const cb = cost[basis[i]!]!; if (cb.n !== 0n && T[i]![j]!.n !== 0n) rc = sub(rc, mul(cb, T[i]![j]!)) }
        if (rc.n < 0n) enter = j
      }
      if (enter < 0) return true
      let leave = -1, best: Q | undefined
      for (let i = 0; i < m; i++) {
        const a = T[i]![enter]!
        if (a.n <= 0n) continue
        const ratio = div(T[i]![nv]!, a)
        if (!best || cmp(ratio, best) < 0 || (cmp(ratio, best) === 0 && basis[i]! < basis[leave]!)) { best = ratio; leave = i }
      }
      if (leave < 0) return false  // unbounded
      pivot(leave, enter)
    }
    return false
  }
  // phase 1: minimize the artificials
  const c1: Q[] = Array.from({length: nv}, (_, j) => (j >= 2 * n + 2 + m ? ONE : Z))
  if (!run(c1, () => true)) return undefined
  let infeas = Z
  for (let i = 0; i < m; i++) if (basis[i]! >= 2 * n + 2 + m) infeas = add(infeas, T[i]![nv]!)
  if (infeas.n !== 0n) return undefined
  // drive artificials out of the basis where they sit at 0
  for (let i = 0; i < m; i++) if (basis[i]! >= 2 * n + 2 + m) { const j = T[i]!.findIndex((x, j) => j < 2 * n + 2 + m && x.n !== 0n); if (j >= 0) pivot(i, j) }
  // phase 2: minimize Σ (c⁺ + c⁻), the artificials out
  const c2: Q[] = Array.from({length: nv}, (_, j) => (j < 2 * n ? ONE : Z))
  run(c2, j => j < 2 * n + 2 + m)
  const val = (j: number): Q => { const i = basis.indexOf(j); return i < 0 ? Z : T[i]![nv]! }
  return {c: Array.from({length: n}, (_, j) => sub(val(j), val(n + j))), d: sub(val(2 * n), val(2 * n + 1))}
}

// Difference constraints over L variables plus a zero node: rows with one +1 and one −1 (d_f − d_t ≥ b) or one +1
// (d_f ≥ b). Returns integer values (the zero node at 0), or none where they conflict.
export function differences(rows: LpRow[], L: number): bigint[] | undefined {
  // x_f − x_t ≥ b  ⇔  x_t ≤ x_f − b: an edge f → t of weight −b; node L is zero
  const edges: [number, number, bigint][] = []
  for (const r of rows) {
    const pos = r.a.findIndex(x => x === 1n), neg = r.a.findIndex(x => x === -1n)
    if (r.a.some(x => x !== 0n && x !== 1n && x !== -1n) || pos < 0) return undefined
    edges.push([pos, neg < 0 ? L : neg, -r.b])
  }
  // x_f ≥ b with no t: x_L ≤ x_f − b, the edge f → L
  const dist: bigint[] = Array.from({length: L + 1}, () => 0n)
  for (let it = 0; it <= L + 1; it++) {
    let changed = false
    for (const [f, t, w] of edges) if (dist[f]! + w < dist[t]!) { dist[t] = dist[f]! + w; changed = true }
    if (!changed) return dist.slice(0, L).map(x => x - dist[L]!)
  }
  return undefined
}

// Q3: a linear rank over the columns `cols` from transition rows (pre, post), one per location: rows of `strict`
// transitions drop by 1 and are ≥ 0 before; rows of `weak` ones don't rise. Constraint generation: an LP over at most
// `cap` rows, the violated rows added and solved again. Returns integer coefficients per location (scaled), or none.
export type Pair = {from: string, to: string, pre: bigint[], post: bigint[]}
export type Ranking = {coefs: Map<string, bigint[]>, k: Map<string, bigint>, scale: bigint}
export const rank = (strict: Pair[], weak: Pair[], locs: string[], n: number, cap = 120): Ranking | undefined => ranks(strict, weak, locs, n, 1, cap)[0]
// every rank that fits, best first: the box's (at most `keep`, by cost), then the exact LP's
export function ranks(strict: Pair[], weak: Pair[], locs: string[], n: number, keep = 12, cap = 120): Ranking[] {
  // variables: per location, n coefficients and a constant: r_l(x) = c_l·x + d_l
  const L = locs.length, N = L * (n + 1), li = new Map(locs.map((l, i) => [l, i]))
  const rowsOf = (p: Pair, isStrict: boolean): LpRow[] => {
    const a: bigint[] = Array.from({length: N}, () => 0n), f = li.get(p.from)! * (n + 1), t = li.get(p.to)! * (n + 1)
    // r_from(pre) − r_to(post) ≥ (strict ? 1 : 0)
    for (let j = 0; j < n; j++) { a[f + j]! += p.pre[j]!; a[t + j]! -= p.post[j]! }
    a[f + n]! += 1n; a[t + n]! -= 1n
    const out: LpRow[] = [{a, a0: 0n, b: isStrict ? 1n : 0n}]
    if (isStrict) { const g: bigint[] = Array.from({length: N}, () => 0n); for (let j = 0; j < n; j++) g[f + j] = p.pre[j]!; g[f + n] = 1n; out.push({a: g, a0: 0n, b: 0n}) }
    return out
  }
  const dedupe = (rs: LpRow[]) => { const m = new Map<string, LpRow>(); for (const r of rs) m.set(`${r.a.join(',')}|${r.b}`, r); return [...m.values()] }
  const all = dedupe([...strict.flatMap(p => rowsOf(p, true)), ...weak.flatMap(p => rowsOf(p, false))])
  if (!all.length) return []
  const result = (c: bigint[]) => {
    const coefs = new Map<string, bigint[]>(), k = new Map<string, bigint>()
    for (const [l, i] of li) { coefs.set(l, c.slice(i * (n + 1), i * (n + 1) + n)); k.set(l, c[i * (n + 1) + n]!) }
    return {coefs, k, scale: 1n}
  }
  // first, small integer coefficients (±1, then ±2), fewest terms first (the box findRank tries first), the constants
  // then solved for (directly at one location, an LP over the constants at several)
  const cpos = Array.from({length: N}, (_, j) => j).filter(j => j % (n + 1) !== n), dpos = locs.map((_, i) => i * (n + 1) + n)
  // every candidate that fits is kept, the fewest terms first, then the smallest constants; the caller checks them in
  // that order (a constant fitted to the samples' size, −x + 143, is refused, and n − x comes next)
  let tried = 0
  const best: {c: bigint[], cost: bigint}[] = []
  const absb = (x: bigint) => (x < 0n ? -x : x)
  const offer = (c: bigint[], size: number) => { const cost = BigInt(size) * (1n << 50n) + dpos.reduce((a, j) => a + absb(c[j]!), 0n); best.push({c: [...c], cost}) }
  // the box: up to 4 terms where there are at most 12 coefficients, 3 up to 20, else 2; ±2 only up to 8
  const maxSize = cpos.length <= 12 ? 4 : cpos.length <= 20 ? 3 : 2
  for (const mag of cpos.length <= 8 ? [1n, 2n] : [1n]) for (let size = 1; size <= Math.min(maxSize, cpos.length); size++) {
    const pick = (from: number, left: number, acc: number[]): number[][] => (left === 0 ? [acc] : cpos.slice(from).flatMap((_, i) => pick(from + i + 1, left - 1, [...acc, cpos[from + i]!])))
    for (const sup of pick(0, size, [])) {
      const vals = mag === 1n ? [1n, -1n] : [2n, -2n, 1n, -1n]
      const combos = sup.reduce((acc: bigint[][]) => acc.flatMap(a => vals.map(v => [...a, v])), [[]])
      for (const cv of combos) {
        if (mag === 2n && !cv.some(v => v === 2n || v === -2n)) continue
        if (++tried > 20000) break
        const c: bigint[] = Array.from({length: N}, () => 0n)
        sup.forEach((j, i) => { c[j] = cv[i]! })
        const need: LpRow[] = []
        let bad = false
        for (const r of all) {
          let v = 0n
          for (const j of sup) v += r.a[j]! * c[j]!
          const da = dpos.map(j => r.a[j]!)
          if (da.every(x => x === 0n)) { if (v < r.b) { bad = true; break } continue }
          need.push({a: da, a0: 0n, b: r.b - v})
        }
        if (bad) continue
        if (L === 1) { let d = -(1n << 62n); for (const r of need) { const x = r.b / r.a[0]!; const lo = r.a[0]! > 0n ? (r.b % r.a[0]! === 0n ? x : x + (r.b > 0n ? 1n : 0n)) : undefined; if (lo === undefined) { bad = true; break } if (lo > d) d = lo } if (bad) continue; c[dpos[0]!] = need.length ? d : 0n; offer(c, size); continue }
        // several locations: the constants by difference constraints (d_f − d_t ≥ w, d_f ≥ w against a zero node),
        // Bellman–Ford from 0 everywhere; a negative cycle means none
        const ds = differences(need, L)
        if (!ds) continue
        ds.forEach((x, i) => { c[dpos[i]!] = x })
        offer(c, size)
      }
    }
  }
  best.sort((a, b) => (a.cost < b.cost ? -1 : a.cost > b.cost ? 1 : 0))
  const found = best.slice(0, keep).map(b => result(b.c))
  if (found.length) return found
  // then (none in the box) the exact LP: its first rows spread over the list, then the violated ones
  let use = all.length <= cap ? all : all.filter((_, i) => i % Math.ceil(all.length / cap) === 0)
  for (let round = 0; round < 6; round++) {
    const sol = lp(use, N)
    if (!sol) return found
    // the rational solution checked on every row; then scaled to coprime integers (a positive multiple)
    const val = (r: LpRow) => r.a.reduce((acc, x, j) => (x === 0n ? acc : add(acc, mul(q(x), sol.c[j]!))), Z)
    const bad = all.filter(r => cmp(val(r), q(r.b)) < 0)
    if (!bad.length) return [...found, result(integral(sol.c))]
    use = dedupe([...use, ...bad.slice(0, 40)])
  }
  return found
}
