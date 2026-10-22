// Linear arithmetic over the integers, inside the library. A conjunction of constraints `lin <= 0` is decided by
// Fourier–Motzkin elimination with integer cuts, and every answer carries evidence that a small checker verifies:
//   refuted  a derivation: input rows, positive combinations of two rows, and cuts (divide a row's variable
//            coefficients by their common divisor g and round the constant up), ending in `positive <= 0`
//   sat      an integer witness, checked by evaluating every input constraint at it
//   unknown  elimination was inexact for the integers and no witness was found (never a wrong answer)
// Elimination of x is exact for the integers when every pair it combines has a coefficient ±1 on x (the Omega test's
// exact shadow). Then a rational solution of the rest extends to an integer x, so back-substitution finds a witness.

export type Lin = Record<string, number> // variable -> coefficient, '1' -> constant
// lin <= 0. `src`: where a leaf's row comes from (the path's i-th atom, a hypothesis's facts, a column's naturality, a pair
// of equal cells, a term column's rows), a hint for Lean's check, which looks there first.
export type Constraint = {lin: Lin, label: string, src?: RowSrc}
export type RowSrc = {atom: number} | {fact: number} | {nat: string} | {pair: [string, string]} | {term: string}

export const v = (name: string): Lin => ({[name]: 1})
export const k = (value: number): Lin => (value === 0 ? {} : {1: value})
// (Plain loops, no intermediate arrays: these run millions of times in a proof. Each keeps the keys in the order they
// first appear, as a sum over the entries would.)
export function add(...xs: Lin[]): Lin {
  const out: Lin = {}
  for (const x of xs) for (const key in x) out[key] = (out[key] ?? 0) + x[key]!
  for (const key in out) if (out[key] === 0) delete out[key]
  return out
}
export const scale = (x: Lin, f: number): Lin => {
  const out: Lin = {}
  for (const key in x) { const value = x[key]! * f; if (value !== 0) out[key] = value }
  return out
}
export const sub = (a: Lin, b: Lin): Lin => {
  const out: Lin = {}
  for (const key in a) out[key] = a[key]!
  for (const key in b) out[key] = (out[key] ?? 0) - b[key]!
  for (const key in out) if (out[key] === 0) delete out[key]
  return out
}
export function show(x: Lin): string {
  const parts = Object.entries(x).filter(([key]) => key !== '1').map(([key, c]) => (c === 1 ? key : c === -1 ? `-${key}` : `${c}${key}`))
  if ((x['1'] ?? 0) !== 0 || parts.length === 0) parts.push(String(x['1'] ?? 0))
  return parts.join(' + ').replace(/\+ -/g, '- ')
}
export const le = (a: Lin, b: Lin, label?: string): Constraint[] => [{lin: sub(a, b), label: label ?? `${show(a)} <= ${show(b)}`}]
export const lt = (a: Lin, b: Lin, label?: string): Constraint[] => [{lin: add(sub(a, b), k(1)), label: label ?? `${show(a)} < ${show(b)}`}]
export const eq = (a: Lin, b: Lin, label?: string): Constraint[] => [...le(a, b, label ?? `${show(a)} = ${show(b)}`), ...le(b, a, label ?? `${show(a)} = ${show(b)}`)]
export const nat = (...names: string[]): Constraint[] => names.flatMap(name => le(k(0), v(name), `${name} >= 0`))
// not (lin <= 0) over the integers is lin >= 1, i.e. 1 − lin <= 0.
export const negate = (c: Constraint): Constraint => ({lin: add(k(1), scale(c.lin, -1)), label: `not (${c.label})`})

export type Step =
  | {kind: 'input', index: number}
  | {kind: 'combine', a: number, b: number, ma: number, mb: number}
  | {kind: 'cut', of: number, g: number}
export type Verdict =
  | {kind: 'refuted', steps: Step[]}
  | {kind: 'sat', witness: Record<string, number>}
  | {kind: 'unknown', point?: Record<string, number>} // point: a rational solution, a hint for where to split

const gcd = (a: number, b: number): number => (b === 0 ? Math.abs(a) : gcd(b, a % b))
const vars = (lin: Lin) => Object.keys(lin).filter(key => key !== '1')

// maxRows: elimination can square the rows each round; past this many live rows, or a round that would make more than
// five times as many before merging them, it gives up with `unknown`.
// The rows the solver has read and made, which a counted search reads as its clock (kernel/prove.ts's `counted`).
export const work = {n: 0}
export function solve(constraints: Constraint[], maxRows = 20_000): Verdict {
  work.n += constraints.length
  const steps: Step[] = []
  const lins: Lin[] = []
  const push = (step: Step, lin: Lin) => (steps.push(step), lins.push(lin), lins.length - 1)
  // A row after its cut, if its variables share a divisor.
  const tighten = (index: number) => {
    const lin = lins[index]!
    let g = 0
    for (const key in lin) if (key !== '1') { g = gcd(g, lin[key]!); if (g === 1) return index }
    if (g <= 1) return index
    const cut: Lin = {}
    for (const key in lin) if (key !== '1') cut[key] = lin[key]! / g
    const constant = Math.ceil((lin['1'] ?? 0) / g)
    return push({kind: 'cut', of: index, g}, add(cut, k(constant)))
  }
  let rows = constraints.map((c, index) => tighten(push({kind: 'input', index}, c.lin)))
  // A row with no variable and a positive constant (kept per row: a row never changes once pushed).
  const contra: boolean[] = []
  const isContra = (r: number) => (contra[r] ??= (lins[r]!['1'] ?? 0) > 0 && Object.keys(lins[r]!).every(key => key === '1'))
  const contradiction = () => rows.find(isContra)
  const eliminated: {x: string, rows: number[]}[] = []
  let exact = true
  // Equalities first: a pair of rows that are each other's negation, with a variable of coefficient ±1, defines that
  // variable. Substituting it into every other row (a combination with one row of the pair) eliminates it exactly,
  // with |rows| new rows instead of the |pos| × |neg| of a plain elimination.
  // A row's key and its negation's, kept per row (a row never changes once pushed).
  const keyOf = (lin: Lin) => JSON.stringify(Object.entries(lin).sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0)))
  const keys: string[] = [], negKeys: string[] = []
  const key = (r: number) => (keys[r] ??= keyOf(lins[r]!)), negKey = (r: number) => (negKeys[r] ??= keyOf(scale(lins[r]!, -1)))
  for (let changed = true; changed && contradiction() === undefined;) {
    changed = false
    const byKey = new Map(rows.map(r => [key(r), r]))
    for (const r of rows) {
      const neg = byKey.get(negKey(r))
      if (neg === undefined || neg === r) continue
      let x: string | undefined
      for (const name in lins[r]!) if (name !== '1' && Math.abs(lins[r]![name]!) === 1) { x = name; break }
      if (x === undefined) continue
      // up: the row of the pair with +x, down: with −x.
      const [up, down] = lins[r]![x] === 1 ? [r, neg] : [neg, r]
      const next: number[] = []
      for (const o of rows) {
        if (o === up || o === down) continue
        const c = lins[o]![x] ?? 0
        if (c === 0) next.push(o)
        else next.push(tighten(push({kind: 'combine', a: o, b: c > 0 ? down : up, ma: 1, mb: Math.abs(c)}, add(lins[o]!, scale(lins[c > 0 ? down : up]!, Math.abs(c))))))
      }
      eliminated.push({x, rows: [up, down]})
      rows = next
      changed = true
      break
    }
  }
  const sigs: string[] = []
  const sigOf = (r: number) => {
    let sig = sigs[r]
    if (sig === undefined) {
      const lin = lins[r]!, keys: string[] = []
      for (const key in lin) if (key !== '1') keys.push(key)
      keys.sort()
      sig = JSON.stringify(keys.map(key => [key, lin[key]]))
      sigs[r] = sig
    }
    return sig
  }
  for (let found = contradiction(); found === undefined; found = contradiction()) {
    // Each variable's rows by sign, in one pass (variables in the order they first appear).
    const index = new Map<string, {pos: number[], neg: number[], posUnit: boolean, negUnit: boolean}>()
    for (const r of rows) for (const x in lins[r]!) {
      if (x === '1') continue
      const c = lins[r]![x]!
      let e = index.get(x)
      if (!e) index.set(x, (e = {pos: [], neg: [], posUnit: true, negUnit: true}))
      if (c > 0) { e.pos.push(r); e.posUnit &&= c === 1 } else if (c < 0) { e.neg.push(r); e.negUnit &&= c === -1 }
    }
    if (index.size === 0) break
    // Eliminate the variable that makes the fewest new rows, preferring exact eliminations (the first such).
    let choice: {x: string, pos: number[], neg: number[], isExact: boolean, size: number} | undefined
    for (const [x, e] of index) {
      const c = {x, pos: e.pos, neg: e.neg, isExact: e.posUnit || e.negUnit, size: e.pos.length * e.neg.length - e.pos.length - e.neg.length}
      if (!choice || (c.isExact && !choice.isExact) || (c.isExact === choice.isExact && c.size < choice.size)) choice = c
    }
    if (!choice) break
    if (choice.pos.length * choice.neg.length > 5 * maxRows) return {kind: 'unknown'}
    work.n += choice.pos.length * choice.neg.length
    exact &&= choice.isExact
    eliminated.push({x: choice.x, rows: [...choice.pos, ...choice.neg]})
    const next = rows.filter(r => (lins[r]![choice.x] ?? 0) === 0)
    for (const p of choice.pos) for (const n of choice.neg) {
      const a = lins[p]![choice.x]!, b = -lins[n]![choice.x]!
      const combined = push({kind: 'combine', a: p, b: n, ma: b / gcd(a, b), mb: a / gcd(a, b)}, add(scale(lins[p]!, b / gcd(a, b)), scale(lins[n]!, a / gcd(a, b))))
      next.push(tighten(combined))
    }
    // Rows with the same variable part: only the tightest (largest constant) matters; rows with no variables that hold
    // say nothing.
    const best = new Map<string, number>()
    for (const r of next) {
      const lin = lins[r]!, sig = sigOf(r)
      if (sig === '[]' && (lin['1'] ?? 0) <= 0) continue
      const seen = best.get(sig)
      if (seen === undefined || (lins[seen]!['1'] ?? 0) < (lin['1'] ?? 0)) best.set(sig, r)
    }
    rows = [...best.values()]
    if (rows.length > maxRows) return {kind: 'unknown'}
  }
  const found = contradiction()
  if (found !== undefined) return {kind: 'refuted', steps: prune(steps, found)}
  // A rational solution the same way (cuts only remove non-integer points, so bounds never cross): where to split.
  const rational: Record<string, number> = {}
  for (const {x, rows: bounds} of [...eliminated].reverse()) {
    let lower = Number.NEGATIVE_INFINITY, upper = Number.POSITIVE_INFINITY
    for (const r of bounds) {
      const lin = lins[r]!, a = lin[x]!
      const rest = Object.entries(lin).reduce((sum, [key, c]) => (key === x ? sum : sum + c * (key === '1' ? 1 : (rational[key] ?? 0))), 0)
      if (a > 0) upper = Math.min(upper, -rest / a)
      else lower = Math.max(lower, -rest / a)
    }
    rational[x] = lower === Number.NEGATIVE_INFINITY ? Math.min(0, upper) : lower
  }
  // Back-substitution, last eliminated first: each variable takes the least integer its bounds allow.
  const point: Record<string, number> = {}
  for (const {x, rows: bounds} of eliminated.reverse()) {
    let lower = Number.NEGATIVE_INFINITY, upper = Number.POSITIVE_INFINITY
    for (const r of bounds) {
      const lin = lins[r]!, a = lin[x]!
      const rest = Object.entries(lin).reduce((sum, [key, c]) => (key === x ? sum : sum + c * (key === '1' ? 1 : (point[key] ?? 0))), 0)
      if (a > 0) upper = Math.min(upper, Math.floor(-rest / a))
      else lower = Math.max(lower, Math.ceil(-rest / a))
    }
    point[x] = lower === Number.NEGATIVE_INFINITY ? Math.min(0, upper) : lower
  }
  for (const c of constraints) for (const key of vars(c.lin)) point[key] ??= 0
  const holds = constraints.every(c => Object.entries(c.lin).reduce((sum, [key, a]) => sum + a * (key === '1' ? 1 : point[key]!), 0) <= 0)
  // An exact elimination always back-substitutes to a witness; anything else is reported as unknown, never as sat.
  void exact
  return holds ? {kind: 'sat', witness: point} : {kind: 'unknown', point: rational}
}

// Only the steps the contradiction depends on, renumbered.
function prune(steps: Step[], last: number): Step[] {
  const keep = new Set<number>()
  const visit = (i: number) => {
    if (keep.has(i)) return
    keep.add(i)
    const s = steps[i]!
    if (s.kind === 'combine') (visit(s.a), visit(s.b))
    if (s.kind === 'cut') visit(s.of)
  }
  visit(last)
  const order = [...keep].sort((a, b) => a - b)
  const at = new Map(order.map((old, i) => [old, i]))
  return order.map(i => {
    const s = steps[i]!
    return s.kind === 'combine' ? {...s, a: at.get(s.a)!, b: at.get(s.b)!} : s.kind === 'cut' ? {...s, of: at.get(s.of)!} : s
  })
}

// A refutation found fast, where there is one over the rationals: Farkas' lemma says rows a·x + c <= 0 (x free) have no
// rational solution exactly when some λ >= 0 has Σ λ·a = 0 and Σ λ·c > 0. A floating-point simplex looks for such λ
// (phase one on Σ λ·a = 0, Σ λ·c = 1), and elimination on the rows it uses alone (usually a handful) gives the
// derivation, renumbered to the whole system's rows. Floating point only picks the rows: the derivation is exact, and
// the checker sees nothing else. Undefined when no λ turns up (a system with a rational solution, or one the floats
// misjudge): the caller goes on as without it.
export function refuteFast(constraints: Constraint[], maxRows = 2_000): Verdict | undefined {
  const m = constraints.length
  if (m === 0) return undefined
  const names = [...new Set(constraints.flatMap(c => vars(c.lin)))], n = names.length
  if (m > maxRows || n > maxRows) return undefined
  // Tableau rows: one per variable (Σ λ_i a_ij = 0) and the normalization (Σ λ_i c_i = 1); columns: the m λs, then one
  // artificial per row, then the right-hand side.
  const R = n + 1, cols = m + R
  const T: Float64Array[] = Array.from({length: R}, () => new Float64Array(cols + 1))
  const col = new Map(names.map((x, j) => [x, j]))
  constraints.forEach((c, i) => {
    for (const [key, a] of Object.entries(c.lin)) { if (key === '1') T[n]![i] = a; else T[col.get(key)!]![i] = a }
  })
  T[n]![cols] = 1
  for (let r = 0; r < R; r++) T[r]![m + r] = 1
  const basis = Array.from({length: R}, (_, r) => m + r)
  // Phase one: minimize the artificials' sum, as the reduced costs of the objective row.
  const z = new Float64Array(cols + 1)
  for (let r = 0; r < R; r++) for (let j = 0; j <= cols; j++) if (j < m || j === cols) z[j]! -= T[r]![j]!
  const eps = 1e-9
  for (let iter = 0; iter < 50 * (R + m); iter++) {
    work.n += 1 + ((R * cols) >> 8)
    // Bland's rule: the first column with a negative reduced cost enters (no cycling on degenerate systems).
    let enter = -1
    for (let j = 0; j < cols; j++) if (z[j]! < -eps) { enter = j; break }
    if (enter < 0) break
    let leave = -1, best = Infinity
    for (let r = 0; r < R; r++) {
      const a = T[r]![enter]!
      if (a > eps) { const ratio = T[r]![cols]! / a; if (ratio < best - eps || (Math.abs(ratio - best) <= eps && basis[r]! < basis[leave]!)) { best = ratio; leave = r } }
    }
    if (leave < 0) return undefined // unbounded: cannot happen in phase one; give up rather than guess
    const p = T[leave]!, pv = p[enter]!
    for (let j = 0; j <= cols; j++) p[j]! /= pv
    for (let r = 0; r < R; r++) if (r !== leave) { const f = T[r]![enter]!; if (f !== 0) { const row = T[r]!; for (let j = 0; j <= cols; j++) row[j]! -= f * p[j]! } }
    const f = z[enter]!
    if (f !== 0) for (let j = 0; j <= cols; j++) z[j]! -= f * p[j]!
    basis[leave] = enter
  }
  if (-z[cols]! > 1e-7) return undefined // the artificials can't all leave: no λ, so a rational solution exists
  const support: number[] = []
  for (let r = 0; r < R; r++) if (basis[r]! < m && T[r]![cols]! > eps) support.push(basis[r]!)
  if (!support.length) return undefined
  const sub = solve(support.sort((a, b) => a - b).map(i => constraints[i]!))
  if (sub.kind !== 'refuted') return undefined
  return {kind: 'refuted', steps: sub.steps.map(st => (st.kind === 'input' ? {...st, index: support[st.index]!} : st))}
}
