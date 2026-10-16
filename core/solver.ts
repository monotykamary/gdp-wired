// Linear arithmetic over the integers, inside the library. A conjunction of constraints `lin <= 0` is decided by
// Fourier–Motzkin elimination with integer cuts, and every answer carries evidence that a small checker verifies:
//   refuted  a derivation: input rows, positive combinations of two rows, and cuts (divide a row's variable
//            coefficients by their common divisor g and round the constant up), ending in `positive <= 0`
//   sat      an integer witness, checked by evaluating every input constraint at it
//   unknown  elimination was inexact for the integers and no witness was found (never a wrong answer)
// Elimination of x is exact for the integers when every pair it combines has a coefficient ±1 on x (the Omega test's
// exact shadow). Then a rational solution of the rest extends to an integer x, so back-substitution finds a witness.

export type Lin = Record<string, number> // variable -> coefficient, '1' -> constant
export type Constraint = {lin: Lin, label: string} // lin <= 0

export const v = (name: string): Lin => ({[name]: 1})
export const k = (value: number): Lin => (value === 0 ? {} : {1: value})
export function add(...xs: Lin[]): Lin {
  const out: Lin = {}
  for (const x of xs) for (const [key, value] of Object.entries(x)) out[key] = (out[key] ?? 0) + value
  for (const key of Object.keys(out)) if (out[key] === 0) delete out[key]
  return out
}
export const scale = (x: Lin, f: number): Lin => add(Object.fromEntries(Object.entries(x).map(([key, value]) => [key, value * f])))
export const sub = (a: Lin, b: Lin) => add(a, scale(b, -1))
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

// maxRows: elimination can square the rows each round; past this many live rows it gives up with `unknown`.
export function solve(constraints: Constraint[], maxRows = 20_000): Verdict {
  const steps: Step[] = []
  const lins: Lin[] = []
  const push = (step: Step, lin: Lin) => (steps.push(step), lins.push(lin), lins.length - 1)
  // A row after its cut, if its variables share a divisor.
  const tighten = (index: number) => {
    const lin = lins[index]!
    const g = vars(lin).reduce((acc, key) => gcd(acc, lin[key]!), 0)
    if (g <= 1) return index
    const cut: Lin = Object.fromEntries(vars(lin).map(key => [key, lin[key]! / g]))
    const constant = Math.ceil((lin['1'] ?? 0) / g)
    return push({kind: 'cut', of: index, g}, add(cut, k(constant)))
  }
  let rows = constraints.map((c, index) => tighten(push({kind: 'input', index}, c.lin)))
  const contradiction = () => rows.find(r => vars(lins[r]!).length === 0 && (lins[r]!['1'] ?? 0) > 0)
  const eliminated: {x: string, rows: number[]}[] = []
  let exact = true
  // Equalities first: a pair of rows that are each other's negation, with a variable of coefficient ±1, defines that
  // variable. Substituting it into every other row (a combination with one row of the pair) eliminates it exactly,
  // with |rows| new rows instead of the |pos| × |neg| of a plain elimination.
  for (let changed = true; changed && contradiction() === undefined;) {
    changed = false
    const key = (lin: Lin) => JSON.stringify(Object.entries(lin).sort())
    const byKey = new Map(rows.map(r => [key(lins[r]!), r]))
    for (const r of rows) {
      const neg = byKey.get(key(scale(lins[r]!, -1)))
      if (neg === undefined || neg === r) continue
      const x = vars(lins[r]!).find(name => Math.abs(lins[r]![name]!) === 1)
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
  for (let found = contradiction(); found === undefined; found = contradiction()) {
    const remaining = [...new Set(rows.flatMap(r => vars(lins[r]!)))]
    if (remaining.length === 0) break
    // Eliminate the variable that makes the fewest new rows, preferring exact eliminations.
    const cost = (x: string) => {
      const pos = rows.filter(r => (lins[r]![x] ?? 0) > 0), neg = rows.filter(r => (lins[r]![x] ?? 0) < 0)
      const isExact = pos.every(p => lins[p]![x] === 1) || neg.every(n => lins[n]![x] === -1)
      return {x, pos, neg, isExact, size: pos.length * neg.length - pos.length - neg.length}
    }
    const choice = remaining.map(cost).sort((a, b) => Number(b.isExact) - Number(a.isExact) || a.size - b.size)[0]!
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
      const lin = lins[r]!, sig = JSON.stringify(vars(lin).sort().map(key => [key, lin[key]]))
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
