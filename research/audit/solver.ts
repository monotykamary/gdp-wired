// The solver inside the library: linear arithmetic over the naturals, decided by Fourier–Motzkin elimination, with a
// certificate for every proof. Enumeration splits a law into cases (the step's branches, min's two sides), and each
// case is one conjunction of linear constraints, which elimination refutes or finds satisfiable.
//
// A refutation is a Farkas certificate: nonnegative multipliers, one per input constraint, whose weighted sum has every
// variable's coefficient 0 and a positive constant, i.e. the constraints add up to "positive <= 0". Checking one is a
// dot product (check.ts), so the solver is untrusted and the trusted part is a few lines.
//
// Over the integers, a strict a < b is entered as a − b + 1 <= 0, which is exact for integers. Elimination itself is
// complete over the rationals; when it finds a case satisfiable, a small search looks for an integer counterexample.

export type Lin = Record<string, number> // variable -> coefficient, and '1' -> the constant
export type Constraint = {lin: Lin, label: string} // lin <= 0

export const v = (name: string): Lin => ({[name]: 1})
export const k = (value: number): Lin => ({1: value})
export function add(...xs: Lin[]): Lin {
  const out: Lin = {}
  for (const x of xs) for (const [key, value] of Object.entries(x)) out[key] = (out[key] ?? 0) + value
  for (const key of Object.keys(out)) if (out[key] === 0) delete out[key]
  return out
}
export const scale = (x: Lin, factor: number): Lin => Object.fromEntries(Object.entries(x).map(([key, value]) => [key, value * factor]))
export const sub = (a: Lin, b: Lin) => add(a, scale(b, -1))

export const le = (a: Lin, b: Lin, label = ''): Constraint[] => [{lin: sub(a, b), label: label || `${show(a)} <= ${show(b)}`}]
export const lt = (a: Lin, b: Lin, label = ''): Constraint[] => [{lin: add(sub(a, b), k(1)), label: label || `${show(a)} < ${show(b)}`}]
export const eq = (a: Lin, b: Lin, label = ''): Constraint[] => [...le(a, b, label || `${show(a)} = ${show(b)}`), ...le(b, a, label || `${show(a)} = ${show(b)}`)]
export const nat = (...names: string[]): Constraint[] => names.flatMap(name => le(k(0), v(name), `${name} >= 0`))

export function show(x: Lin): string {
  const parts = Object.entries(x).filter(([key]) => key !== '1').map(([key, value]) => (value === 1 ? key : value === -1 ? `-${key}` : `${value}${key}`))
  if ((x['1'] ?? 0) !== 0 || parts.length === 0) parts.push(String(x['1'] ?? 0))
  return parts.join(' + ').replace(/\+ -/g, '- ')
}

type Row = {lin: Lin, from: number[]} // from: multipliers of the input constraints

export type Verdict =
  | {kind: 'refuted', certificate: number[]} // the case is impossible
  | {kind: 'satisfiable'} // over the rationals; see counterexample()

export function refute(constraints: Constraint[]): Verdict {
  let rows: Row[] = constraints.map((c, index) => ({lin: c.lin, from: constraints.map((_, j) => (j === index ? 1 : 0))}))
  const variables = [...new Set(constraints.flatMap(c => Object.keys(c.lin).filter(key => key !== '1')))]
  for (const x of variables) {
    const pos = rows.filter(r => (r.lin[x] ?? 0) > 0), neg = rows.filter(r => (r.lin[x] ?? 0) < 0)
    const rest = rows.filter(r => (r.lin[x] ?? 0) === 0)
    for (const p of pos) for (const n of neg) {
      const a = p.lin[x]!, b = -n.lin[x]!
      rest.push({lin: add(scale(p.lin, b), scale(n.lin, a)), from: p.from.map((value, j) => value * b + n.from[j]! * a)})
    }
    rows = rest
    const contradiction = rows.find(r => Object.keys(r.lin).every(key => key === '1') && (r.lin['1'] ?? 0) > 0)
    if (contradiction) return {kind: 'refuted', certificate: contradiction.from}
  }
  const contradiction = rows.find(r => (r.lin['1'] ?? 0) > 0)
  return contradiction ? {kind: 'refuted', certificate: contradiction.from} : {kind: 'satisfiable'}
}

// An integer point within 0..bound that satisfies every constraint, if there is one.
export function counterexample(constraints: Constraint[], bound = 6): Record<string, number> | undefined {
  const variables = [...new Set(constraints.flatMap(c => Object.keys(c.lin).filter(key => key !== '1')))]
  const point: Record<string, number> = {}
  const holds = () => constraints.every(c => Object.entries(c.lin).reduce((sum, [key, value]) => sum + value * (key === '1' ? 1 : point[key]!), 0) <= 0)
  const search = (index: number): boolean => {
    if (index === variables.length) return holds()
    for (let value = 0; value <= bound; value++) {
      point[variables[index]!] = value
      if (search(index + 1)) return true
    }
    return false
  }
  return search(0) ? {...point} : undefined
}
