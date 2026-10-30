// The trusted part, in TypeScript (bendtt-style twin: check.lean is the same checker with its soundness proof).
// A derivation refutes its constraints when every step replays: an input is that constraint, a combination adds two
// earlier rows with positive integer multipliers (strict when either row is), a cut divides every variable coefficient
// of an earlier row by g > 0 (each must be divisible) and rounds the constant up, and the last row has no variable and
// a positive constant, or (over the rationals) a constant >= 0 and is strict (0 < 0 is false).
// One check for both domains: over the rationals (`integral` false: Rationals.lean's checkQ) a derivation is a Farkas
// certificate with strict rows, and a cut, the one step whose soundness needs an integer point (Cert.lean's cut_sound),
// is refused; over the integers (the default: Cert.lean's check, exactly) a cut is allowed and no row is strict (a
// strict row over the integers is lin + 1 <= 0), so the naturals and the integers are the rationals plus that rule.
// Rows over the rationals come with integer coefficients (a leaf's linear forms over a positive denominator,
// kernel.ts), and in both domains every coefficient read or made must stay a safe integer, so none is rounded (a
// float past 2^53 would let a row of a true constraint read as a false one).
// A witness satisfies its constraints when every one of them evaluates to at most 0 at it.
import type {Constraint, Lin, Step} from './solver.ts'

const vars = (lin: Lin) => Object.keys(lin).filter(key => key !== '1')
const exact = (lin: Lin) => Object.values(lin).every(c => Number.isSafeInteger(c))

export function checkRefutation(constraints: Constraint[], steps: Step[], integral = true): boolean {
  const rows: Lin[] = [], strict: boolean[] = []
  for (const [i, s] of steps.entries()) {
    if (s.kind === 'input') {
      if (!(Number.isInteger(s.index) && s.index >= 0 && s.index < constraints.length)) return false
      const c = constraints[s.index]!
      if (!exact(c.lin)) return false
      rows.push(c.lin); strict.push(!integral && c.strict === true)
    } else if (s.kind === 'combine') {
      if (!(s.a < i && s.b < i && Number.isSafeInteger(s.ma) && Number.isSafeInteger(s.mb) && s.ma > 0 && s.mb > 0)) return false
      if (!integral && !(Number.isInteger(s.a) && Number.isInteger(s.b) && s.a >= 0 && s.b >= 0)) return false
      const out: Lin = {}
      for (const [lin, m] of [[rows[s.a]!, s.ma], [rows[s.b]!, s.mb]] as const) for (const [key, c] of Object.entries(lin)) out[key] = (out[key] ?? 0) + m * c
      if (!exact(out)) return false
      rows.push(out); strict.push(strict[s.a]! || strict[s.b]!)
    } else {
      if (!integral) return false
      const row = rows[s.of]
      if (!(row !== undefined && s.of < i && Number.isSafeInteger(s.g) && s.g > 0 && vars(row).every(key => row[key]! % s.g === 0))) return false
      rows.push({...Object.fromEntries(vars(row).map(key => [key, row[key]! / s.g])), 1: Math.ceil((row['1'] ?? 0) / s.g)}); strict.push(false)
    }
  }
  const last = rows.at(-1), constant = last?.['1'] ?? 0
  return last !== undefined && vars(last).every(key => last[key] === 0) && (constant > 0 || (strict.at(-1)! && constant >= 0))
}

export function checkWitness(constraints: Constraint[], witness: Record<string, number>): boolean {
  return constraints.every(c => Object.entries(c.lin).reduce((sum, [key, a]) => sum + a * (key === '1' ? 1 : (witness[key] ?? NaN)), 0) <= 0)
}
