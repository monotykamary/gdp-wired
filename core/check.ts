// The trusted part, in TypeScript (bendtt-style twin: check.lean is the same checker with its soundness proof).
// A derivation refutes its constraints when every step replays: an input is that constraint, a combination adds two
// earlier rows with positive integer multipliers, a cut divides every variable coefficient of an earlier row by g > 0
// (each must be divisible) and rounds the constant up, and the last row has no variable and a positive constant.
// A witness satisfies its constraints when every one of them evaluates to at most 0 at it.
import type {Constraint, Lin, Step} from './solver.ts'

const vars = (lin: Lin) => Object.keys(lin).filter(key => key !== '1')

export function checkRefutation(constraints: Constraint[], steps: Step[]): boolean {
  const rows: Lin[] = []
  for (const [i, s] of steps.entries()) {
    if (s.kind === 'input') {
      if (!(s.index >= 0 && s.index < constraints.length)) return false
      rows.push(constraints[s.index]!.lin)
    } else if (s.kind === 'combine') {
      if (!(s.a < i && s.b < i && Number.isInteger(s.ma) && Number.isInteger(s.mb) && s.ma > 0 && s.mb > 0)) return false
      const out: Lin = {}
      for (const [lin, m] of [[rows[s.a]!, s.ma], [rows[s.b]!, s.mb]] as const) for (const [key, c] of Object.entries(lin)) out[key] = (out[key] ?? 0) + m * c
      rows.push(out)
    } else {
      const row = rows[s.of]
      if (!(row !== undefined && s.of < i && Number.isInteger(s.g) && s.g > 0 && vars(row).every(key => row[key]! % s.g === 0))) return false
      rows.push({...Object.fromEntries(vars(row).map(key => [key, row[key]! / s.g])), 1: Math.ceil((row['1'] ?? 0) / s.g)})
    }
  }
  const last = rows.at(-1)
  return last !== undefined && vars(last).every(key => last[key] === 0) && (last['1'] ?? 0) > 0
}

export function checkWitness(constraints: Constraint[], witness: Record<string, number>): boolean {
  return constraints.every(c => Object.entries(c.lin).reduce((sum, [key, a]) => sum + a * (key === '1' ? 1 : (witness[key] ?? NaN)), 0) <= 0)
}
