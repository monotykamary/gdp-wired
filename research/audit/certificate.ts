// The trusted part: a Farkas certificate refutes its constraints when its multipliers are nonnegative, the weighted sum
// of the constraints has no variable left, and its constant is positive. Nothing here knows how the solver found it.
import type {Constraint} from './solver.ts'

export function checkCertificate(constraints: Constraint[], multipliers: number[]): boolean {
  if (multipliers.length !== constraints.length || multipliers.some(m => !(Number.isInteger(m) && m >= 0))) return false
  const sum: Record<string, number> = {}
  constraints.forEach((c, i) => {
    for (const [key, value] of Object.entries(c.lin)) sum[key] = (sum[key] ?? 0) + multipliers[i]! * value
  })
  return Object.entries(sum).every(([key, value]) => key === '1' || value === 0) && (sum['1'] ?? 0) > 0
}
