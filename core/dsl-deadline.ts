// Soft search limits are not replacements for the caller's work budget.
// Legacy mode executes the identical polling path. Full accounting consumes
// only authenticated refusals belonging to this stage's own endpoint.
import {budgetEnd, clock, fullRate, inWorkScope, withDeadline, withWall} from '../kernel/prove.ts'
import {workLedger} from './work-admission.ts'
import {workFromNumber, workMultiply} from './work-amount.ts'
import {completeWorkProfile} from './work-profile.ts'

export function withStageDeadline<T, F>(until: number, run: () => T, refused: () => F): T | F {
  if (!completeWorkProfile.enabled) return withDeadline(until, run)
  if (until === Infinity) return workLedger.withCapacityRefusalBoundary(run)
  return workLedger.withDeadlineRefusalBoundary(workMultiply(workFromNumber(until), workFromNumber(fullRate)), run, refused)
}
// These two stages previously polled their ms allowance without opening a
// legacy deadline. Only full accounting adds the admission boundary.
export function withStageAllowance<T, F>(ms: number, run: () => T, refused: () => F): T | F {
  return completeWorkProfile.enabled ? withStageDeadline(clock() + ms, run, refused) : run()
}
// A DSL wall used as a local stage allowance is also a counted deadline inside
// a work scope. Do not change the legacy wall path, or the supplied endpoint.
export function withStageWall<T, F>(until: number, run: () => T, refused: () => F): T | F {
  return inWorkScope() ? withStageDeadline(Math.min(budgetEnd(), until), run, refused) : withWall(until, run)
}
