// Cooperative cancellation of untrusted search. Legacy callers retain their
// wall; an explicit work scope never consults it or grants completion headroom.
import {wallTermination, clock, searchNow, wallAt, inBudget, inWorkScope, checkBudget, checkWorkAdmission, remainingWork,wallDeadline,type WallDeadline} from '../kernel/prove.ts'
import {runtimeWall} from './runtime-wall.ts'
import type {SearchTermination} from './search-termination.ts'
export {wallDeadline,withBudget, budgetEnd, inBudget, checkBudget, checkWorkEndpoint, BudgetExpired, searchNow} from '../kernel/prove.ts'
export {traceNow} from './trace-clock.ts'
// CLI proposal loops historically use epoch milliseconds rather than performance.
// Preserve that fallback, but share the work clock in either opt-in work mode.
export const searchDateNow = (): number => inWorkScope() ? clock() : Date.now()
export const searchWall = (ms: number): WallDeadline => wallDeadline(inWorkScope()
  ? Math.min(wallAt(), clock() + Math.max(0, ms))
  : searchNow() + ms - Math.min(1000, Math.max(0, ms) / 20))
// Legacy transport had a scaled wall allowance for uncounted assembly. Work
// mode uses the given counted end, without a time multiplier or fresh budget.
export const transportEnd = (until: number, cap = Infinity): number => inWorkScope()
  ? Math.min(wallAt(), until)
  : Math.min(wallAt(), searchNow() + Math.min(cap, Math.max(0, until - clock()) * 10))
export class WallExpired extends Error {
  constructor(readonly phase: string, readonly termination?: SearchTermination) { super(`time (${phase})`); this.name = 'WallExpired' }
}
export function checkWall(phase: string): void {
  if (inBudget()) { checkBudget(phase); return }
  const termination = wallTermination(phase)
  if (termination) throw new WallExpired(phase, termination)
}
// The interpreter must not import the proof engine just to check cancellation.
runtimeWall.check = checkWall
runtimeWall.admit = checkWorkAdmission
runtimeWall.remaining = remainingWork
