// Wall telemetry is unavailable inside counted search, including legacy counted
// scopes. Zero means no wall measurement, not elapsed time or counted units.
// Do not capture/bind a clock: a tripwire must see every possible wall read.
import {stepWorkProfile} from './step-work.ts'
let depth = 0
export const snapshotTraceClockDepth = (): number => depth
export function withTraceWorkScope<T>(f: () => T): T {
  depth++
  try { return f() } finally { depth-- }
}
export const traceNow = (): number => stepWorkProfile.enabled || depth > 0 ? 0 : performance.now()

