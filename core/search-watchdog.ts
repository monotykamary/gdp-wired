// An explicit real safety watchdog, independent of work accounting and legacy
// withWall. No watchdog means no real-clock read in explicit-work searches.
import type {SearchTermination} from './search-termination.ts'
let watchdogEnd = Infinity
export class WatchdogExpired extends Error {
  readonly termination: SearchTermination
  constructor(phase: string) {
    super(`wall deadline reached (${phase}; explicit watchdog)`)
    this.name = 'WatchdogExpired'
    this.termination = {kind: 'wall-deadline', phase, scope: 'search'}
  }
}
export function withSearchWatchdog<T>(ms: number | undefined, run: () => T): T {
  validateWatchdog(ms)
  const outer = watchdogEnd
  if (ms !== undefined) watchdogEnd = Math.min(outer, performance.now() + ms)
  try {
    checkWatchdog('search preflight')
    const out = run()
    checkWatchdog('search result')
    return out
  } finally { watchdogEnd = outer }
}
export function checkWatchdog(phase: string): void {
  if (watchdogEnd !== Infinity && performance.now() >= watchdogEnd) throw new WatchdogExpired(phase)
}
export function validateWatchdog(ms: number | undefined): void {
  if (ms !== undefined && (!Number.isFinite(ms) || ms < 0)) throw new RangeError('watchdogMs must be finite and nonnegative')
}
export function checkWatchdog(phase: string): void {
  if (watchdogEnd !== Infinity && performance.now() >= watchdogEnd) throw new WatchdogExpired(phase)
}
export function withSearchWatchdog<T>(ms: number | undefined, run: () => T): T {
  validateWatchdog(ms)
  if (ms === undefined) return run()
  const previous = watchdogEnd
  watchdogEnd = Math.min(previous, performance.now() + ms)
  try { checkWatchdog('search watchdog entry'); return run() }
  finally { watchdogEnd = previous }
}
