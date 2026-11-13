// Search policy is not work accounting. The projection is a new deterministic
// heuristic, not a replay of the legacy clock (whose charges and wall differed).
import {completeWorkProfile} from './work-profile.ts'
import {workLedger} from './work-admission.ts'
import {legacyWeights} from './work-kinds.ts'

export type ProxySearchState = {
  rate: number
  model: boolean
  deadline: number
  deadlineEpr: number
  workCap: number
  wallEnd: number
}
type SearchPolicy = {kind: 'native'} | {kind: 'proxy', state: ProxySearchState}
let policy: SearchPolicy | undefined
export const proxySearchState = (): ProxySearchState | undefined => policy?.kind === 'proxy' ? policy.state : undefined
export const inProxySearch = (): boolean => policy?.kind === 'proxy'

// No extra counter, weight, charge, grant, lease or root. Preserve declared order.
export function projectedSearchWork(): number {
  let n = 0
  for (const [key, weight] of legacyWeights) n += weight * Number(workLedger.counter(key))
  return n
}
// Public proveRule owns the selection, using its existing actual-machine test.
// A native parent locks its entire call tree, including nested plain public calls.
// A native public child of a proxy temporarily suspends it; proxy state is separate
// from all legacy/native control state and resumes only after that child exits.
export function withPlainSearchPolicy<T>(hasCounts: boolean, run: () => T): T {
  if (!completeWorkProfile.enabled || !workLedger.inBudget() || policy?.kind === 'native'
    || policy?.kind === 'proxy' && !hasCounts) return run()
  const previous = policy
  policy = hasCounts ? {kind: 'native'} : {kind: 'proxy', state: {
    rate: 0, model: false, deadline: Infinity, deadlineEpr: 0, workCap: Infinity, wallEnd: Infinity,
  }}
  try { return run() } finally { policy = previous }
}
