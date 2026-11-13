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
type SearchPolicy = {kind: 'native', locked?: boolean} | {kind: 'proxy', state: ProxySearchState}
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
  policy = hasCounts ? {kind: 'native', locked: true} : {kind: 'proxy', state: {
    rate: 0, model: false, deadline: Infinity, deadlineEpr: 0, workCap: Infinity, wallEnd: Infinity,
  }}
  try { return run() } finally { policy = previous }
}

// A public counted call defers its policy choice until searchCounted knows the
// branch. Explicit native scopes and rejecting ancestors remain locked.
export function withPublicSearchPolicy<T>(hasCounts:boolean,run:()=>T):T {
 if(!hasCounts)return withPlainSearchPolicy(false,run)
 if(!completeWorkProfile.enabled||!workLedger.inBudget()||policy?.kind==='native'&&policy.locked!==false)return run()
 const previous=policy;policy={kind:'native',locked:false}
 try{return run()}finally{policy=previous}
}
export function canUseCountedProxy():boolean {
 return completeWorkProfile.enabled&&workLedger.inBudget()&&!(policy?.kind==='native'&&policy.locked!==false)
}
// Only the counted branch selector may relax an unresolved native policy.
export function withCountedSearchPolicy<T>(rejecting:boolean,run:()=>T):T {
 if(!completeWorkProfile.enabled||!workLedger.inBudget()||policy?.kind==='native'&&policy.locked!==false)return run()
 if(!rejecting&&policy?.kind==='proxy')return run()
 const previous=policy
 policy=rejecting?{kind:'native',locked:true}:{kind:'proxy',state:{rate:0,model:false,deadline:Infinity,deadlineEpr:0,workCap:Infinity,wallEnd:Infinity}}
 try{return run()}finally{policy=previous}
}
