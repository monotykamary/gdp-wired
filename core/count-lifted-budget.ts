// W is the original enclosing CLOCK-unit allowance, not a remaining case share.
// Divide once: every local leaf uses W/120, every operation uses W/30, and
// both are clipped to the caller's absolute endpoint. Legacy search is exact.
import {completeWorkProfile} from './work-profile.ts'
import {type CountStrategyOptions,strategyLeafUnits} from './count-strategy.ts'
import {clock} from '../kernel/prove.ts'
import {countPrimitiveUnits} from './count-primitive-budget.ts'
import {type WorkAmount, workShare} from './work-amount.ts'
import {remainingAdmittedWork, workAdmissionSnapshot, workLedger} from './work-admission.ts'

export type LiftedWorkSlice = Readonly<{kind:'case'|'leaf',key:string,caseKey?:string,allocation:WorkAmount,scopeId:number,rootEpoch:number}>
export type LiftedWorkSliceObserver = (slice:LiftedWorkSlice)=>void
export type LiftedLeasePlan = Readonly<{original:WorkAmount,leaf:WorkAmount,operation:WorkAmount,cases:Readonly<Record<string,WorkAmount>>,observe?:LiftedWorkSliceObserver}>
export type LiftedWorkBudget=Readonly<{workAllowance:number,leafUnits:number,caseUnits:number,full:boolean,lease?:LiftedLeasePlan}>
export function liftedWorkBudget(workAllowance:number,full=completeWorkProfile.enabled):LiftedWorkBudget{
 if(full&&(!Number.isFinite(workAllowance)||workAllowance<0))throw new RangeError('invalid lifted work allowance')
 return Object.freeze({workAllowance,leafUnits:full?strategyLeafUnits(workAllowance):500,caseUnits:full?workAllowance/30:2000,full})
}
export const liftedDeadline=(now:number,parent:number,units:number):number=>Math.min(parent,now+Math.max(0,units))
export function liftedLeafUntil(until:number,options:CountStrategyOptions,legacy=500):number{
 return liftedDeadline(clock(),until,countPrimitiveUnits(legacy,options.leafUnits))
}
export function liftedCaseUntil(until:number,budget:LiftedWorkBudget,frame=false):number{
 return liftedDeadline(clock(),until,countPrimitiveUnits(frame?500:2000,budget.caseUnits))
}

// Explicit opt-in. These amounts are RAW work from the original grant, never
// decoded from clock(), remaining capacity or a telemetry display. Infinity is
// only the legacy-until sentinel inside a live exact child scope.
export function liftedWorkLeaseBudget(original:WorkAmount,overrides:{leaf?:WorkAmount,cases?:Readonly<Record<string,WorkAmount>>,observe?:LiftedWorkSliceObserver}={}):LiftedWorkBudget{
 if(!completeWorkProfile.enabled)throw new Error('lifted work leases require FULL accounting')
 const valid=(amount:WorkAmount)=>{if(amount.den<=0n||amount.num<0n)throw new RangeError('invalid lifted work grant')}
 valid(original)
 const leaf=overrides.leaf??workShare(original,1n,120n),operation=workShare(original,1n,30n),cases=Object.freeze({...overrides.cases})
 valid(leaf);for(const amount of Object.values(cases))valid(amount)
 return Object.freeze({workAllowance:Infinity,leafUnits:Infinity,caseUnits:Infinity,full:true,lease:Object.freeze({original,leaf,operation,cases,observe:overrides.observe})})
}
function withLiftedSlice<T>(kind:'case'|'leaf',key:string,allocation:WorkAmount,observe:LiftedWorkSliceObserver|undefined,run:(until:number)=>T,caseKey?:string):T{
 if(!key)throw new Error('lifted work slice requires a stable key')
 if(!completeWorkProfile.enabled||remainingAdmittedWork()===null)throw new Error('lifted work slice requires an inherited FULL endpoint')
 return workLedger.withBudget(allocation,()=>{
  const snapshot=workAdmissionSnapshot(),scope=snapshot.activeEndpoints.at(-1)!
  observe?.({kind,key,caseKey,allocation,scopeId:scope.id,rootEpoch:snapshot.rootEpoch})
  return run(Infinity)
 })
}
export function withLiftedLeaf<T>(until:number,options:CountStrategyOptions,legacy:number,key:string,run:(until:number)=>T):T{
 return options.leafWork===undefined?run(liftedLeafUntil(until,options,legacy)):withLiftedSlice('leaf',key,options.leafWork,options.workSliceObserver,run,options.caseKey)
}
export function withLiftedCase<T>(until:number,budget:LiftedWorkBudget,frame:boolean,key:string,run:(until:number)=>T):T{
 const plan=budget.lease
 return plan===undefined?run(liftedCaseUntil(until,budget,frame)):withLiftedSlice('case',key,plan.cases[key]??plan.operation,plan.observe,run)
}
export function liftedLeaseOptions(budget:LiftedWorkBudget,caseKey:string):Pick<CountStrategyOptions,'leafUnits'|'leafWork'|'caseKey'|'workSliceObserver'>{
 return {leafUnits:budget.leafUnits,...(budget.lease?{leafWork:budget.lease.leaf,caseKey,workSliceObserver:budget.lease.observe}:{})}
}
