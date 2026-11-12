// W is the original enclosing CLOCK-unit allowance, not a remaining case share.
// Divide once: every local leaf uses W/120, every operation uses W/30, and
// both are clipped to the caller's absolute endpoint. Legacy search is exact.
import {completeWorkProfile} from './work-profile.ts'
import {type CountStrategyOptions,strategyLeafUnits} from './count-strategy.ts'
import {clock} from '../kernel/prove.ts'
import {countPrimitiveUnits} from './count-primitive-budget.ts'
import {type WorkAmount, workShare,workSub} from './work-amount.ts'
import {remainingAdmittedWork, workAdmissionSnapshot, workLedger} from './work-admission.ts'
import {type CountFundingOwners} from './count-disjoint-funding.ts'

export type LiftedWorkSlice = Readonly<{kind:'case'|'leaf',key:string,caseKey?:string,allocation:WorkAmount,scopeId:number,rootEpoch:number}>
export type LiftedWorkSliceObserver = (slice:LiftedWorkSlice)=>void
export type LiftedWorkTraceEvent=Readonly<{stage:'start',slice:LiftedWorkSlice}>|
 Readonly<{stage:'end',slice:LiftedWorkSlice,used:WorkAmount,completed:boolean,error?:unknown}>
export type LiftedWorkTrace=(event:LiftedWorkTraceEvent)=>void
let sliceObserver:LiftedWorkSliceObserver|undefined
export function withLiftedWorkSliceObservation<T>(observe:LiftedWorkSliceObserver,run:()=>T):T{const prior=sliceObserver;sliceObserver=observe;try{return run()}finally{sliceObserver=prior}}
export type LiftedLeasePlan = Readonly<{original:WorkAmount,leaf:WorkAmount,operation:WorkAmount,cases:Readonly<Record<string,WorkAmount>>,observe?:LiftedWorkSliceObserver,trace?:LiftedWorkTrace,owners?:CountFundingOwners}>
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
export function liftedWorkLeaseBudget(original:WorkAmount,overrides:{leaf?:WorkAmount,cases?:Readonly<Record<string,WorkAmount>>,observe?:LiftedWorkSliceObserver,trace?:LiftedWorkTrace,owners?:CountFundingOwners}={}):LiftedWorkBudget{
 if(!completeWorkProfile.enabled)throw new Error('lifted work leases require FULL accounting')
 const valid=(amount:WorkAmount)=>{if(amount.den<=0n||amount.num<0n)throw new RangeError('invalid lifted work grant')}
 valid(original)
 const leaf=overrides.leaf??workShare(original,1n,120n),operation=workShare(original,1n,30n),cases=Object.freeze({...overrides.cases})
 valid(leaf);for(const amount of Object.values(cases))valid(amount)
 return Object.freeze({workAllowance:Infinity,leafUnits:Infinity,caseUnits:Infinity,full:true,lease:Object.freeze({original,leaf,operation,cases,observe:overrides.observe,trace:overrides.trace,owners:overrides.owners})})
}
function withLiftedSlice<T>(kind:'case'|'leaf',key:string,allocation:WorkAmount,observe:LiftedWorkSliceObserver|undefined,run:(until:number)=>T,caseKey?:string,trace?:LiftedWorkTrace):T{
 if(!key)throw new Error('lifted work slice requires a stable key')
 if(!completeWorkProfile.enabled||remainingAdmittedWork()===null)throw new Error('lifted work slice requires an inherited FULL endpoint')
 const state:{receipt?:{slice:LiftedWorkSlice,before:WorkAmount,completed:boolean,error?:unknown}}={}
 try{return workLedger.withBudget(allocation,()=>{
  const snapshot=workAdmissionSnapshot(),scope=snapshot.activeEndpoints.at(-1)!
  const slice={kind,key,caseKey,allocation,scopeId:scope.id,rootEpoch:snapshot.rootEpoch}
  if(!trace){observe?.(slice);sliceObserver?.(slice);return run(Infinity)}
  state.receipt={slice,before:workLedger.actual(),completed:false}
  trace({stage:'start',slice})
  observe?.(slice);sliceObserver?.(slice)
  const result=run(Infinity);state.receipt.completed=true;return result
 })}catch(error){if(state.receipt){state.receipt.error=error;state.receipt.completed=false}throw error}
 finally{
  const receipt=state.receipt
  // Finish bookkeeping after the expired local slice has unwound, but inside
  // its real parent/round. If that parent cannot pay, its hard stop wins.
  // `used` is exact work inside the physical slice, not its exit metadata.
  if(receipt)trace!({stage:'end',slice:receipt.slice,used:workSub(workLedger.actual(),receipt.before),completed:receipt.completed,...(!receipt.completed?{error:receipt.error}:{})})
 }
}
export function withLiftedLeaf<T>(until:number,options:CountStrategyOptions,legacy:number,key:string,run:(until:number)=>T):T{
 if(options.workOwners)return options.workOwners.leaf(key,()=>run(Infinity),options.caseKey)
 return options.leafWork===undefined?run(liftedLeafUntil(until,options,legacy)):withLiftedSlice('leaf',key,options.leafWork,options.workSliceObserver,run,options.caseKey,options.workSliceTrace)
}
export function withLiftedCase<T>(until:number,budget:LiftedWorkBudget,frame:boolean,key:string,run:(until:number)=>T):T{
 const plan=budget.lease
 if(plan?.owners)return plan.owners.case(key,()=>run(Infinity))
 return plan===undefined?run(liftedCaseUntil(until,budget,frame)):withLiftedSlice('case',key,plan.cases[key]??plan.operation,plan.observe,run,undefined,plan.trace)
}
export function liftedLeaseOptions(budget:LiftedWorkBudget,caseKey:string):Pick<CountStrategyOptions,'leafUnits'|'leafWork'|'caseKey'|'workSliceObserver'|'workSliceTrace'|'workOwners'>{
 return {leafUnits:budget.leafUnits,...(budget.lease?{leafWork:budget.lease.leaf,caseKey,workSliceObserver:budget.lease.observe,workSliceTrace:budget.lease.trace,workOwners:budget.lease.owners}:{})}
}
