// Atomic admission of a prepared retry. Metadata preparation is already paid;
// this boundary does not start a ticket or a callback when the live bank refuses.
import {BudgetExpired,type WorkLedger,workLedger} from './work-admission.ts'
import {CountAttemptTickets,countAttemptStop,type CountAttemptStop,type CountRetryPlan,type CountSlice} from './count-retry-budget.ts'
export type CountRoundValue<T>=Readonly<{kind:'proposal',value:T}>|Readonly<{kind:'decline',reason:string}>
export type CountRoundResult<T>=CountRoundValue<T>|Readonly<{kind:'unfinished',stop:CountAttemptStop}>|
 Readonly<{kind:'hard-cap',stop:CountAttemptStop}>|Readonly<{kind:'not-started',reason:string}>
export function runCountRetryRound<T>(plan:CountRetryPlan,tickets:CountAttemptTickets,run:()=>CountRoundValue<T>,
 options:{bank?:WorkLedger,slices?:readonly CountSlice[],eligible?:()=>boolean}={}):CountRoundResult<T>{
 if(plan.kind==='refused')return {kind:'not-started',reason:plan.reason}
 const bank=options.bank??workLedger
 if(!bank.inBudget()||plan.rootEpoch!==bank.snapshot().rootEpoch)return {kind:'not-started',reason:'missing-root'}
 if(tickets.snapshot().terminal||tickets.snapshot().active)return {kind:'not-started',reason:'tickets'}
 try{bank.checkAmount(plan.need,'count retry admission')}
 catch(error){if(error instanceof BudgetExpired)return {kind:'not-started',reason:'headroom'};throw error}
 return bank.withBudget(plan.need,()=>{
  if(options.eligible&&!options.eligible())return {kind:'not-started',reason:'ineligible'}
  // Ticket commitment and user code are inside the already funded round. Any
  // failure of this bookkeeping quantum is hard and starts no user callback.
  bank.start('ticks',1,'count retry ticket commitment')
  if(!tickets.start())return {kind:'not-started',reason:'tickets'}
  try{
   const value=run();tickets.finish(value.kind);return value
  }catch(error){
   if(!(error instanceof BudgetExpired)){tickets.finish('hard-cap');throw error}
   const stop=countAttemptStop(error,options.slices??[],bank)
   tickets.finish(stop.kind==='soft-slice'?'unfinished':'hard-cap')
   return stop.kind==='soft-slice'?{kind:'unfinished',stop}:{kind:'hard-cap',stop}
  }
 })
}
