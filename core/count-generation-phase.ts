// Optional generation phase. Legacy callers run exactly the original body.
import {BudgetExpired,budgetEnd,checkBudget,clock,fullRate,withBudget,withDeadline,withinDeadline} from '../kernel/prove.ts'
import {inProxySearch} from './search-policy.ts'
import {withSearchAllowance} from './count-search-allowance.ts'
export type CountGenerationResult<T>={complete:true,value:T}|{complete:false}
export function countGenerationPhase<T>(until:number,run:()=>T):CountGenerationResult<T>{
 checkBudget('generation parent entry')
 const remaining=until-clock()
 if(remaining<=0)return {complete:false}
 // A proxy allowance has no owned ledger endpoint: never catch a hard refusal.
 if(inProxySearch())return withSearchAllowance(until,()=>({complete:true as const,value:run()}))
 // Capture the inherited endpoint while a nonrestricting budget exposes bare
 // withWork caps too. Equality is parent expiry, never a local partial result.
 const parentEnd=withBudget(Number.MAX_VALUE,()=>withinDeadline(budgetEnd()))
 let installedEnd:number|undefined
 try{return withBudget(remaining*fullRate,()=>{
  installedEnd=withinDeadline(budgetEnd())
  return withDeadline(until,()=>({complete:true as const,value:run()}))
 })}
 catch(error){
  if(!(error instanceof BudgetExpired))throw error
  // A bare withWork cap has no sticky parent budget after child unwind.
  // Only an endpoint strictly inside the captured parent can expire locally.
  checkBudget('generation parent completion')
  if(installedEnd===undefined||installedEnd>=parentEnd)throw error
  return {complete:false}
 }
}
