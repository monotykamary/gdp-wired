// Counted-unit reservations, not wall-clock timers. A strategy floor is not
// a per-law or pool cap: the unreserved remainder and unused generation flow
// to strategies, while an ordinary-work floor remains protected.
import {attemptShare} from './support-budget.ts'
import {BudgetExpired,budgetEnd,clock,withDeadline} from '../kernel/prove.ts'
export type CountTierBudget = Readonly<{
 active:boolean,
 generationUntil:number,
 strategyFloor:number,
 ordinaryFloor:number,
 strategyUntil:number|undefined,
 until:number,
}>
export function countTierBudget(start:number,until:number,selectedStrategies:number):CountTierBudget{
 if(!Number.isSafeInteger(selectedStrategies)||selectedStrategies<0)throw new RangeError('invalid strategy count')
 // No dispatcher hit: no reservation and precisely the existing split.
 if(!selectedStrategies)return Object.freeze({active:false,generationUntil:until,strategyFloor:0,ordinaryFloor:0,strategyUntil:undefined,until})
 if(!Number.isFinite(start)||!Number.isFinite(until))throw new RangeError('tiered work requires finite counted endpoints')
 const width=Math.max(0,until-start),ordinaryFloor=width*3/10
 return Object.freeze({active:true,generationUntil:Math.min(until,start+width/4),strategyFloor:width*7/20,ordinaryFloor,strategyUntil:until-ordinaryFloor,until})
}
// The public caller has already spent work on normalization and preflight.
// Never regrant its original duration after that work.
export function remainingCountTierBudget(start:number,requested:number,selected:number):CountTierBudget{
 const plan=countTierBudget(start,Math.min(start+requested,budgetEnd()),selected)
 if(!plan.active)return plan
 // Include fixed public preflight in the original generation quarter.
 const originalStart=plan.until-requested
 return Object.freeze({...plan,generationUntil:Math.min(plan.generationUntil,originalStart+requested/4)})
}
// One endpoint shared by every STEP refinement and every retry. Expiration
// returns to ordinary INIT/STEP completion; it does not cancel that reserve.
export function strategyPhase<T>(budget:CountTierBudget|undefined,attemptEnd:number,run:(end:number)=>T):T|undefined{
 if(!budget?.active)return run(attemptEnd)
 const end=Math.min(attemptEnd,budget.strategyUntil??attemptEnd)
 if(clock()>=end)return undefined
 try{
  const result=withDeadline(end,()=>run(end)),now=clock()
  // Equality does not throw BudgetExpired. Only a local-cap unknown hands
  // back the ordinary reserve; proofs and genuine refutations stay results.
  if(now>=end&&now<=budgetEnd()&&result!==null&&typeof result==='object'&&
     'stuck'in result&&result.stuck==='unknown'&&!('proof'in result)&&
     !('refuted'in result&&result.refuted))return undefined
  return result
 }catch(error){
  if(!(error instanceof BudgetExpired)||clock()<end||clock()>budgetEnd())throw error
  return undefined
 }
}

// A local full-work deadline throws the same exception as the public budget.
// Only the former is an unknown attempt: preserve the enclosing phase's end,
// captured before per-law/subset scopes, and never swallow outer cancellation.
export function isLocalCountExpiration(error:unknown,enclosingEnd:number):boolean{
 return error instanceof BudgetExpired&&clock()<Math.min(enclosingEnd,budgetEnd())
}

export function ordinaryTierShare(budget:CountTierBudget,now:number,pending:ReadonlySet<string>):number{
 return attemptShare(budget.until-now,pending)
}
