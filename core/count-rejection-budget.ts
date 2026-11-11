// Scheduling only. Rejection earns no facts and cannot enlarge the root budget.
import {type CountTierBudget} from './count-tier-budget.ts'
export type CountRejectionBudget=Readonly<{captureUntil:number,rejectionUntil:number,rejectionLimit:number}>
// One third of the generation tier, not an absolute provisional-unit ceiling.
export function countRejectionBudget(budget:CountTierBudget|undefined,enabled:boolean):CountRejectionBudget|undefined{
 if(!enabled||!budget?.active)return
 const start=budget.until-budget.workAllowance,end=Math.min(budget.until,budget.generationUntil)
 if(![start,end,budget.workAllowance].every(Number.isFinite)||budget.workAllowance<0)throw new RangeError('invalid rejection tier')
 const generation=Math.max(0,end-start),rejectionLimit=generation/3
 return Object.freeze({captureUntil:end-rejectionLimit,rejectionUntil:end,rejectionLimit})
}
export function remainingRejectionAllowance(budget:CountRejectionBudget,now:number):number{
 if(!Number.isFinite(now))throw new RangeError('invalid rejection clock')
 return Math.max(0,Math.min(budget.rejectionLimit,budget.rejectionUntil-now))
}
