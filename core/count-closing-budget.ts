// Opt-in family check-once scheduling, not proof acceptance or calibration.
import {type CountTierBudget,countTierBudget} from './count-tier-budget.ts'
import {budgetEnd} from '../kernel/prove.ts'
export type CountClosingBudget=CountTierBudget & Readonly<{
 closingMode:'family-check-once',
 closingFloor:number,
 searchUntil:number,
 initialUntil:number,
}>
// Explicit replacement allocation: generation <=1/4, strategy floor7/20,
// ordinary/INIT floor1/40, closing native floor3/8. They sum to one root W.
// The old ordinary-search floor3/10 is NOT claimed in this opt-in mode.
export function reserveCountClosing(budget:CountTierBudget,enabled=false,rootUntil=budgetEnd()):CountTierBudget|CountClosingBudget{
 if(!enabled||!budget.active)return budget
 if(Number.isNaN(rootUntil)||rootUntil===-Infinity)throw new RangeError('invalid root endpoint')
 const until=Math.min(budget.until,rootUntil)
 if(until<budget.until){
  const start=budget.until-budget.workAllowance,clamped=countTierBudget(start,until,1)
  budget=Object.freeze({...clamped,generationUntil:Math.min(budget.generationUntil,clamped.generationUntil)})
 }
 if('closingMode'in budget){
  if(budget.closingMode!=='family-check-once')throw new RangeError('unknown closing mode')
  return budget as CountClosingBudget
 }
 const width=budget.workAllowance
 if(!Number.isFinite(width)||width<0||!Number.isFinite(budget.until))throw new RangeError('invalid closing allowance')
 const ordinaryFloor=width/40,closingFloor=width*3/8,searchUntil=budget.until-closingFloor
 const strategyUntil=Math.min(budget.strategyUntil??budget.until,searchUntil-ordinaryFloor)
 return Object.freeze({...budget,ordinaryFloor,strategyUntil,closingMode:'family-check-once' as const,closingFloor,searchUntil,initialUntil:searchUntil})
}
// An observed-cost estimate, NOT a worst-case kernel bound. Two times the
// checked held packets' measured replay/check cost leaves an explicit margin.
// If there is no measurement retain the old reserve. Insufficient estimates
// can only produce UNKNOWN at the unchanged root/native acceptance boundary.
export function reserveCheckedCountClosing(budget:CountClosingBudget,costs:readonly number[],now:number):CountClosingBudget{
 if(!Number.isFinite(now))throw new RangeError('invalid reserve clock')
 if(costs.some(cost=>!Number.isFinite(cost)||cost<0))throw new RangeError('invalid checked packet cost')
 if(!costs.length)return budget
 const total=costs.reduce((sum,cost)=>sum+cost,0)
 const closingFloor=Math.min(budget.workAllowance,Math.max(0,budget.until-now),Math.max(1,total*2))
 const searchUntil=budget.until-closingFloor
 const ordinaryFloor=Math.min(budget.ordinaryFloor,Math.max(0,searchUntil-now))
 const strategyUntil=searchUntil-ordinaryFloor
 return Object.freeze({...budget,ordinaryFloor,closingFloor,searchUntil,initialUntil:searchUntil,strategyUntil})
}
export function countOrdinaryUntil(budget:CountTierBudget):number{
 return 'closingMode'in budget?(budget as CountClosingBudget).searchUntil:budget.until
}
