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
export function countOrdinaryUntil(budget:CountTierBudget):number{
 return 'closingMode'in budget?(budget as CountClosingBudget).searchUntil:budget.until
}
