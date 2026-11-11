import {expect,test} from 'bun:test'
import {countTierBudget} from './count-tier-budget.ts'
import {budgetEnd,clock,withBudget} from '../kernel/prove.ts'
import {countOrdinaryUntil,reserveCountClosing,type CountClosingBudget} from './count-closing-budget.ts'
test('check-once replaces the ordinary floor instead of overcommitting W',()=>{
 const base=countTierBudget(100,900100,1),plan=reserveCountClosing(base,true) as CountClosingBudget
 expect(plan.until).toBe(base.until)
 expect(plan.workAllowance).toBe(900000)
 expect(plan.generationUntil).toBe(225100)
 expect(plan.strategyUntil).toBe(540100)
 expect(plan.searchUntil).toBe(562600)
 expect(plan.initialUntil).toBe(plan.searchUntil)
 expect(plan.ordinaryFloor).toBe(22500)
 expect(plan.closingFloor).toBe(337500)
 expect(plan.generationUntil-100+plan.strategyFloor+plan.ordinaryFloor+plan.closingFloor).toBe(900000)
 expect(plan.until-plan.searchUntil).toBe(plan.closingFloor)
})
test('all laws and retries share immutable endpoints, not new reservations',()=>{
 for(const count of [1,2,7,49]){
  const plan=reserveCountClosing(countTierBudget(0,900000,count),true) as CountClosingBudget
  expect(plan.strategyUntil).toBe(540000)
  expect(plan.searchUntil).toBe(562500)
  expect(reserveCountClosing(plan,true)).toBe(plan)
  expect(Object.isFrozen(plan)).toBe(true)
 }
})
test('legacy and no-dispatch paths are exact identity',()=>{
 const legacy=countTierBudget(0,900000,3),inactive=countTierBudget(0,900000,0)
 expect(reserveCountClosing(legacy)).toBe(legacy)
 expect(reserveCountClosing(legacy,false)).toBe(legacy)
 expect(reserveCountClosing(inactive,true)).toBe(inactive)
 expect(countOrdinaryUntil(legacy)).toBe(legacy.until)
})
test('scaling and preflight cannot move the root or consume native reserve',()=>{
 for(const width of [0,1,120,60000,900000,3600000]){
  const original=countTierBudget(31,31+width,2),base={...original,generationUntil:31+width/8}
  const plan=reserveCountClosing(base,true) as CountClosingBudget
  expect(plan.until).toBe(base.until)
  expect(plan.generationUntil).toBe(base.generationUntil)
  expect(plan.strategyUntil!-plan.generationUntil).toBeGreaterThanOrEqual(plan.strategyFloor-1e-9)
  expect(plan.searchUntil-plan.strategyUntil!).toBeCloseTo(plan.ordinaryFloor)
  expect(plan.until-countOrdinaryUntil(plan)).toBeCloseTo(plan.closingFloor)
 }
})
test('the supplied measurement fits only as a diagnostic, not a predictive cost bound',()=>{
 const plan=reserveCountClosing(countTierBudget(0,900000,1),true) as CountClosingBudget
 expect(plan.closingFloor*250).toBe(84375000)
 expect(plan.closingFloor*250).toBeGreaterThan(81194798)
 expect(225000000-115200000-81194798).toBe(28605202)
})
test('a nominal end beyond the actual root cannot enlarge any reserved endpoint',()=>{
 const base=countTierBudget(29695,929695,1),plan=reserveCountClosing(base,true,900000) as CountClosingBudget
 expect(plan.until).toBe(900000)
 expect(plan.workAllowance).toBe(870305)
 expect(plan.closingFloor).toBe(870305*3/8)
 expect(plan.strategyUntil).toBeLessThan(plan.searchUntil)
 expect(plan.searchUntil).toBeLessThan(plan.until)
 expect(plan.generationUntil).toBeLessThanOrEqual(base.generationUntil)
 expect(reserveCountClosing(plan,true,900000)).toBe(plan)
})
test('default reservation reads the inherited budgetEnd rather than trusting a nominal plan',()=>{
 withBudget(225000000,()=>{
  const root=budgetEnd(),start=clock()+29695,base=countTierBudget(start,root+29695,1)
  const plan=reserveCountClosing(base,true) as CountClosingBudget
  expect(plan.until).toBe(root)
  expect(plan.workAllowance).toBeCloseTo(root-start)
  expect(plan.searchUntil).toBeLessThan(root)
 })
})
