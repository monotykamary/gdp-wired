import {expect,test} from 'bun:test'
import {countTierBudget} from './count-tier-budget.ts'
import {countRejectionBudget,remainingRejectionAllowance} from './count-rejection-budget.ts'
test('rejection is a scale-invariant share of generation, with no new root allowance',()=>{
 for(const width of [0,1,120,60000,900000,3600000]){
  const tier=countTierBudget(100,100+width,1),plan=countRejectionBudget(tier,true)!
  expect(plan.rejectionUntil).toBe(tier.generationUntil)
  expect(plan.rejectionLimit).toBeCloseTo(width/12)
  expect(plan.captureUntil-100+plan.rejectionLimit).toBeCloseTo(width/4)
  expect(plan.captureUntil).toBeLessThanOrEqual(plan.rejectionUntil)
  expect(plan.rejectionUntil).toBeLessThanOrEqual(tier.until)
 }
})
test('unused capture work does not grant rejection more than its original share',()=>{
 const tier=countTierBudget(0,900000,2),plan=countRejectionBudget(tier,true)!
 expect(plan.rejectionLimit).toBe(75000)
 for(const now of [0,100,150000])expect(remainingRejectionAllowance(plan,now)).toBe(75000)
 expect(remainingRejectionAllowance(plan,200000)).toBe(25000)
 expect(remainingRejectionAllowance(plan,225000)).toBe(0)
 expect(remainingRejectionAllowance(plan,225001)).toBe(0)
})
test('one absolute endpoint survives fallbacks and preflight is not regranted',()=>{
 const plan=countRejectionBudget({...countTierBudget(100,1100,1),generationUntil:200},true)!
 expect(plan.rejectionLimit).toBeCloseTo(100/3)
 expect(plan.captureUntil).toBeCloseTo(200-100/3)
 const first=remainingRejectionAllowance(plan,190),second=remainingRejectionAllowance(plan,195)
 expect(first).toBe(10);expect(second).toBe(5)
})
test('disabled or unselected paths have no reservation',()=>{
 expect(countRejectionBudget(undefined,true)).toBeUndefined()
 expect(countRejectionBudget(countTierBudget(0,900000,1),false)).toBeUndefined()
 expect(countRejectionBudget(countTierBudget(0,900000,0),true)).toBeUndefined()
})
test('expired generation cannot create a rejection allowance',()=>{
 const plan=countRejectionBudget({...countTierBudget(100,200,1),generationUntil:99},true)!
 expect(plan.rejectionLimit).toBe(0)
 expect(remainingRejectionAllowance(plan,100)).toBe(0)
 expect(()=>remainingRejectionAllowance(plan,NaN)).toThrow(RangeError)
})
