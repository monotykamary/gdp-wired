import {expect,test} from 'bun:test'
import {type Goal} from '../kernel/kernel.ts'
import {type C} from './machine.ts'
import {budgetedLeafRows} from './prover-row-budget.ts'
import {completeWorkProfile} from './work-profile.ts'
import {withBudget,BudgetExpired} from './wall.ts'
import {fullWork} from '../kernel/prove.ts'
const full=completeWorkProfile.enabled?test:test.skip
const fixture=():Goal=>({name:'independent row cells',hyps:Array.from({length:20},(_,i):C=>({op:'<=',a:{op:'var',name:'x'+i},b:{op:'const',value:0}}))})
full('the untrusted leaf row proposer admits table cells before a tight endpoint',()=>{
 for(const W of [0,1,5,17,31]){
  const start=fullWork()
  expect(()=>withBudget(W,()=>budgetedLeafRows(fixture(),new Map()))).toThrow(BudgetExpired)
  expect(fullWork()-start).toBeLessThanOrEqual(W)
 }
})
test('ample leaf row proposals keep their content',()=>{
 const plain=budgetedLeafRows(fixture(),new Map())
 const scoped=withBudget(100000,()=>budgetedLeafRows(fixture(),new Map()))
 expect(scoped).toEqual(plain)
 expect(scoped.length).toBeGreaterThan(0)
})
