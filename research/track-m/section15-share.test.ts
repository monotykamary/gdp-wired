import {test,expect} from 'bun:test'
import {supportBudget} from '../../core/support-budget.ts'
import {supportShare} from './section15-share.ts'
test('each attempt receives an even share of what remains, not the round-start balance',()=>{
 let remaining=1200,untried=4
 expect(supportShare(remaining,untried)).toBe(300)
 remaining-=30;untried--
 expect(supportShare(remaining,untried)).toBe(390)
 remaining-=390;untried--
 expect(supportShare(remaining,untried)).toBe(390)
})
test('shares and unchanged support draws are nonnegative and bounded by the current pool',()=>{
 for(const remaining of [-1,0,1,2,30,2700,60000])for(let untried=0;untried<=35;untried++){
  const share=supportShare(remaining,untried)
  expect(share).toBeGreaterThanOrEqual(0);expect(share).toBeLessThanOrEqual(Math.max(0,remaining))
  for(const caller of [false,true])for(const structural of [false,true]){
   const draw=supportBudget(remaining,share,caller,structural)
   expect(draw).toBeGreaterThanOrEqual(0);expect(draw).toBeLessThanOrEqual(Math.max(0,remaining))
  }
 }
})
test('local support and caller ceilings are unchanged',()=>{
 expect(supportBudget(60000,supportShare(60000,30),false,true)).toBe(5000)
 expect(supportBudget(60000,supportShare(60000,30),true)).toBe(20000)
 expect(supportBudget(2700,supportShare(2700,3),false)).toBe(900)
 expect(supportBudget(10,5000,false,true)).toBe(10)
})
