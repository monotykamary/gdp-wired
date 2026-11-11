import {describe,expect,it} from 'bun:test'
import {liftedDeadline,liftedWorkBudget} from './count-lifted-budget.ts'
describe('one-time lifted W-relative caps',()=>{
 it('uses the original W in clock units, including a smaller parent share',()=>{
  const W=1_000_000_000/250,b=liftedWorkBudget(W,true)
  expect(b.leafUnits).toBe(W/120);expect(b.caseUnits).toBe(W/30)
  const now=123,share=50_000,end=now+share
  const caseEnd=liftedDeadline(now,end,b.caseUnits)
  expect(caseEnd).toBe(end)
  expect(liftedDeadline(now,caseEnd,b.leafUnits)).toBe(now+W/120)
  expect(liftedDeadline(now+1,caseEnd,b.leafUnits)).toBe(now+1+W/120)
 })
 it('never redivides a case share or extends any absolute parent',()=>{
  for(const W of [0,1,7,120,900_000,4_000_000,8_000_000])for(const remaining of [0,1,100,W/100,W]){
   const now=19,parent=now+remaining,b=liftedWorkBudget(W,true),caseEnd=liftedDeadline(now,parent,b.caseUnits),leafEnd=liftedDeadline(now,caseEnd,b.leafUnits)
   expect(caseEnd).toBeLessThanOrEqual(parent);expect(leafEnd).toBeLessThanOrEqual(caseEnd)
   expect(leafEnd).toBe(Math.min(parent,now+W/30,now+W/120))
  }
 })
 it('preserves legacy constants without validating an unused W',()=>{
  for(const W of [-1,Infinity,NaN,4_000_000]){const b=liftedWorkBudget(W,false);expect(b.leafUnits).toBe(500);expect(b.caseUnits).toBe(2000);expect(b.full).toBe(false)}
 })
 it('rejects invalid full-count grants and keeps zero grants closed',()=>{
  for(const W of [-1,Infinity,NaN])expect(()=>liftedWorkBudget(W,true)).toThrow(RangeError)
  expect(liftedDeadline(42,100,liftedWorkBudget(0,true).caseUnits)).toBe(42)
 })
})
