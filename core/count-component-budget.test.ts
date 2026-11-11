import {expect,test} from 'bun:test'
import {countComponentAttemptBudget} from './count-component-budget.ts'
test('the first member can use the remaining pool except other members minimum floors',()=>{
 expect(countComponentAttemptBudget(10,100,2)).toEqual({end:99,allotted:89,reserved:1})
 expect(countComponentAttemptBudget(40,100,1)).toEqual({end:100,allotted:60,reserved:0})
})
test('small remaining pools are not rounded upward or silently starved',()=>{
 const tiny=countComponentAttemptBudget(0,0.3,3)
 expect(tiny.allotted).toBeCloseTo(0.1,12);expect(tiny.reserved).toBeCloseTo(0.2,12)
 expect(tiny.end).toBeLessThanOrEqual(0.3)
 expect(countComponentAttemptBudget(100,90,2)).toEqual({end:90,allotted:0,reserved:0})
})
test('unused work belongs to the same endpoint, never a renewed grant',()=>{
 const first=countComponentAttemptBudget(10,100,3),next=countComponentAttemptBudget(20,100,2)
 expect(first.end).toBe(98);expect(next.end).toBe(99)
 expect(countComponentAttemptBudget(100,100,1).allotted).toBe(0)
})
test('invalid caps and member counts are refused',()=>{
 expect(()=>countComponentAttemptBudget(0,Infinity,2)).toThrow(RangeError)
 expect(()=>countComponentAttemptBudget(0,10,0)).toThrow(RangeError)
 expect(()=>countComponentAttemptBudget(0,10,2,-1)).toThrow(RangeError)
})
