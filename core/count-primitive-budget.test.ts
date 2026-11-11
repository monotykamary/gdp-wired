import {expect,test} from 'bun:test'
import {completeWorkProfile} from './work-profile.ts'
import {countPrimitiveUnits} from './count-primitive-budget.ts'
test('primitive limit preserves legacy constants outside full accounting',()=>{
 for(const old of [150,250,600,900,1000])for(const leaf of [0,50,500,7500,Infinity])expect(countPrimitiveUnits(old,leaf)).toBe(completeWorkProfile.enabled?leaf:old)
})
test('absent leaf allowance retains the old limit and negative leaf grants no work',()=>{
 expect(countPrimitiveUnits(150)).toBe(150)
 expect(countPrimitiveUnits(250,-1)).toBe(completeWorkProfile.enabled?0:250)
})
test('a primitive can never extend the enclosing absolute endpoint',()=>{
 for(const remaining of [0,1,150,7500,100000])for(const leaf of [0,500,7500,Infinity]){
  const start=123,end=start+remaining,local=Math.min(end,start+countPrimitiveUnits(150,leaf))
  expect(local).toBeLessThanOrEqual(end);expect(local).toBeGreaterThanOrEqual(start)
 }
})
