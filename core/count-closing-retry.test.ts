import {expect,test} from 'bun:test'
import {claimCountClosingFallback} from './count-recipe-controller.ts'

test('closing fallback shares the persistent supplier-repair retry and defers actual transport declines',()=>{
 const fresh={supplierRepairUsed:false}
 expect(claimCountClosingFallback(fresh,true)).toBe(false)
 expect(fresh.supplierRepairUsed).toBe(false)
 expect(claimCountClosingFallback(fresh,false)).toBe(true)
 expect(fresh.supplierRepairUsed).toBe(true)
 expect(claimCountClosingFallback(fresh,false)).toBe(false)
 expect(claimCountClosingFallback(fresh,true)).toBe(false)
 const repaired={supplierRepairUsed:true}
 expect(claimCountClosingFallback(repaired,false)).toBe(false)
 expect(claimCountClosingFallback(repaired,true)).toBe(false)
 expect(repaired.supplierRepairUsed).toBe(true)
})
