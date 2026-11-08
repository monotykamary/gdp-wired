import {expect,test} from 'bun:test'
import {withDeferredCountRecovery,type Tried} from './counts.ts'
import {clock} from '../kernel/prove.ts'

test('ordinary checked proposals take priority over deferred count recovery',()=>{
 const events:string[]=[],proof={ordinary:true}
 const result=withDeferredCountRecovery(clock()+1000,defer=>{
  defer(()=>{events.push('recovery');return {ordinary:false}})
  events.push('ordinary')
  return {proof}
 })
 expect(result).toEqual({proof})
 expect(events).toEqual(['ordinary'])
})

test('an unsuccessful ordinary attempt can recover within its remaining allowance',()=>{
 const events:string[]=[],proof={recovered:true}
 const result=withDeferredCountRecovery(clock()+1000,defer=>{
  defer(()=>{events.push('recovery');return proof})
  events.push('ordinary')
  return {stuck:'unknown'}
 })
 expect(result).toEqual({proof})
 expect(events).toEqual(['ordinary','recovery'])
})

test('failed recovery preserves the exact ordinary result, including a model outcome',()=>{
 const ordinary:Tried<{}>={stuck:'sat'}
 const result=withDeferredCountRecovery(clock()+1000,defer=>{defer(()=>undefined);return ordinary})
 expect(result).toBe(ordinary)
})

test('expired attempts never borrow a fresh recovery allowance',()=>{
 let called=false
 const ordinary:Tried<{}>={stuck:'unknown'}
 const result=withDeferredCountRecovery(clock()-1,defer=>{defer(()=>{called=true;return {}});return ordinary})
 expect(result).toBe(ordinary)
 expect(called).toBe(false)
})

test('deferred recovery uses only the latest warmed proposal context',()=>{
 const events:string[]=[]
 const result=withDeferredCountRecovery(clock()+1000,defer=>{
  defer(()=>{events.push('cold');return 1})
  defer(()=>{events.push('warm');return 0})
  return {stuck:'sat'}
 })
 expect(result).toEqual({proof:0})
 expect(events).toEqual(['warm'])
})

test('an ordinary failure without a recovery proposal is unchanged',()=>{
 const ordinary:Tried<{}>={stuck:'unknown'}
 expect(withDeferredCountRecovery(clock()+1000,()=>ordinary)).toBe(ordinary)
})
