import {expect,test} from 'bun:test'
import {withDeferredCountRecovery,countedAttempts,cprof,type Tried} from './counts.ts'
import {type Machine,type Law,all,any,atMost,get,n,same,x} from './machine.ts'
import {checkCountedLaws} from '../kernel/kernel.ts'
import {clock,counted,fullRate,withWall} from '../kernel/prove.ts'

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

test('recovery readiness is checked after ordinary work, without spending a new allowance',()=>{
 let counted=true,calls=0
 const ordinary:Tried<number>={stuck:'unknown'}
 const wait=withDeferredCountRecovery(clock()+1000,defer=>{
  defer(()=>{calls++;return 1})
  return ordinary
 },()=>!counted)
 expect(wait).toBe(ordinary)
 expect(calls).toBe(0)
 const retry=withDeferredCountRecovery(clock()+1000,defer=>{
  defer(()=>{calls++;return 1})
  counted=false
  return ordinary
 },()=>!counted)
 expect(retry).toEqual({proof:1})
 expect(calls).toBe(1)
})

test('a successful counted attempt suppresses recovery deferred by a failed plain attempt',()=>{
 const events:string[]=[],ordinary:Tried<number>={stuck:'sat'}
 expect(withDeferredCountRecovery(clock()+1000,defer=>{
  events.push('plain');defer(()=>{events.push('recovery');return 2});return ordinary
 },()=>false)).toBe(ordinary)
 expect(withDeferredCountRecovery(clock()+1000,defer=>{
  events.push('counted');defer(()=>{events.push('recovery');return 2});return {proof:1}
 })).toEqual({proof:1})
 expect(events).toEqual(['plain','counted'])
})

test('focused recovery remains available when both ordinary passes fail',()=>{
 const events:string[]=[],ordinary:Tried<number>={stuck:'unknown'}
 withDeferredCountRecovery(clock()+1000,defer=>{
  events.push('plain');defer(()=>2);return ordinary
 },()=>false)
 const result=withDeferredCountRecovery(clock()+1000,defer=>{
  events.push('counted');defer(()=>{events.push('recovery');return 2});return ordinary
 })
 expect(result).toEqual({proof:2})
 expect(events).toEqual(['plain','counted','recovery'])
})

test('a certified counterexample cannot be rescued by a proof under the same family',()=>{
 let calls=0
 const ordinary:Tried<number>={stuck:'sat',refuted:true}
 expect(withDeferredCountRecovery(clock()+1000,defer=>{defer(()=>{calls++;return 1});return ordinary})).toBe(ordinary)
 expect(calls).toBe(0)
})

test('ordinary counted reasoning gets a chance before finite-input recovery',()=>{
 const m:Machine={name:'constant finite count',params:[],inputs:['action'],inputMaps:['Input'],state:{value:n(0)},
  counts:{Rows:{j:'row',key:'member',below:n(2),body:n(1)}},
  assume:all(any(...[0,1,2].map(i=>same(x('action'),n(i))))),step:{state:{value:get('Rows',n(0))}}}
 const law:Law={name:'bounded',holds:atMost(x('value'),n(2))},family=[law]
 withWall(performance.now()+5000,()=>counted(fullRate,()=>{
  const attempts=countedAttempts(m,[],new Set(),clock()+5000),before=cprof.focused??0
  // Production family admission enables bounded widening after a narrow model.
  attempts.houdini=true
  const plain=attempts.traced(law,family,0,1000)
  expect('proof' in plain).toBe(false)
  expect(cprof.focused??0).toBe(before)
  const recovered=attempts.traced(law,family,1,3000)
  expect('proof' in recovered).toBe(true)
  if('proof' in recovered)expect(checkCountedLaws(m,family,{instances:{[law.name]:recovered.proof.instances},certs:recovered.proof.certs})).toBe(true)
  expect(cprof.focused??0).toBe(before)
 },true))
})

test('an ordinary failure without a recovery proposal is unchanged',()=>{
 const ordinary:Tried<{}>={stuck:'unknown'}
 expect(withDeferredCountRecovery(clock()+1000,()=>ordinary)).toBe(ordinary)
})
