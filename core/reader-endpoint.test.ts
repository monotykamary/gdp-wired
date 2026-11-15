import {expect,test} from 'bun:test'
import {Reader,type Trail} from '../kernel/reader.ts'
import {BudgetExpired,withBudget} from '../kernel/prove.ts'
import {completeWorkProfile} from './work-profile.ts'
import {workLedger} from './work-admission.ts'
import {rawWork} from './work-meter.ts'
const fullTest=completeWorkProfile.enabled?test:test.skip
const trail:Trail={get:()=>undefined,stamp:()=>0,size:()=>0,lin:()=>{throw Error('empty trail')}}
const reader=()=>new Reader({name:'reader endpoint',hyps:[]},trail)
fullTest('reader work refuses an exhausted root before changing counters',()=>{
 const r=reader(),before=rawWork()
 expect(()=>withBudget(0,()=>{
  for(const visit of [()=>r.dec({x:1}),()=>r.linear({op:'var',name:'x'}),()=>r.truth({op:'=',a:{op:'var',name:'x'},b:{op:'const',value:0}}),()=>r.form({x:1})])expect(visit).toThrow(BudgetExpired)
  // Empty sync is a pure endpoint check; no refused charge is made sticky implicitly.
  expect(()=>r.sync()).not.toThrow();expect(rawWork()).toEqual(before)
  r.linear({op:'var',name:'x'})
 })).toThrow(BudgetExpired)
 expect(rawWork()).toEqual(before)
})
fullTest('reader local refusal does not promote the local deadline to root expiry',()=>{
 withBudget(100000,()=>{
  const root=workLedger.currentScope()!,before=rawWork()
  let error:unknown
  try{workLedger.withEndpoint('deadline',workLedger.actual(),()=>reader().linear({op:'var',name:'x'}))}catch(caught){error=caught}
  expect(error).toBeInstanceOf(BudgetExpired)
  const refusal=workLedger.capacityRefusal(error);expect(refusal).toBeDefined()
  expect(refusal!.limiting.every(endpoint=>endpoint.id!==root.id&&endpoint.kind==='deadline')).toBe(true)
  expect(rawWork()).toEqual(before)
  expect(()=>reader().linear({op:'var',name:'x'})).not.toThrow()
 })
})
fullTest('reader is usable with no endpoint after exceptional unwind',()=>{
 const before=rawWork()
 expect(()=>withBudget(0,()=>reader().dec({x:1}))).toThrow(BudgetExpired)
 expect(rawWork()).toEqual(before)
 expect(()=>reader().dec({x:1})).not.toThrow()
})
