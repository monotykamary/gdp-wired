import {expect,spyOn,test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {join} from 'node:path'
import {nat,proveRule,proveSteps,rule} from './dsl.ts'
import {discover} from './discover.ts'
import {inferLaws} from './infer.ts'
import {BudgetExpired,checkWorkEndpoint,inBudget,withBudget} from '../kernel/prove.ts'
import {costs} from './solver.ts'
import {completeWorkProfile} from './work-profile.ts'
import {workLedger} from './work-admission.ts'

for(const mode of ['public','steps','infer','discover']) test(`${mode} preserves exact native counts under scheduling delays`,()=>{
 const script=join(import.meta.dir,'../tools/counted-budget-audit/delay-probe.ts')
 const run=(delay:number)=>{
  const child=spawnSync(process.execPath,[script,mode],{encoding:'utf8',env:{...process.env,GDP_CYCLIC_LOG:'0',BUDGET_TEST_DELAY:String(delay)},timeout:120_000})
  expect(child.status,child.stderr).toBe(0)
  return JSON.parse(child.stdout.trim().split('\n').at(-1)!)
 }
 expect(run(5)).toEqual(run(0))
},300_000)

test('public work exhaustion is structured and mixed ms/work fails before entry',()=>{
 const r=rule('zero work').inputs({n:nat}).state({x:0}).step(({n})=>({x:n})),law=r.law('natural',({x})=>x.atLeast(0))
 for(const go of [()=>proveRule(r,[law],{search:{work:0}}),()=>proveSteps(r,[law],[],{search:{work:0}}),()=>discover(r,[law],[],undefined,{work:0}).verdict]){
  expect(go()).toMatchObject({proven:false,checked:false,stuck:'unknown',stopped:true,termination:{kind:'work-exhausted',scope:'search'}})
 }
 expect(()=>proveRule(r,[law],{search:{work:0,ms:0}})).toThrow('choose a work budget')
 expect(()=>inferLaws(r,[law],[],{work:0,timed:true})).toThrow('choose an explicit work budget')
})

test('child exhaustion leaves a larger parent usable, ancestor exhaustion propagates',()=>{
 const r=rule('nested work').inputs({n:nat}).state({x:0}).step(({n})=>({x:n})),law=r.law('natural',({x})=>x.atLeast(0))
 const charge=()=>completeWorkProfile.enabled?workLedger.start('ticks',10_001):costs.fm+=10_001
 const original=r.withSumsOf.bind(r)
 const hook=spyOn(r,'withSumsOf').mockImplementation((...args)=>{charge();return original(...args)})
 try{
  withBudget(1_000_000,()=>{
   expect(inBudget()).toBe(true)
   const child=proveRule(r,[law],{search:{work:10}})
   expect(child.termination?.kind).toBe('work-exhausted')
   expect(()=>checkWorkEndpoint('parent remains usable')).not.toThrow()
  })
  expect(()=>withBudget(10,()=>proveRule(r,[law],{search:{work:1_000_000}}))).toThrow(BudgetExpired)
 } finally {hook.mockRestore()}
 expect(inBudget()).toBe(false)
})
