import {expect,spyOn,test} from 'bun:test'
import {nat,proveRule,proveSteps,rule} from './dsl.ts'
import {BudgetExpired,checkBudget,checkWorkEndpoint,withBudget} from '../kernel/prove.ts'
import {costs} from './solver.ts'
import {completeWorkProfile} from './work-profile.ts'
import {workLedger} from './work-admission.ts'

const fixture=()=>{
 const r=rule('public budget owner').inputs({n:nat}).state({x:0}).step(({n})=>({x:n}))
 return {r,law:r.law('natural',({x})=>x.atLeast(0))}
}
const charge=()=>{if(completeWorkProfile.enabled)workLedger.start('ticks',10_001);else costs.fm+=10_001}

for(const mode of ['rule','steps'] as const){
 test(`${mode} preserves actual work cause when its own watchdog expires before recovery`,()=>{
  const {r,law}=fixture()
  let childEntered=false,time=0,lateWatchdogReads=0,actualWorkError:BudgetExpired|undefined
  const now=spyOn(performance,'now').mockImplementation(()=>{if(time===100)lateWatchdogReads++;return time})
  const hook=spyOn(r,'withSumsOf').mockImplementation(()=>{
   childEntered=true
   try{charge();checkBudget('actual public child work stop')}
   catch(error){if(error instanceof BudgetExpired){actualWorkError=error;time=100}throw error}
   return r
  })
  try{
   const opts={search:{work:10},watchdogMs:10}
   const out=mode==='rule'?proveRule(r,[law],opts):proveSteps(r,[law],[],opts)
   expect(childEntered).toBe(true)
   expect(actualWorkError).toBeInstanceOf(BudgetExpired)
   expect(lateWatchdogReads).toBeGreaterThan(0)
   expect(out).toMatchObject({proven:false,checked:false,stopped:true,termination:{kind:'work-exhausted',phase:actualWorkError?.phase}})
   expect(out.why).toMatch(/^work budget/)
  }finally{now.mockRestore();hook.mockRestore()}
  expect(()=>checkWorkEndpoint('restored')).not.toThrow()
 })

 test(`${mode} own watchdog cannot return through exhausted ancestor work`,()=>{
  for(const explicitWork of [false,true]){
   const {r,law}=fixture()
   let childEntered=false,returnedAfterChild=false,time=0,lateWatchdogReads=0
   const now=spyOn(performance,'now').mockImplementation(()=>{if(time===100)lateWatchdogReads++;return time})
   const hook=spyOn(r,'withSumsOf').mockImplementation(()=>{childEntered=true;charge();time=100;return r})
   try{
    expect(()=>withBudget(10,()=>{
     // The implicit case isolates outer watchdog recovery: no child
     // withBudget completion guard may save a missing ancestor recheck.
     const opts={search:explicitWork?{work:20_000}:false as const,watchdogMs:10}
     if(mode==='rule')proveRule(r,[law],opts)
     else proveSteps(r,[law],[],opts)
     returnedAfterChild=true
    })).toThrow(BudgetExpired)
    expect(childEntered).toBe(true)
    expect(returnedAfterChild).toBe(false)
    // Complete-ledger admission may refuse earlier; normal mode must really
    // traverse the owned-watchdog-first bug path, not just any outer failure.
    if(!completeWorkProfile.enabled)expect(lateWatchdogReads).toBeGreaterThan(0)
   }finally{now.mockRestore();hook.mockRestore()}
   expect(()=>checkWorkEndpoint('restored')).not.toThrow()
  }
 })
}
