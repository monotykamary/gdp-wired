import {expect,spyOn,test} from 'bun:test'
import {discover} from './discover.ts'
import {nat,proveRule,rule,type Verdict} from './dsl.ts'
import {BudgetExpired,checkBudget,checkWorkEndpoint,withBudget} from '../kernel/prove.ts'
import {WatchdogExpired,checkWatchdog,withSearchWatchdog} from './search-watchdog.ts'
import {costs} from './solver.ts'
import {completeWorkProfile} from './work-profile.ts'
import {workLedger} from './work-admission.ts'

const fixture=()=>{
 const r=rule('discovery scope control').inputs({n:nat}).state({x:0}).step(({n})=>({x:n}))
 return {r,law:r.law('nonnegative',({x})=>x.atLeast(0))}
}
const pause=()=>{Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0,25)}

test('standalone discovery owned watchdog stops separately and keeps initial diagnostic context',()=>{
 const {r,law}=fixture()
 // A diagnostic-only preflight fixture, never accepted as proof evidence.
 const first:Verdict={proven:false,checked:false,stuck:'SAT',goal:'original goal',witness:{n:7},why:'preflight witness'}
 const out=discover(r,[law],[],first,{work:20_000,watchdogMs:0})
 expect(out.verdict).toMatchObject({proven:false,checked:false,stopped:true,termination:{kind:'wall-deadline'},context:{goal:'original goal',stuck:'SAT',witness:{n:7},why:'preflight witness'}})
 expect(out.rule).toBe(r)
 expect(out.found).toEqual({})
 expect(()=>checkWatchdog('restored')).not.toThrow()
})

test('missing or longer child watchdog cannot renew an expired discovery owner',()=>{
 for(const watchdogMs of [undefined,60_000]){
  const {r,law}=fixture()
  let childEntered=false,returnedAfterChild=false
  const original=r.withSumsOf.bind(r)
  const hook=spyOn(r,'withSumsOf').mockImplementation((...args)=>{childEntered=true;pause();return original(...args)})
  try{
   expect(()=>withSearchWatchdog(10,()=>{
    discover(r,[law],[],undefined,{work:20_000,...(watchdogMs===undefined?{}:{watchdogMs})})
    returnedAfterChild=true
   })).toThrow(WatchdogExpired)
   expect(childEntered).toBe(true)
   expect(returnedAfterChild).toBe(false)
  }finally{hook.mockRestore()}
 }
 expect(()=>checkWatchdog('restored')).not.toThrow()
})

test('discovery work owner throws inside the public child rather than only at scope completion',()=>{
 const {r,law}=fixture()
 let childEntered=false,returnedAfterChild=false
 const original=r.withSumsOf.bind(r)
 const hook=spyOn(r,'withSumsOf').mockImplementation((...args)=>{
  childEntered=true
  if(completeWorkProfile.enabled)workLedger.start('ticks',10_001)
  else costs.fm+=10_001
  return original(...args)
 })
 try{
  expect(()=>withBudget(10,()=>{
   discover(r,[law],[],undefined,{work:20_000,watchdogMs:60_000})
   returnedAfterChild=true
  })).toThrow(BudgetExpired)
  expect(childEntered).toBe(true)
  expect(returnedAfterChild).toBe(false)
 }finally{hook.mockRestore()}
 expect(()=>checkWorkEndpoint('restored')).not.toThrow()
})

test('owned discovery watchdog can stop after child entry without poisoning a healthy parent',()=>{
 const {r,law}=fixture()
 let childEntered=false
 const original=r.withSumsOf.bind(r)
 const hook=spyOn(r,'withSumsOf').mockImplementation((...args)=>{childEntered=true;pause();return original(...args)})
 try{
  withSearchWatchdog(60_000,()=>{
   const out=discover(r,[law],[],undefined,{work:20_000,watchdogMs:10})
   expect(childEntered).toBe(true)
   expect(out.verdict).toMatchObject({proven:false,checked:false,stopped:true,termination:{kind:'wall-deadline'}})
   expect(()=>checkWatchdog('parent healthy')).not.toThrow()
  })
 }finally{hook.mockRestore()}
})

test('completed discovery evidence survives a late own watchdog observer, never an expired ancestor',()=>{
 for(const ancestor of [false,true]){
  const {r,law}=fixture()
  // Use a genuine checked public proof; no manufactured acceptance bits.
  const completed=proveRule(r,[law],{search:false})
  expect(completed).toMatchObject({proven:true,checked:true})
  let childEntered=false,returnedAfterChild=false,reads=0
  const hook=spyOn(r,'withSumsOf').mockImplementation(()=>{childEntered=true;return r})
  const lastHealthyRead=ancestor?6:4
  const now=spyOn(performance,'now').mockImplementation(()=>++reads<=lastHealthyRead?0:100)
  try{
   if(ancestor){
    expect(()=>withSearchWatchdog(10,()=>{
     discover(r,[law],[],completed,{work:20_000,watchdogMs:60_000})
     returnedAfterChild=true
    })).toThrow(WatchdogExpired)
    expect(childEntered).toBe(true)
    expect(returnedAfterChild).toBe(false)
   }else{
    const out=discover(r,[law],[],completed,{work:20_000,watchdogMs:10})
    expect(childEntered).toBe(true)
    expect(out.verdict).toBe(completed)
    expect(out.verdict.termination).toBeUndefined()
   }
   expect(reads).toBeGreaterThan(lastHealthyRead)
  }finally{now.mockRestore();hook.mockRestore()}
 }
})

test('a watchdog expiring after actual BudgetExpired cannot relabel work during inner recovery',()=>{
 for(const ancestor of [false,true]){
  const {r,law}=fixture()
  let childEntered=false,returnedAfterChild=false,time=0,actualWorkError:BudgetExpired|undefined
  const now=spyOn(performance,'now').mockImplementation(()=>time)
  const hook=spyOn(r,'withSumsOf').mockImplementation(()=>{
   childEntered=true
   try{
    if(completeWorkProfile.enabled)workLedger.start('ticks',10_001)
    else costs.fm+=10_001
    checkBudget('actual discovery child work stop')
   }catch(error){
    if(error instanceof BudgetExpired){actualWorkError=error;time=100}
    throw error
   }
   return r
  })
  try{
   const child=()=>discover(r,[law],[],undefined,{work:10,watchdogMs:ancestor?60_000:10})
   if(ancestor){
    expect(()=>withSearchWatchdog(10,()=>{
     child()
     returnedAfterChild=true
    })).toThrow(WatchdogExpired)
    expect(returnedAfterChild).toBe(false)
   }else{
    const out=child()
    expect(out.verdict).toMatchObject({proven:false,checked:false,stopped:true,termination:{kind:'work-exhausted',phase:actualWorkError?.phase}})
    expect(out.verdict.why).toMatch(/^work budget/)
   }
   expect(childEntered).toBe(true)
   expect(actualWorkError).toBeInstanceOf(BudgetExpired)
   expect(time).toBe(100)
  }finally{now.mockRestore();hook.mockRestore()}
 }
})

test('an owned discovery watchdog cannot hide exhausted ancestor work before child return',()=>{
 const {r,law}=fixture()
 let childEntered=false,returnedAfterChild=false,time=0,lateWatchdogReads=0
 const now=spyOn(performance,'now').mockImplementation(()=>{if(time===100)lateWatchdogReads++;return time})
 const hook=spyOn(r,'withSumsOf').mockImplementation(()=>{
  childEntered=true
  if(completeWorkProfile.enabled)workLedger.start('ticks',10_001)
  else costs.fm+=10_001 // default mode must reach the own-watchdog-first path
  time=100
  return r
 })
 try{
  expect(()=>withBudget(10,()=>{
   discover(r,[law],[],undefined,{work:20_000,watchdogMs:10})
   returnedAfterChild=true
  })).toThrow(BudgetExpired)
  expect(childEntered).toBe(true)
  expect(returnedAfterChild).toBe(false)
  if(!completeWorkProfile.enabled)expect(lateWatchdogReads).toBeGreaterThan(0)
 }finally{now.mockRestore();hook.mockRestore()}
 expect(()=>checkWorkEndpoint('restored')).not.toThrow()
})
