import {expect,test} from 'bun:test'
import {withLemmas} from './effect.ts'
import {type Extraction} from './extract.ts'
import {nat,rule} from './dsl.ts'
import {BudgetExpired,checkWorkEndpoint,withBudget} from '../kernel/prove.ts'
import {WatchdogExpired,checkWatchdog,withSearchWatchdog} from './search-watchdog.ts'

const fixture=()=>{
 const r=rule('optional support scope').inputs({n:nat}).assume(({n})=>n.atMost(1)).state({x:0}).step(({n})=>({x:n}))
 const lemmas=[r.law('nonnegative support',({x})=>x.atLeast(0)),r.law('bounded support',({x})=>x.atMost(1))]
 return {rule:r,invariants:[],lemmas} as unknown as Extraction
}

test('per-lemma optional work stops retain actual verdicts and do not claim support',()=>{
 const x=fixture(),out=withLemmas(x,{work:0})
 expect(out.proven).toEqual([])
 expect(out.unproven).toEqual(['nonnegative support','bounded support'])
 expect(out.attempts).toHaveLength(2)
 for(const a of out.attempts)expect(a.verdict).toMatchObject({proven:false,checked:false,stopped:true,termination:{kind:'work-exhausted'}})
 expect(out.x.invariants).toEqual([])
})

test('owned per-lemma watchdog stops stay diagnostic data, not ancestor cancellation',()=>{
 withSearchWatchdog(60_000,()=>{
  const out=withLemmas(fixture(),{work:20_000,watchdogMs:0})
  expect(out.attempts).toHaveLength(2)
  expect(out.proven).toEqual([])
  for(const a of out.attempts)expect(a.verdict).toMatchObject({proven:false,checked:false,stopped:true,termination:{kind:'wall-deadline'}})
  expect(()=>checkWatchdog('owner still healthy')).not.toThrow()
 })
})

test('optional support cannot swallow an inherited work or watchdog expiry',()=>{
 const workFixture=fixture(),watchdogFixture=fixture()
 let returnedAfterWorkHelper=false,returnedAfterWatchdogHelper=false
 expect(()=>withBudget(0,()=>{
  withLemmas(workFixture,{work:20_000})
  returnedAfterWorkHelper=true
 })).toThrow(BudgetExpired)
 expect(returnedAfterWorkHelper).toBe(false)
 expect(()=>withSearchWatchdog(1,()=>{
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0,25)
  withLemmas(watchdogFixture,{work:20_000,watchdogMs:60_000})
  returnedAfterWatchdogHelper=true
 })).toThrow(WatchdogExpired)
 expect(returnedAfterWatchdogHelper).toBe(false)
 expect(()=>checkWatchdog('restored')).not.toThrow()
 expect(()=>checkWorkEndpoint('restored')).not.toThrow()
})

test('per-lemma caps preserve successful support and reject ambiguous options',()=>{
 const x=fixture(),out=withLemmas(x,{work:20_000})
 expect(out.proven).toEqual(['nonnegative support','bounded support'])
 expect(out.unproven).toEqual([])
 for(const a of out.attempts){expect(a.verdict).toMatchObject({proven:true,checked:true});expect(a.verdict?.termination).toBeUndefined()}
 expect(out.x.invariants).toHaveLength(2)
 expect(()=>withLemmas(x,{ms:0,work:0})).toThrow('choose a work budget')
})
