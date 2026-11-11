import {expect,test} from 'bun:test'
import {Reader,type Trail} from '../kernel/reader.ts'
import {BudgetExpired,clock,withBudget,withDeadline} from '../kernel/prove.ts'
import {completeWorkProfile} from './work-profile.ts'
import {coreMeter} from './meter.ts'
import {rawWork} from './work-meter.ts'
const fullTest=completeWorkProfile.enabled?test:test.skip
const trail:Trail={get:()=>undefined,stamp:()=>0,size:()=>0,lin:()=>{throw Error('empty trail')}}
const reader=()=>new Reader({name:'reader endpoint',hyps:[]},trail)
fullTest('reader checkpoints stop an exhausted root before changing work',()=>{
 const r=reader()
 expect(()=>withBudget(0,()=>{
  coreMeter.tableCells++
  const before=rawWork()
  for(const visit of [()=>r.dec({x:1}),()=>r.linear({op:'var',name:'x'}),()=>r.truth({op:'=',a:{op:'var',name:'x'},b:{op:'const',value:0}}),()=>r.form({x:1}),()=>r.sync()])expect(visit).toThrow(BudgetExpired)
  expect(rawWork()).toEqual(before)
 })).toThrow(BudgetExpired)
})
fullTest('reader endpoint hooks do not promote a local deadline to root expiry',()=>{
 withBudget(100000,()=>withDeadline(clock(),()=>{
  expect(()=>reader().linear({op:'var',name:'x'})).not.toThrow()
 }))
})
fullTest('reader is usable with no endpoint after exceptional unwind',()=>{
 expect(()=>withBudget(0,()=>{coreMeter.tableCells++;reader().dec({x:1})})).toThrow(BudgetExpired)
 expect(()=>reader().dec({x:1})).not.toThrow()
})
