import {expect,test} from 'bun:test'
import {countedAttempts,countsDump} from './counts.ts'
import {countTierBudget} from './count-tier-budget.ts'
import {BudgetExpired,checkBudget,clock,counted,fullRate,withBudget} from '../kernel/prove.ts'
import {workLedger} from './work-admission.ts'
import {completeWorkProfile} from './work-profile.ts'
import {type Law,type Machine,n,x} from './machine.ts'
const fullTest=completeWorkProfile.enabled?test:test.skip
const m:Machine={name:'expiry recipe',params:[],inputs:[],state:{},maps:{A:0},counts:{Total:{j:'row',key:'key',below:n(2),body:{op:'get',map:'A',key:x('key')}}},step:{maps:{A:{key:n(0),value:n(1)}}}}
const law:Law={name:'count remains empty',holds:{op:'=',a:{op:'get',map:'Total',key:n(0)},b:n(0)}}
function run(parent:boolean){
 const previous=countsDump.on
 let sawNative=false
 // A zero parent must fail at native admission, before any local catch can swallow it.
 try{return counted(fullRate,()=>withBudget(parent?0:1e7,()=>{
  const end=clock()+1000,tiers=countTierBudget(clock()-4000,end,1)
  const attempt=countedAttempts(m,[law],new Set(),end,true,true,tiers,undefined,[law])
  countsDump.on=event=>{if('phase'in event&&event.phase==='query'&&!sawNative){
   sawNative=true
   // A genuine strict child refusal, not a raw counter write or manufactured exception.
   withBudget(0,()=>{
    try{workLedger.start('ticks',1,'recipe native cutoff')}catch(error){
     expect(error).toBeInstanceOf(BudgetExpired);expect(workLedger.capacityRefusal(error)).toBeDefined();throw error
    }
   })
  }}
  const result=attempt.traced(law,[law],0,10)
  expect(sawNative).toBe(true);checkBudget('recipe parent survives');return result
 }),true)}finally{countsDump.on=previous}
}
fullTest('the prerequisite path preserves a native local expiry as typed unknown',()=>{
 expect(run(false)).toMatchObject({stuck:'unknown',expired:true})
})
fullTest('the prerequisite path never turns inherited cancellation into local unknown',()=>{
 expect(()=>run(true)).toThrow(BudgetExpired)
})
