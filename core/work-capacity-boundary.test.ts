import {expect,test} from 'bun:test'
import {BudgetExpired,workLedger,type WorkCapacityRefusal} from './work-admission.ts'
import {workAmount} from './work-amount.ts'
import {completeWorkProfile} from './work-profile.ts'
import {checkGoalLemmas,type LemmaCut} from '../kernel/kernel.ts'
const bounded=<T>(run:()=>T)=>workLedger.withBudget(workAmount(10n),run)
const refuse=():never=>{workLedger.start('ticks',11,'boundary probe');throw Error('expected refusal')}
test('capacity boundary observes no mutation of budgets, counters or epochs',()=>bounded(()=>{
 expect(completeWorkProfile.enabled).toBe(true)
 const before=workLedger.snapshot(),value={tag:'same object'}
 expect(workLedger.withCapacityRefusalBoundary(()=>value)).toBe(value)
 expect(workLedger.snapshot()).toEqual(before)
}))
test('capacity boundary preserves a swallowed genuine refusal and its exact provenance',()=>bounded(()=>{
 let original:unknown,caught:unknown,proof:WorkCapacityRefusal|undefined
 const before=workLedger.snapshot()
 try{workLedger.withCapacityRefusalBoundary(()=>{try{refuse()}catch(error){original=error;proof=workLedger.capacityRefusal(error)};return 'not a result'})}catch(error){caught=error}
 expect(original).toBeInstanceOf(BudgetExpired);expect(caught).toBe(original)
 expect(workLedger.capacityRefusal(caught)).toBe(proof);expect(proof).toBeDefined()
 expect(workLedger.snapshot()).toEqual(before)
}))
test('capacity boundary does not replace provenance with a later checker error',()=>bounded(()=>{
 let first:unknown,caught:unknown
 try{workLedger.withCapacityRefusalBoundary(()=>{try{refuse()}catch(error){first=error};throw new TypeError('checker caught and replaced refusal')})}catch(error){caught=error}
 expect(caught).toBe(first);expect(workLedger.capacityRefusal(caught)).toBeDefined()
}))
test('nested capacity boundaries retain the first refusal across both scopes',()=>bounded(()=>{
 let first:unknown,caught:unknown
 try{workLedger.withCapacityRefusalBoundary(()=>{try{workLedger.withCapacityRefusalBoundary(()=>{try{refuse()}catch(error){first=error};try{refuse()}catch{};return 1})}catch{};return 2})}catch(error){caught=error}
 expect(caught).toBe(first);expect(workLedger.capacityRefusal(caught)).toBeDefined()
}))
test('capacity boundaries do not invent provenance for arbitrary errors',()=>bounded(()=>{
 for(const original of [new BudgetExpired('external'),new TypeError('malformed')]){
  let caught:unknown;try{workLedger.withCapacityRefusalBoundary(()=>{throw original})}catch(error){caught=error}
  expect(caught).toBe(original);expect(workLedger.capacityRefusal(caught)).toBeUndefined()
 }
}))
test('unopted legacy catches and later clean boundaries remain unchanged',()=>bounded(()=>{
 const legacy=()=>{try{refuse()}catch{};return 7}
 expect(legacy()).toBe(7)
 expect(workLedger.withCapacityRefusalBoundary(()=>8)).toBe(8)
}))
test('capacity boundaries reject asynchronous callbacks and restore their stack',()=>bounded(()=>{
 expect(()=>workLedger.withCapacityRefusalBoundary(()=>Promise.resolve(1))).toThrow('must be synchronous')
 expect(workLedger.withCapacityRefusalBoundary(()=>9)).toBe(9)
}))
test('capacity boundary propagates genuine refusal swallowed inside unchanged kernel checking',()=>{
 const goal={name:'kernel-catch budget fixture',hyps:[]}
 const lemmas:LemmaCut[]=[{when:[],cut:{x:1},tree:{leaf:[]}}]
 // The unchanged kernel classifies malformed/checker failures as false.
 expect(workLedger.withBudget(workAmount(0n),()=>checkGoalLemmas(goal,{leaf:[]},lemmas))).toBe(false)
 let caught:unknown
 try{workLedger.withBudget(workAmount(0n),()=>workLedger.withCapacityRefusalBoundary(()=>checkGoalLemmas(goal,{leaf:[]},lemmas)))}catch(error){caught=error}
 expect(caught).toBeInstanceOf(BudgetExpired)
 const provenance=workLedger.capacityRefusal(caught)
 expect(provenance).toBeDefined();expect(provenance!.reason).toBe('quantum')
 expect(provenance!.limiting.some(endpoint=>endpoint.kind==='root')).toBe(true)
})
