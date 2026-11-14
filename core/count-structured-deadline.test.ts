// Direct-export cancellation regression. Use real native refusals at legal
// scope boundaries, never raw counter writes past a stricter child allowance.
import {expect,mock,test} from 'bun:test'
import * as planning from './count-prerequisite-plan.ts'
import * as walls from './wall.ts'
import {admitCountedFamily} from './counts.ts'
import {rowCompositionFixture} from './count-row-composition.fixture.ts'
import {env} from './solver.ts'
import {workLedger} from './work-admission.ts'
import {compareWork,integerQuotient,workFromExact} from './work-amount.ts'
import {BudgetExpired,clock,fullRate,withBudget,withDeadline,withinDeadline} from '../kernel/prove.ts'
const original={...planning},wall={...walls}
let calls=0,expireAt=0,phaseId=0,mode:'first'|'second'|'local'='first'
const refuse=(site:string,owner:number):never=>{
 const left=workLedger.available();expect(left).not.toBeNull()
 const ticks=integerQuotient(left!,workLedger.weights.ticks)
 if(ticks)workLedger.start('ticks',Number(ticks),site)
 const before=workLedger.actual()
 try{workLedger.start('ticks',1,site)}catch(error){
  expect(error).toBeInstanceOf(BudgetExpired)
  const refusal=workLedger.capacityRefusal(error);expect(refusal).toBeDefined()
  expect(refusal!.limiting.some(endpoint=>endpoint.id===owner)).toBe(true)
  expect(refusal!.limiting.every(endpoint=>compareWork(before,workFromExact(endpoint.end))<=0)).toBe(true)
  expect(workLedger.actual()).toEqual(before);throw error
 }
 throw Error('exhausted endpoint admitted an extra tick')
}
void mock.module('./count-prerequisite-plan.ts',()=>({...original,countPrerequisiteSchedule:()=>{
 calls++
 return withDeadline(clock()+1,()=>refuse('optional planning subcap',workLedger.currentScope()!.id))
}}))
// The parent is live at these existing post-attempt checkpoints, after the
// planner's stricter child scopes have unwound. Exercise each fallback boundary.
void mock.module('./wall.ts',()=>({...wall,checkWall:(phase:string)=>{
 if(mode==='first'&&phase==='structured fallback'||mode==='second'&&phase==='structured fallback completion')
  return refuse('inherited planning phase',phaseId)
 return wall.checkWall(phase)
}}))
const flags={GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0',GDP_COUNT_STRATEGIES:'1',GDP_COUNT_TIERS:'1',GDP_COUNT_FINAL_DEFER_CHECKS:'1',GDP_COUNT_CLOSING_RESERVE:'1',GDP_COUNT_PREREQUISITES:'1',GDP_COUNT_ROW_DEFER_CHECKS:'1'}
for(const scenario of ['first','second','local'] as const)test(scenario+' structured fallback preserves the directly exported caller phase',()=>{
 const saved=Object.fromEntries(Object.keys(flags).map(key=>[key,env[key]])),prior=withinDeadline(Infinity)
 Object.assign(env,flags);calls=0;mode=scenario
 let returned:ReturnType<typeof admitCountedFamily>|undefined,error:unknown,rootEnd=0
 try{
  const {m,law,family}=rowCompositionFixture()
  try{withBudget(100000000,()=>{
   rootEnd=clock()+100000000/fullRate;expireAt=Math.ceil(clock())+500
   return withDeadline(expireAt,()=>{phaseId=workLedger.currentScope()!.id;returned=admitCountedFamily(m,[law],family,new Set(),clock()+10000);return returned})
  })}catch(caught){error=caught}
  expect(calls).toBe(scenario==='first'?1:2)
  expect(clock()).toBeLessThan(rootEnd)
  if(scenario==='local'){
   expect(clock()).toBeLessThan(expireAt);expect(error).toBeUndefined();expect(returned).toMatchObject({proven:false,why:'prerequisite planning budget'})
  }else{
   expect(clock()).toBeLessThanOrEqual(expireAt);expect(error).toBeInstanceOf(BudgetExpired);expect(returned).toBeUndefined()
   expect(workLedger.capacityRefusal(error)?.limiting.some(endpoint=>endpoint.id===phaseId)).toBe(true)
  }
  expect(withinDeadline(Infinity)).toBe(prior)
 }finally{for(const [key,value]of Object.entries(saved))if(value===undefined)delete env[key];else env[key]=value}
})
