// Direct-export cancellation regression; planner failures are untrusted search outcomes.
import {expect,mock,test} from 'bun:test'
import * as planning from './count-prerequisite-plan.ts'
import {admitCountedFamily} from './counts.ts'
import {rowCompositionFixture} from './count-row-composition.fixture.ts'
import {env,costs} from './solver.ts'
import {BudgetExpired,checkBudget,clock,fullRate,withBudget,withDeadline,withinDeadline} from '../kernel/prove.ts'
const original={...planning}
let calls=0,expireAt=0,mode:'first'|'second'|'local'='first'
const chargePast=(end:number)=>{costs.fm+=Math.max(1,Math.ceil((end-clock())*fullRate/2.33)+2)}
void mock.module('./count-prerequisite-plan.ts',()=>({...original,countPrerequisiteSchedule:()=>{
 calls++
 if(mode==='first'||mode==='second'&&calls===2){chargePast(expireAt);checkBudget('inherited planning phase');throw Error('phase did not expire')}
 return withDeadline(clock()+1,()=>{chargePast(withinDeadline(Infinity));checkBudget('optional planning subcap');throw Error('subcap did not expire')})
}}))
const flags={GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0',GDP_COUNT_STRATEGIES:'1',GDP_COUNT_TIERS:'1',GDP_COUNT_FINAL_DEFER_CHECKS:'1',GDP_COUNT_CLOSING_RESERVE:'1',GDP_COUNT_PREREQUISITES:'1',GDP_COUNT_ROW_DEFER_CHECKS:'1'}
for(const scenario of ['first','second','local'] as const)test(scenario+' structured fallback preserves the directly exported caller phase',()=>{
 const saved=Object.fromEntries(Object.keys(flags).map(key=>[key,env[key]])),fm=costs.fm,prior=withinDeadline(Infinity)
 Object.assign(env,flags);calls=0;mode=scenario
 let returned:ReturnType<typeof admitCountedFamily>|undefined,error:unknown,rootEnd=0
 try{
  const {m,law,family}=rowCompositionFixture()
  try{withBudget(100000000,()=>{
   rootEnd=clock()+100000000/fullRate;expireAt=clock()+500
   return withDeadline(expireAt,()=>{returned=admitCountedFamily(m,[law],family,new Set(),clock()+10000);return returned})
  })}catch(caught){error=caught}
  console.log('DIRECT_PHASE_RESULT '+JSON.stringify({fallback:scenario,calls,returned:returned&&{proven:returned.proven,why:returned.why},error:String(error),pastPhase:clock()>expireAt,beforeRoot:clock()<rootEnd}))
  expect(calls).toBe(scenario==='first'?1:2)
  expect(clock()).toBeLessThan(rootEnd)
  if(scenario==='local'){
   expect(clock()).toBeLessThan(expireAt);expect(error).toBeUndefined();expect(returned).toMatchObject({proven:false,why:'prerequisite planning budget'})
  }else{
   expect(clock()).toBeGreaterThan(expireAt);expect(error).toBeInstanceOf(BudgetExpired);expect(returned).toBeUndefined()
  }
  expect(withinDeadline(Infinity)).toBe(prior)
 }finally{costs.fm=fm;for(const [key,value]of Object.entries(saved))if(value===undefined)delete env[key];else env[key]=value}
})
