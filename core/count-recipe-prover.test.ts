// Isolated process: only proposal production and one semantic reduced replay
// refusal are controlled. Scope capture, full fallback and final checking stay real.
import {expect,mock,spyOn,test} from 'bun:test'
import {type Law,type Machine,n,same,x} from './machine.ts'
import {admitCountedFamily,countedAttempts,countsDump} from './counts.ts'
import * as strategies from './count-strategies.ts'
import * as planning from './count-prerequisite-plan.ts'
import * as scope from './count-proof-scope.ts'
import {checkCountedLaws} from '../kernel/kernel.ts'
import {clock,fullRate,withBudget,withWall} from '../kernel/prove.ts'
import {completeWorkProfile} from './work-profile.ts'
const fullTest=completeWorkProfile.enabled?test:test.skip
const left:Law={name:'left',holds:same(x('left'),n(0))},right:Law={name:'right',holds:same(x('right'),n(0))},noise:Law={name:'extra valid scope',holds:same(x('noise'),n(0))},family=[left,right,noise]
const machine:Machine={name:'funded full fallback',params:[],inputs:[],state:{left:n(0),right:n(0),noise:n(0)},step:{state:{left:x('right'),right:x('left'),noise:x('noise')}}}
const producer={...strategies},planner={...planning}
void mock.module('./count-strategies.ts',()=>({...producer,prepareCountStrategyMachine:(m:Machine)=>m,selectedCountStrategies:()=>family,
 proposeCountStrategiesForClosing:(m:Machine,context:Law[],law:Law,end:number)=>{
  const result=countedAttempts(m,[law],new Set(),end).traced(law,context,0,Math.max(0,end-clock()),false)
  return 'proof'in result?{...result.proof,status:'unchecked' as const,premises:context.map(law=>law.name)}:undefined
 }}))
void mock.module('./count-prerequisite-plan.ts',()=>({...planner,countPrerequisiteSchedule:()=>({requirements:new Map([[left.name,[right.name]],[right.name,[left.name]]]),recipes:new Map(family.map(law=>[law.name,[{id:'fixture',kind:'strategy' as const,required:law===left?[right.name]:law===right?[left.name]:[]}]])),costs:new Map(family.map((law,i)=>[law.name,i]))})}))
fullTest('prover: reduced refusal retains funded full-only unchecked scope through native closing',()=>{
 const saved=new Map<string,string|undefined>(),flags=['GDP_COUNT_STRATEGIES','GDP_COUNT_TIERS','GDP_COUNT_FINAL_DEFER_CHECKS','GDP_COUNT_CLOSING_RESERVE','GDP_COUNT_PREREQUISITES','GDP_COUNT_PROOF_GUIDED_SCHEDULING']
 for(const flag of flags){saved.set(flag,process.env[flag]);process.env[flag]='1'}
 const replay=spyOn(scope,'replayScopedCountProof'),events:Record<string,unknown>[]=[],previous=countsDump.on
 replay.mockImplementationOnce(()=>undefined);countsDump.on=event=>events.push(event as Record<string,unknown>)
 try{
  const result=withBudget(25000000,()=>withWall(clock()+25000000/fullRate,()=>admitCountedFamily(machine,[left],family,new Set(),clock()+25000000/fullRate)))
  expect(events.some(event=>event.phase==='count-component-rescope'&&event.stage==='canonical'&&event.checked===false)).toBe(true)
  expect(events.some(event=>event.phase==='count-component-rescope'&&event.stage==='original'&&event.checked===true)).toBe(true)
  const fullOnly=events.find(event=>event.phase==='count-recipe-result'&&event.outcome==='proposal'&&event.checkedReduced===false)
  expect(fullOnly).toBeDefined();expect(fullOnly!.premises).toContain(noise.name)
  expect(result.proven).toBe(true);expect(checkCountedLaws(result.m,result.laws,result.proof!)).toBe(true)
 }finally{replay.mockRestore();countsDump.on=previous;for(const [flag,value]of saved)if(value===undefined)delete process.env[flag];else process.env[flag]=value}
})
