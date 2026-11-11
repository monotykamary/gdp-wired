// Isolated test process: mock untrusted planning/proposal producers. The real
// counted pipeline and its final checkCountedLaws must decide acceptance.
import {expect,test,mock} from 'bun:test'
import {type Law,type Machine,get,n,same,x} from './machine.ts'
import {admitCountedFamily,certFor,countsDump} from './counts.ts'
import * as strategies from './count-strategies.ts'
import * as planning from './count-prerequisite-plan.ts'
import {checkCountedLaws,countedObligations,mcGoal} from '../kernel/kernel.ts'
import {clock,counted,fullRate,grow} from '../kernel/prove.ts'
import {finishCountStrategy,type CountStrategyProof} from './count-strategy.ts'
import {familyStepProposal,finalCountStepDeferralEnabled} from './count-final-step.ts'
test('the actual counted pipeline never publishes an unchecked invalid family',()=>counted(fullRate,()=>{
 expect(finalCountStepDeferralEnabled()).toBe(true)
 const m:Machine={name:'public closure',params:[],inputs:[],state:{},maps:{tokens:0},counts:{total:{j:'row',key:'member',below:n(1),body:{op:'if',c:same(get('tokens',x('member')),n(1)),then:n(1),else:n(0)}}},step:{}}
 const law:Law={name:'natural count',forall:'r',holds:{op:'<=',a:n(0),b:get('total',x('r'))}},family=[law],instances={[law.name]:[x('r#')]},until=clock()+100000
 const step=countedObligations(m,family,{[law.name]:instances},0).at(-1)!,request=certFor(step.goal,step.decls,false,0),goal=mcGoal(step.goal.hyps,step.decls,request)!,out=grow(goal,new Map(),{nodes:0,until})
 if(!('tree'in out))throw Error('public fixture failed')
 const valid=finishCountStrategy(m,family,law,instances,'total',{...request,tree:out.tree},until,(g,ds)=>certFor(g,ds,false,0),undefined,{familyProposal:familyStepProposal})!
 expect(valid.status).toBe('unchecked')
 let proposal:CountStrategyProof=structuredClone(valid)
 const original={...strategies},planner={...planning},events:Record<string,unknown>[]=[];let calls=0
 // The supplied factory is synchronous; the test process owns these bindings.
 void mock.module('./count-strategies.ts',()=>({...original,selectedCountStrategies:()=>family,prepareCountStrategyMachine:(machine:Machine)=>machine,proposeCountStrategiesForClosing:()=>{calls++;return proposal}}))
 void mock.module('./count-prerequisite-plan.ts',()=>({...planner,countPrerequisiteSchedule:()=>({requirements:new Map(),recipes:new Map(family.map(member=>[member.name,[{id:'fixture',kind:'strategy' as const,required:[]}]])),costs:new Map(family.map(member=>[member.name,0]))})}))
 const previous=countsDump.on;countsDump.on=e=>events.push(e as Record<string,unknown>)
 try{
  const run=()=>admitCountedFamily(m,family,family,new Set(),clock()+100000)
  const good=run();expect(good.proven).toBe(true);expect(good.proof).toBeDefined();expect(calls).toBeGreaterThan(0)
  expect(events.some(e=>e.phase==='count-strategy-result'&&e.status==='unchecked'&&e.checked===false)).toBe(true)
  expect(checkCountedLaws(good.m,good.laws,good.proof!)).toBe(true)
  expect(events.some(e=>e.phase==='closed-family'&&e.checked===true)).toBe(true)
  const mutations:((p:CountStrategyProof)=>void)[]=[p=>{p.certs[law.name+' @step']!.tree={leaf:[]}},p=>{delete p.certs[law.name+' @start']},p=>{p.certs[law.name+' @start']!.tree={leaf:[]}},p=>{p.certs[law.name+' @step']!.reads[0]![1]='absent'},p=>{p.certs[law.name+' @start']!.insts[0]!.wit='tokens'}]
  for(const mutate of mutations){proposal=structuredClone(valid);mutate(proposal);events.length=0;const before=calls,bad=run();expect(calls).toBeGreaterThan(before);expect(bad.proven).toBe(false);expect(events.some(e=>e.phase==='count-strategy-result'&&e.status==='unchecked'&&e.checked===false)).toBe(true);expect(events.some(e=>e.phase==='closed-family'&&e.checked===true)).toBe(false)}
 }finally{countsDump.on=previous;mock.restore()}
},true))
