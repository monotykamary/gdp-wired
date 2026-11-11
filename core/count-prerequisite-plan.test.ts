import {expect,test} from 'bun:test'
import {countPrerequisitePlan,countPrerequisiteSchedule} from './count-prerequisite-plan.ts'
import {countPrerequisiteComponents} from './count-prerequisite-components.ts'
import {rowCompositionFixture} from './count-row-composition.fixture.ts'
import {admitCountedFamily,countedAttempts,countsDump} from './counts.ts'
import {checkCountedLaws} from '../kernel/kernel.ts'
import {env} from './solver.ts'
import {clock,counted,fullRate,withWall} from '../kernel/prove.ts'
import {type Law,n,same,x} from './machine.ts'
import {completeWorkProfile} from './work-profile.ts'
const integration=completeWorkProfile.enabled?test:test.skip
const flags={GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0',GDP_COUNT_STRATEGIES:'1',GDP_COUNT_TIERS:'1',GDP_COUNT_FINAL_DEFER_CHECKS:'1',GDP_COUNT_CLOSING_RESERVE:'1',GDP_COUNT_PREREQUISITES:'1',GDP_COUNT_ROW_DEFER_CHECKS:'1'}
function enabled<T>(body:()=>T):T{
 const saved=Object.fromEntries(Object.keys(flags).map(key=>[key,env[key]]))
 Object.assign(env,flags)
 try{return body()}finally{for(const [key,value]of Object.entries(saved))if(value===undefined)delete env[key];else env[key]=value}
}
test('optional row pool is not promoted into required edges under renamed labels',()=>enabled(()=>{
 const {m,law,family}=rowCompositionFixture(),marker=family[2]!
 law.name='arbitrary target';marker.name='arbitrary prior'
 const before=JSON.stringify([m,family]),plan=countPrerequisitePlan(m,family,new Set([law]),clock()+1000)
 expect(plan.get(law.name)).toEqual([]);expect(JSON.stringify([m,family])).toBe(before)
 const queue=countPrerequisiteComponents([marker.name,law.name],plan,[law.name])
 expect(queue.next()).toMatchObject({kind:'attempt',name:marker.name})
 queue.finish(marker.name,[]);queue.commit([marker.name]);expect(queue.next()).toMatchObject({kind:'attempt',name:law.name})
}))
test('empty selection has no plan and does not dispatch by names',()=>{
 const {m,law,family}=rowCompositionFixture();law.name='K3 safety Q2 Inv3915'
 expect(countPrerequisitePlan(m,family,new Set(),clock()+1000).size).toBe(0)
})
integration('ordinary alternative explicitly bypasses a selected strategy on every attempt path',()=>enabled(()=>{
 const {m,law,family}=rowCompositionFixture(),events:Record<string,unknown>[]=[],prior=countsDump.on
 try{counted(fullRate,()=>withWall(performance.now()+8000,()=>{
  countsDump.on=e=>events.push(e as Record<string,unknown>)
  countedAttempts(m,[law],new Set(),clock()+5000,true,new Set([law])).traced(law,family,0,2000,false)
 }))}finally{countsDump.on=prior}
 expect(events.some(e=>e.phase==='count-strategy'||e.phase==='count-strategy-result')).toBe(false)
}),12000)
integration('prerequisite-first native fixture reaches the unchanged final family check',()=>enabled(()=>{
 const {m,law,family}=rowCompositionFixture(),events:Record<string,unknown>[]=[],prior=countsDump.on
 try{counted(fullRate,()=>withWall(performance.now()+8000,()=>{
  countsDump.on=e=>events.push(e as Record<string,unknown>)
  const out=admitCountedFamily(m,[law],family,new Set(),clock()+20000)
  expect(out.proven).toBe(true);expect(out.proof).toBeDefined()
  expect(checkCountedLaws(out.m,out.laws,out.proof!)).toBe(true)
  expect(events.some(e=>e.phase==='closed-family'&&e.checked===true)).toBe(true)
  expect(out.proof!.premises?.[law.name]).not.toContain(family[1]!.name)
  expect(events.some(e=>e.phase==='count-prerequisite-complete'&&e.law===law.name)).toBe(true)
 }))}finally{countsDump.on=prior}
}),12000)
integration('ordinary scope discovery closes a genuine mutual-induction component together',()=>enabled(()=>{
 const {m,family}=rowCompositionFixture(),prior=countsDump.on,events:Record<string,unknown>[]=[]
 m.state={left:n(0),right:n(0)};m.step.state={left:x('right'),right:x('left')}
 const left:Law={name:'left stays zero',holds:same(x('left'),n(0))},right:Law={name:'right stays zero',holds:same(x('right'),n(0))}
 try{counted(fullRate,()=>withWall(performance.now()+8000,()=>{
  countsDump.on=e=>events.push(e as Record<string,unknown>)
  const out=admitCountedFamily(m,[left],[left,right,...family],new Set(),clock()+20000)
  expect(out.proven).toBe(true);expect(checkCountedLaws(out.m,out.laws,out.proof!)).toBe(true)
  expect(out.proof!.premises?.[left.name]).toContain(right.name)
  expect(out.proof!.premises?.[right.name]).toContain(left.name)
  expect(events.some(e=>e.phase==='count-component-closed'&&(e.members as string[]).includes(left.name)&&(e.members as string[]).includes(right.name))).toBe(true)
  expect(events.some(e=>e.reason==='cycle')).toBe(false)
 }))}finally{countsDump.on=prior}
}),12000)
integration('production completes marker attempt before the dependent row can run',()=>enabled(()=>{
 const {m,law,family}=rowCompositionFixture(),marker=family[2]!,events:Record<string,unknown>[]=[],prior=countsDump.on,stop=new Error('after prerequisite order')
 try{counted(fullRate,()=>withWall(performance.now()+8000,()=>{
  countsDump.on=value=>{const e=value as Record<string,unknown>;events.push(e);if(e.phase==='count-tier-attempt'&&e.law===law.name)throw stop}
  expect(()=>admitCountedFamily(m,[law],family,new Set(),clock()+5000)).toThrow(stop)
 }))}finally{countsDump.on=prior}
 expect(events.some(e=>e.phase==='count-prerequisite-complete'&&e.law===marker.name)).toBe(true)
 const row=events.findIndex(e=>e.phase==='count-tier-attempt'&&e.law===law.name),ready=events.findIndex(e=>e.phase==='count-prerequisite-complete'&&e.law===marker.name)
 expect(ready).toBeLessThan(row)
}),12000)
integration('an unproven optional marker may be discovered but is never an accepted proof',()=>enabled(()=>{
 const {m,law,family}=rowCompositionFixture(),events:Record<string,unknown>[]=[],prior=countsDump.on
 m.step.maps!.marker={each:'r',value:n(1)}
 try{counted(fullRate,()=>withWall(performance.now()+8000,()=>{
  countsDump.on=e=>events.push(e as Record<string,unknown>)
  const result=admitCountedFamily(m,[law],family,new Set(),clock()+5000)
  expect(result.proven).toBe(false)
 }))}finally{countsDump.on=prior}
 expect(events.some(e=>e.phase==='closed-family')).toBe(false)
 const rows=events.filter(e=>e.phase==='count-component-attempt'&&e.law===law.name)
 expect(rows.length).toBeGreaterThan(0)
 const marker=family[2]!.name,results=events.filter(e=>e.phase==='count-component-result'&&e.law===marker)
 expect(results.length).toBeGreaterThan(0)
 expect(results.some(e=>e.held===true)).toBe(false)
 const failed=events.findIndex(e=>e.phase==='count-component-result'&&e.law===marker&&(e.outcome==='refuted'||e.outcome==='refused'))
 if(failed>=0)expect(events.slice(failed+1).filter(e=>e.phase==='count-component-attempt'&&e.law===law.name).every(e=>!(e.context as string[]).includes(marker))).toBe(true)
 else expect(results.every(e=>e.outcome==='unknown')).toBe(true)
}),12000)

test('recipe requirements and cost order are structural, not display-name dispatch',()=>enabled(()=>{
 const {m,law,family}=rowCompositionFixture(),selected=new Set([law])
 const first=countPrerequisiteSchedule(m,family,selected,clock()+1000)
 expect(first.recipes.get(law.name)?.[0]?.kind).toBe('strategy')
 expect(first.recipes.get(law.name)?.find(recipe=>recipe.kind==='ordinary')?.required).toBeUndefined()
 const costs=family.map(member=>first.costs.get(member.name))
 family.forEach((member,index)=>{member.name='renamed '+index})
 const second=countPrerequisiteSchedule(m,family,selected,clock()+1000)
 expect(family.map(member=>second.costs.get(member.name))).toEqual(costs)
}))
