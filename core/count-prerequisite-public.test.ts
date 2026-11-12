// Isolated process: only untrusted scheduling/proposal producers are replaced.
// Every proof is built by the ordinary prover; the real final checker decides.
import {expect,mock,test} from 'bun:test'
import {type Law,type Machine,all,n,same,x} from './machine.ts'
import {admitCountedFamily,countedAttempts,countsDump} from './counts.ts'
import * as strategies from './count-strategies.ts'
import * as planning from './count-prerequisite-plan.ts'
import * as views from './count-premise-view.ts'
import {checkCountedLaws} from '../kernel/kernel.ts'
import {BudgetExpired,checkBudget,clock,counted,fullRate,withinDeadline,withBudget,withWall} from '../kernel/prove.ts'
import {costs} from './solver.ts'
import {scopeCountProof,replayScopedCountProof} from './count-proof-scope.ts'
import {compareWork,type WorkAmount} from './work-amount.ts'
let offeredScope=false
let alternatives=new Set<string>(),priority=new Map<string,number>(),selected:Law[]|undefined,interrupt:((event:Record<string,unknown>)=>void)|undefined
let decline:((target:Law)=>boolean)|undefined
let family:Law[]=[],requirements=new Map<string,readonly string[]>(),chooseSource:((target:Law,context:Law[])=>Law[])|undefined
const original={...strategies},planner={...planning},view={...views}
const proposeFixture=(m:Machine,context:Law[],target:Law,end:number)=>{
  if(decline?.(target))return undefined
  const source=chooseSource?.(target,context)??context
  const result=countedAttempts(m,[target],new Set(),end).traced(target,source,0,Math.max(0,end-clock()),false)
  if(!('proof'in result))return undefined
  if(source===context)return offeredScope?{...result.proof,status:'unchecked' as const,premises:context.map(law=>law.name)}:result.proof
  const scoped=scopeCountProof(m,target,source,result.proof,end)
  return scoped?replayScopedCountProof(m,context,scoped,end):undefined
}
void mock.module('./count-strategies.ts',()=>({...original,prepareCountStrategyMachine:(m:Machine)=>m,selectedCountStrategies:()=>selected??family,
 proposeCountStrategiesForClosing:proposeFixture,proposeCountStrategyKindForClosing:(_kind:'row'|'guard',m:Machine,context:Law[],target:Law,end:number)=>proposeFixture(m,context,target,end)}))
void mock.module('./count-prerequisite-plan.ts',()=>({...planner,countPrerequisiteSchedule:()=>({requirements,recipes:new Map(family.map(law=>[law.name,[...(selected&&!selected.includes(law)?[{id:'ordinary',kind:'ordinary' as const}]:[{id:'row',kind:'strategy' as const,required:requirements.get(law.name)??[]}]),...(alternatives.has(law.name)?[{id:'independent',kind:'ordinary' as const,required:[]}]:[])]])),costs:new Map(family.map((law,index)=>[law.name,priority.get(law.name)??index]))})}))
// Hold context selection fixed in this test so the optional subset optimizer
// cannot avoid the intentionally offered false outsider before it is exercised.
void mock.module('./count-premise-view.ts',()=>({...view,countPremiseContext:()=>undefined}))
function run(m:Machine,callers:Law[],work?:number){
 const events:Record<string,unknown>[]=[],previous=countsDump.on
 countsDump.on=e=>{events.push(e as Record<string,unknown>);interrupt?.(e as Record<string,unknown>)}
 const invoke=()=>withWall(work===undefined?performance.now()+15000:clock()+work/fullRate,()=>({out:admitCountedFamily(m,callers,family,new Set(),clock()+100000),events}))
 try{return counted(fullRate,()=>work===undefined?invoke():withBudget(work,invoke))}
 finally{countsDump.on=previous}
}
for(const unproved of [false,true])test('held and parked ordinary state survives structured fallback, unproved='+unproved,()=>{
 const ordinary:Law={name:'ordinary retained state',holds:same(x('ordinary'),n(0))},core:Law={name:'required core',holds:same(x('core'),n(0))}
 const m:Machine={name:'fallback memory',params:[],inputs:[],state:{ordinary:n(0),core:n(0)},step:{state:{ordinary:unproved?n(1):x('ordinary'),core:x('core')}}}
 family=[ordinary,core];selected=[core];requirements=new Map();alternatives=new Set();priority=new Map([[ordinary.name,0],[core.name,1]])
 let coreCalls=0;decline=target=>target===core&&++coreCalls===1
 try{
  const {out,events}=run(m,[core],25000000)
  expect(out.proven).toBe(true);expect(checkCountedLaws(out.m,out.laws,out.proof!)).toBe(true)
  const tries=events.filter(event=>event.phase==='count-component-attempt'&&event.law===ordinary.name)
  expect(tries).toHaveLength(1);expect(tries[0]?.purpose).toBe('discovery')
  expect(events.filter(event=>event.phase==='count-prerequisite-plan')).toHaveLength(2)
  if(unproved){
   const result=events.find(event=>event.phase==='count-component-result'&&event.law===ordinary.name)!
   expect(result.outcome).toBe('unknown');expect(result.failed).toEqual([])
  }else expect(events.filter(event=>event.phase==='count-prerequisite-memory').at(-1)?.held).toContain(ordinary.name)
 }finally{decline=undefined}
})
test('a conditional core remains uncommitted while its helper is unknown across fallback',()=>{
 const helper:Law={name:'parked helper',holds:same(x('helper'),n(0))},core:Law={name:'conditional core',holds:same(x('core'),n(0))}
 const m:Machine={name:'conditional fallback',params:[],inputs:[],state:{helper:n(0),core:n(0)},step:{state:{helper:n(1),core:x('helper')}}}
 family=[helper,core];selected=[core];requirements=new Map();alternatives=new Set();priority=new Map([[helper.name,0],[core.name,1]])
 const previous=costs.fm;let purpose=''
 try{
  interrupt=event=>{
   if(event.phase==='count-component-attempt')purpose=String(event.purpose)
   if(event.phase==='query'&&event.law===helper.name&&purpose==='required')withBudget(0,()=>{costs.fm++;checkBudget('unresolved helper child')})
  }
  const {out,events}=run(m,[core],25000000)
  expect(out.proven).toBe(false)
  expect(events.some(event=>event.phase==='count-component-result'&&event.law===core.name&&event.held===true&&(event.premises as string[]).includes(helper.name))).toBe(true)
  expect(events.filter(event=>event.phase==='count-prerequisite-plan')).toHaveLength(2)
  expect(events.filter(event=>event.phase==='count-prerequisite-memory').at(-1)?.held).toContain(core.name)
  expect(events.filter(event=>event.phase==='count-component-attempt'&&event.law===core.name)).toHaveLength(1)
  expect(events.some(event=>event.phase==='count-component-closed'&&(event.members as string[]).includes(core.name))).toBe(false)
  expect(events.some(event=>event.phase==='closed-family')).toBe(false)
 }finally{interrupt=undefined;costs.fm=previous}
})
test('a native-expired ordinary member joins the later core and is checked together',()=>{
 const left:Law={name:'later core',holds:same(x('left'),n(0))},right:Law={name:'expired ordinary',holds:same(x('right'),n(0))}
 const m:Machine={name:'expiry absorption',params:[],inputs:[],state:{left:n(0),right:n(0)},step:{state:{left:x('right'),right:x('left')}}}
 family=[right,left];selected=[left];requirements=new Map([[left.name,[right.name]]]);alternatives=new Set();priority=new Map([[right.name,0],[left.name,1]])
 const saved=costs.fm;let stopped=false
 interrupt=event=>{if(event.phase==='query'&&event.law===right.name&&!stopped){
  stopped=true;costs.fm+=Math.max(1,Math.ceil((withinDeadline(Infinity)-clock())*fullRate/2.33)+2)
  checkBudget('native ordinary expiry');throw new BudgetExpired('native ordinary expiry')
 }}
 try{
  const {out,events}=run(m,[left],25000000)
  expect(stopped).toBe(true)
  expect(events.some(event=>event.phase==='count-component-result'&&event.law===right.name&&event.outcome==='unknown'&&event.reason==='budget-expired'&&(event.failed as string[]).length===0)).toBe(true)
  expect(events.some(event=>event.phase==='count-component-attempt'&&event.law===right.name&&(event.component as string[]).length===2)).toBe(true)
  expect(events.some(event=>event.phase==='count-component-attempt'&&event.mode==='dissolve')).toBe(false)
  expect(out.proven).toBe(true);expect(checkCountedLaws(out.m,out.laws,out.proof!)).toBe(true)
 }finally{interrupt=undefined;costs.fm=saved}
})
test('a declared alternative may fail without declining the checked joint component',()=>{
 const left:Law={name:'mutual left',holds:same(x('left'),n(0))},right:Law={name:'mutual right',holds:same(x('right'),n(0))}
 const m:Machine={name:'mutual',params:[],inputs:[],state:{left:n(0),right:n(0)},step:{state:{left:x('right'),right:x('left')}}}
 alternatives=new Set([left.name]);priority=new Map();selected=undefined
 family=[left,right];requirements=new Map([[left.name,[right.name]],[right.name,[left.name]]]);chooseSource=undefined
 const {out,events}=run(m,[left])
 expect(events.some(e=>e.phase==='count-component-result'&&e.mode==='dissolve'&&e.held===false&&(e.failed as string[]).length===0)).toBe(true)
 expect(events.some(e=>e.phase==='count-component-attempt'&&e.mode==='joint')).toBe(true)
 expect(out.proven).toBe(true);expect(checkCountedLaws(out.m,out.laws,out.proof!)).toBe(true)
 expect(out.proof!.premises?.[left.name]).toContain(right.name)
 expect(out.proof!.premises?.[right.name]).toContain(left.name)
})
test('proof-guided admission checks and shrinks offers before expansion, then closes natively',()=>{
 const left:Law={name:'scoped left',holds:same(x('left'),n(0))},right:Law={name:'scoped right',holds:same(x('right'),n(0))},noise:Law={name:'unused false offer',holds:same(x('noise'),n(7))}
 const m:Machine={name:'generic checked offers',params:[],inputs:[],state:{left:n(0),right:n(0),noise:n(0)},step:{state:{left:x('right'),right:x('left')}}}
 family=[noise,left,right];selected=[left,right];requirements=new Map([[left.name,[right.name]],[right.name,[left.name]]]);alternatives=new Set();priority=new Map([[noise.name,0],[left.name,10],[right.name,11]]);chooseSource=undefined
 const previous=process.env.GDP_COUNT_PROOF_GUIDED_SCHEDULING
 process.env.GDP_COUNT_PROOF_GUIDED_SCHEDULING='1';offeredScope=true
 try{
  const {out,events}=run(m,[left],25000000)
  expect(out.proven).toBe(true);expect(checkCountedLaws(out.m,out.laws,out.proof!)).toBe(true)
  expect(out.laws).not.toContain(noise)
  expect(events.some(e=>e.phase==='count-component-rescope'&&e.stage==='original'&&e.checked===true)).toBe(false)
  expect(events.some(e=>e.phase==='count-component-rescope'&&e.stage==='canonical'&&e.checked===true)).toBe(true)
  const held=events.filter(e=>e.phase==='count-recipe-result'&&e.outcome==='proposal')
  expect(held).toHaveLength(2)
  expect(held.every(e=>e.checkedReduced===true&&!(e.premises as string[]).includes(noise.name))).toBe(true)
  const phases=events.filter(e=>e.phase==='count-recipe-admission').map(e=>(e.ancestors as {scope:string,remaining:WorkAmount}[]).at(-2)!.remaining)
  expect(phases.length).toBeGreaterThanOrEqual(2)
  expect(compareWork(phases[1]!,phases[0]!)).toBe(1)
  expect(events.some(e=>e.phase==='count-family-closing'&&e.stage==='end'&&e.checked===true)).toBe(true)
 }finally{
  offeredScope=false
  if(previous===undefined)delete process.env.GDP_COUNT_PROOF_GUIDED_SCHEDULING;else process.env.GDP_COUNT_PROOF_GUIDED_SCHEDULING=previous
 }
})

test('reachable screening precedes a required ordinary allowance and survives fallback',()=>{
 const bad:Law={name:'reachable ordinary',holds:same(x('noise'),n(0))},core:Law={name:'independent core',holds:same(x('core'),n(0))}
 const m:Machine={name:'generic required screen',params:[],inputs:[],state:{noise:n(0),core:n(0)},step:{state:{noise:n(1),core:x('core')}}}
 family=[bad,core];selected=[core];requirements=new Map([[core.name,[bad.name]]]);alternatives=new Set();priority=new Map([[bad.name,0],[core.name,1]])
 let calls=0;decline=target=>target===core&&++calls===1
 const previous=process.env.GDP_COUNT_PROOF_GUIDED_SCHEDULING;process.env.GDP_COUNT_PROOF_GUIDED_SCHEDULING='1'
 try{
  const {out,events}=run(m,[core],25000000)
  expect(out.proven).toBe(true);expect(checkCountedLaws(out.m,out.laws,out.proof!)).toBe(true)
  expect(events.some(e=>e.phase==='count-reachability'&&e.law===bad.name&&e.outcome==='rejected')).toBe(true)
  expect(events.some(e=>e.phase==='count-reachability-invalidated'&&(e.rejected as string[]).includes(bad.name))).toBe(true)
  expect(events.some(e=>e.phase==='count-component-attempt'&&e.law===bad.name&&e.purpose==='required')).toBe(false)
  expect(out.laws).not.toContain(bad)
 }finally{decline=undefined;if(previous===undefined)delete process.env.GDP_COUNT_PROOF_GUIDED_SCHEDULING;else process.env.GDP_COUNT_PROOF_GUIDED_SCHEDULING=previous}
})

test('a failed outsider invalidates the actual citing proposal and the survivor is rebuilt without it',()=>{
 const good:Law={name:'good bound',holds:{op:'<=',a:x('right'),b:n(0)}}
 const left:Law={name:'surviving left',holds:same(x('left'),n(0))}
 const bad:Law={name:'false outsider',holds:all(same(x('right'),n(0)),same(x('noise'),n(1)))}
 const m:Machine={name:'rebuild',params:[],inputs:[],state:{left:n(0),right:n(0),noise:n(1)},step:{state:{left:x('right'),right:x('left'),noise:n(0)}}}
 alternatives=new Set();selected=[left,good];priority=new Map([[left.name,0],[good.name,1],[bad.name,2]])
 family=[bad,left,good];requirements=new Map([[good.name,[left.name]],[left.name,[bad.name]],[bad.name,[good.name]]])
 // Put the false source first in the original goal, rather than transporting
 // through a subset with potentially duplicate normalized constraints.
 chooseSource=undefined
 const {out,events}=run(m,[good,left])
 if(!events.some(e=>e.phase==='count-component-result'&&(e.invalidated as string[]).includes(left.name)))throw Error(JSON.stringify({why:out.why,events:events.filter(e=>String(e.phase).startsWith('count-component'))}))
 expect(events.some(e=>e.phase==='count-component-result'&&e.law===bad.name&&e.outcome==='refuted')).toBe(true)
 expect(events.some(e=>e.phase==='count-component-result'&&(e.invalidated as string[]).includes(left.name))).toBe(true)
 expect(events.filter(e=>e.phase==='count-component-attempt'&&e.law===left.name&&e.mode==='joint').length).toBeGreaterThanOrEqual(2)
 expect(out.proven).toBe(true);expect(checkCountedLaws(out.m,out.laws,out.proof!)).toBe(true)
 expect(out.laws).not.toContain(bad);expect(out.proof!.premises?.[left.name]).not.toContain(bad.name)
})
