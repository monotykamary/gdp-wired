// B independent 46.18 controls. Own FULL-profile Bun process; no skip aliases.
// Uses the real controller and native global ledger, not a replacement bank.
// These are allocation controls; native public proof acceptance is covered by
// count-recipe-context-public.test.ts. No production b0/F or fit claim.
import {beforeAll,expect,test} from 'bun:test'
import * as controller from './count-recipe-controller.ts'
import {type CountControllerMember,type CountCaptured} from './count-recipe-controller.ts'
import {countRecipeGraph,type CountRecipeGraph} from './count-recipe-graph.ts'
import {BudgetExpired,workLedger} from './work-admission.ts'
import {type ExactRaw,type WorkAmount,workAmount,workFromExact,workAdd,workSub,workShare,compareWork,minWork} from './work-amount.ts'
import {completeWorkProfile} from './work-profile.ts'
import {withBudget} from '../kernel/prove.ts'
const ROOT=4_800_000,a=(n:number)=>workAmount(BigInt(n))
type Kind='ordinary'|'strategy'
type Event=Record<string,unknown>
type Pass=controller.CountRecipePass<string>
type Options={pad?:WorkAmount,construct?:(name:string,id:string,pass:Pass)=>CountCaptured<string>|undefined,observe?:(event:Event,pass:Pass)=>void}
beforeAll(()=>{expect(completeWorkProfile.enabled).toBe(true);expect(workLedger.weights.ticks).toEqual(a(1))})
const exact=(value:unknown):WorkAmount=>{expect(value).toBeDefined();return workFromExact(value as ExactRaw)}
function family(wide:boolean,kind:Kind,extra=20):CountControllerMember[]{
 return [{name:'a',reference:0,recipes:[{id:'first',kind,required:[]}]},
  {name:'b',reference:1,recipes:[{id:'first',kind,required:[]}]},
  {name:'target',reference:2,recipes:[{id:'known',kind,required:['a','b']},{id:'trigger',kind,...(wide?{}:{required:[]})}]},
  ...Array.from({length:extra},(_,i)=>({name:'outside'+i,reference:i+3,recipes:[{id:'first',kind,required:[]}]}))]
}
function execute(members:CountControllerMember[],options:Options={}){
 return withBudget(ROOT,()=>{
  const pass=new controller.CountRecipePass<string>(members,'B fixed cohort'),events:Event[]=[]
  if(options.pad&&compareWork(options.pad,a(0))>0){expect(options.pad.den).toBe(1n);workLedger.start('ticks',Number(options.pad.num),'fixture headroom alignment')}
  const result=controller.runCountRecipeController(pass,['target'],{
   construct:(name,recipe)=>options.construct?.(name,recipe.id,pass),close:()=>false,
   observe:event=>{events.push(event);options.observe?.(event,pass)}
  })
  return {pass,events,result}
 })
}
function admission(events:Event[],name:string,index=0){
 const found=events.filter(e=>e.phase==='count-recipe-admission'&&e.law===name)[index]
 expect(found).toBeDefined();return found!
}
function formula(event:Event,p:number,kind:Kind){
 const remaining=exact(event.allocationRemaining),allotted=exact(event.allotted)
 expect(event.allocationCohort).toBe(p)
 const reserve=a(p-1),expected=kind==='ordinary'?workShare(remaining,1n,BigInt(p)):
  compareWork(remaining,reserve)>0?workSub(remaining,reserve):a(0)
 expect(allotted).toEqual(expected);return {remaining,allotted}
}
// Access optional new helpers only for the Q=0 arithmetic edge. The main
// controller assertions above/below run before this, so old-pin sensitivity
// is not just a missing-export/import error.
const cohortApi=controller as unknown as {
 countRecipeAllocationCohort:(members:Iterable<string>,graph:CountRecipeGraph,selected:string,tick:()=>void)=>number,
 countRecipeMemberAllotment:(remaining:WorkAmount,p:number,kind:Kind,tick:WorkAmount)=>WorkAmount
}

test('46.18 B1: equal live headroom gives a closure member the same allotment with or without widening',()=>{
 for(const kind of ['ordinary','strategy'] as const){
  const narrow0=execute(family(false,kind)),wide0=execute(family(true,kind))
  const n0=admission(narrow0.events,'a'),w0=admission(wide0.events,'a')
  // A behavioral discriminator before reading the new diagnostic fields.
  if(kind==='ordinary')expect(compareWork(exact(w0.allotted),a(ROOT/8))).toBeGreaterThan(0)
  const nr=exact(n0.allocationRemaining),wr=exact(w0.allocationRemaining),shared=minWork(nr,wr)
  const narrow=execute(family(false,kind),{pad:workSub(nr,shared)}),wide=execute(family(true,kind),{pad:workSub(wr,shared)})
  const n=formula(admission(narrow.events,'a'),3,kind),w=formula(admission(wide.events,'a'),3,kind)
  expect(n.remaining).toEqual(shared);expect(w.remaining).toEqual(shared)
  expect(w.allotted).toEqual(n.allotted)
 }
})

test('46.18 B2: outside selected member counts itself with Q=3; empty Q gives p=1, not new credit',()=>{
 for(const kind of ['ordinary','strategy'] as const){
  const members=family(true,kind).map(member=>member.name.startsWith('outside')&&member.name!=='outside0'
   ?{...member,recipes:[{id:'first',kind,required:['outside0']}]}
   :member)
  const out=execute(members),event=admission(out.events,'outside0')
  if(kind==='ordinary')expect(compareWork(exact(event.allotted),a(ROOT/10))).toBeGreaterThan(0)
  formula(event,4,kind)
  withBudget(ROOT,()=>{
   const graph=countRecipeGraph(members,['target']),empty={...graph,closure:new Set([...graph.closure,'not-a-member']),usable:new Set(graph.closure),blocked:new Set(['not-a-member'])}
   const p=cohortApi.countRecipeAllocationCohort(members.map(m=>m.name),empty,'outside0',()=>workLedger.start('ticks',1))
   expect(p).toBe(1)
   const before=workLedger.available()!,result=cohortApi.countRecipeMemberAllotment(before,p,kind,workLedger.weights.ticks)
   expect(result).toEqual(before);expect(workLedger.available()).toEqual(before)
   expect(cohortApi.countRecipeMemberAllotment(a(0),4,kind,workLedger.weights.ticks)).toEqual(a(0))
  })
 }
})

test('46.18 B3: twenty widened members affect scheduling, not either closure allocation formula',()=>{
 for(const kind of ['ordinary','strategy'] as const){
  const members=family(true,kind),graph=countRecipeGraph(members,['target'],()=>{})
  expect(graph.candidates.size).toBe(23);expect([...graph.closure].sort()).toEqual(['a','b','target'])
  expect(graph.next?.name).toBe('a');expect([...graph.requirements.get('target')!]).toEqual(['a','b'])
  const out=execute(members),event=admission(out.events,'a')
  if(kind==='ordinary')expect(compareWork(exact(event.allotted),a(ROOT/8))).toBeGreaterThan(0)
  formula(event,3,kind)
 }
})

test('46.18 B4: widened member exhausts its own fixed allotment, spends real ancestor work, and stops hard',()=>{
 const members:CountControllerMember[]=[{name:'outside',reference:0,recipes:[{id:'first',kind:'ordinary',required:[]}]},
  {name:'target',reference:1,recipes:[{id:'trigger',kind:'ordinary'}]},
  ...Array.from({length:20},(_,i)=>({name:'irrelevant'+i,reference:i+2,recipes:[{id:'first',kind:'ordinary' as const,required:[]}]}))]
 let charged=a(0),caught:unknown
 const out=execute(members,{observe:event=>{
  if(event.phase==='count-recipe-admission'&&event.law==='outside'){
   expect(compareWork(exact(event.allotted),a(ROOT/5))).toBeGreaterThan(0);formula(event,2,'ordinary')
  }
 },construct:name=>{
  if(name!=='outside')return undefined
  const before=workLedger.snapshot(),available=workLedger.available()!,ticks=Number(available.num/available.den/2n)
  charged=a(ticks);expect(ticks).toBeGreaterThan(0)
  workLedger.start('ticks',ticks,'widened member productive work')
  const after=workLedger.snapshot()
  expect(workSub(workFromExact(after.actual),workFromExact(before.actual))).toEqual(charged)
  expect(workSub(available,workLedger.available()!)).toEqual(charged)
  expect(after.activeEndpoints.map(e=>[e.id,e.end])).toEqual(before.activeEndpoints.map(e=>[e.id,e.end]))
  expect(after.reserved).toEqual(before.reserved)
  for(const endpoint of before.activeEndpoints){
   const oldHeadroom=workSub(workSub(workFromExact(endpoint.end),workFromExact(before.actual)),workFromExact(before.reserved))
   const newHeadroom=workSub(workSub(workFromExact(endpoint.end),workFromExact(after.actual)),workFromExact(after.reserved))
   expect(workSub(oldHeadroom,newHeadroom)).toEqual(charged)
  }
  const preRefusal=workLedger.actual(),left=workLedger.available()!
  try{workLedger.start('ticks',Number(left.num/left.den)+1,'widened member over cap')}
  catch(error){caught=error;expect(error).toBeInstanceOf(BudgetExpired);expect(workLedger.capacityRefusal(error)).toBeDefined();expect(workLedger.actual()).toEqual(preRefusal);throw error}
  throw Error('expected authenticated member refusal')
 }})
 expect(caught).toBeInstanceOf(BudgetExpired)
 const state=out.pass.states.find(s=>s.member.name==='outside')!
 expect(compareWork(state.used,charged)).toBeGreaterThanOrEqual(0)
 expect(compareWork(state.used,state.allotted!)).toBeLessThanOrEqual(0)
 expect(state.recipes[0]!.tickets.snapshot()).toMatchObject({started:1,terminal:true})
 expect(out.events.some(e=>e.phase==='count-recipe-result'&&e.law==='outside'&&e.outcome==='hard-cap')).toBe(true)
 expect(out.events.some(e=>e.phase==='count-recipe-result'&&e.law==='outside'&&e.outcome==='unfinished')).toBe(false)
})

test('46.18 B5: terminal widening trigger changes future Q but never resets a member shared allotment',()=>{
 const members=family(true,'ordinary')
 members[0]={...members[0]!,recipes:[{id:'first',kind:'ordinary',required:[]},{id:'second',kind:'ordinary',required:[]}]}
 let consumed=false
 const out=execute(members,{observe:(event,pass)=>{
  if(event.phase==='count-recipe-result'&&event.law==='a'&&event.recipe==='first'){
   pass.states.find(s=>s.member.name==='target')!.recipes.find(r=>r.recipe.id==='trigger')!.terminal=true;consumed=true
  }
 },construct:(name,id)=>name==='a'&&id==='first'?undefined:{payload:name,premises:[],checkedReduced:true,checkCost:a(0)}})
 expect(consumed).toBe(true)
 const first=admission(out.events,'a'),second=admission(out.events,'a',1),later=admission(out.events,'b')
 expect(compareWork(exact(first.allotted),a(ROOT/8))).toBeGreaterThan(0)
 formula(first,3,'ordinary');formula(second,3,'ordinary');formula(later,2,'ordinary')
 expect(second.allotted).toEqual(first.allotted);expect(second.allocationRemaining).toEqual(first.allocationRemaining)
 expect(compareWork(exact(second.used),exact(first.used))).toBeGreaterThan(0)
 const row=out.pass.states.find(s=>s.member.name==='a')!
 expect(row.recipes.map(r=>r.tickets.snapshot().started)).toEqual([1,1])
 expect(row.allotted).toEqual(exact(first.allotted))
})
