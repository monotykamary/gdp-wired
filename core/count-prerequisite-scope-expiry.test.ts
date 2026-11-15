// Isolated process. Native proofs and scope logic stay real; only untrusted
// producers and the timing of one scope call are controlled.
import {expect,mock,test} from 'bun:test'
import {type Law,type Machine,n,same,x} from './machine.ts'
import {admitCountedFamily,countedAttempts,countsDump} from './counts.ts'
import * as strategies from './count-strategies.ts'
import * as planning from './count-prerequisite-plan.ts'
import * as scope from './count-proof-scope.ts'
import * as views from './count-premise-view.ts'
import {workLedger,type WorkCapacityRefusal} from './work-admission.ts'
import {compareWork,integerQuotient,workFromExact} from './work-amount.ts'
import {completeWorkProfile} from './work-profile.ts'
import {BudgetExpired,clock,fullRate,withBudget,withDeadline} from '../kernel/prove.ts'
import {checkCountedLaws} from '../kernel/kernel.ts'
const fullTest=completeWorkProfile.enabled?test:test.skip
const a:Law={name:'held left',holds:same(x('left'),n(0))},b:Law={name:'scoped right',holds:same(x('right'),n(0))},family=[a,b]
const m:Machine={name:'scope endpoint',params:[],inputs:[],state:{left:n(0),right:n(0)},step:{state:{left:x('right'),right:x('left')}}}
const original={...strategies},planner={...planning},scoper={...scope},view={...views}
let mode:'equal'|'invalid'|'parent'|'healthy'='equal',intercepted=false,parentId=0,exhaustionObserved=false
let localRefusal:WorkCapacityRefusal|undefined
const fillEndpoint=()=>{
 const left=workLedger.available();expect(left).not.toBeNull()
 const ticks=integerQuotient(left!,workLedger.weights.ticks)
 if(ticks)workLedger.start('ticks',Number(ticks),'scope control fill')
 expect(compareWork(workLedger.available()!,workLedger.weights.ticks)).toBeLessThan(0)
}
const authenticate=(error:unknown)=>{
 const refusal=workLedger.capacityRefusal(error);expect(refusal).toBeDefined()
 expect(refusal!.limiting.every(endpoint=>compareWork(workFromExact(refusal!.actual),workFromExact(endpoint.end))<=0)).toBe(true)
 return refusal!
}
void mock.module('./count-strategies.ts',()=>({...original,prepareCountStrategyMachine:(value:Machine)=>value,selectedCountStrategies:()=>family,
 proposeCountStrategiesForClosing:(machine:Machine,context:Law[],target:Law,end:number)=>{
  const result=countedAttempts(machine,[target],new Set(),end).traced(target,context,0,Math.max(0,end-clock()),false)
  return 'proof'in result?result.proof:undefined
 }}))
void mock.module('./count-prerequisite-plan.ts',()=>({...planner,countPrerequisiteSchedule:()=>({requirements:new Map([[a.name,[b.name]],[b.name,[a.name]]]),recipes:new Map(family.map(law=>[law.name,[{id:'fixture',kind:'strategy' as const,required:[law===a?b.name:a.name]}]])),costs:new Map([[a.name,0],[b.name,1]])})}))
void mock.module('./count-premise-view.ts',()=>({...view,countPremiseContext:()=>undefined}))
void mock.module('./count-proof-scope.ts',()=>({...scoper,scopeCountProof:(...args:Parameters<typeof scope.scopeCountProof>)=>{
 if(args[1].name===b.name&&!intercepted){
  intercepted=true
  if(mode==='invalid')return undefined
  if(mode==='parent'||mode==='healthy')return scoper.scopeCountProof(...args)
  fillEndpoint()
  exhaustionObserved=true
  // Exercise the native scoper at the exact bank boundary. Its first unpaid
  // operation must be refused locally, without invalidating the held member.
  try{const result=scoper.scopeCountProof(...args);expect(result).toBeUndefined();return result}
  catch(error){
   localRefusal=authenticate(error)
   expect(localRefusal.limiting.every(endpoint=>endpoint.kind!=='root'&&endpoint.id!==parentId)).toBe(true)
   throw error
  }
 }
 return scoper.scopeCountProof(...args)
}}))
function run(kind:typeof mode,units=25000000){
 mode=kind;intercepted=false;exhaustionObserved=false;localRefusal=undefined
 const previous=countsDump.on,events:Record<string,unknown>[]=[]
 let error:unknown,result:ReturnType<typeof admitCountedFamily>|undefined
 countsDump.on=event=>{
  const row=event as Record<string,unknown>
  // Only after the native scope returns are its stricter child allowances gone.
  // Cancel at that handoff, under the actual inherited parent endpoint.
  if(kind==='parent'&&row.phase==='count-component-result'&&row.law===b.name){
   fillEndpoint()
   try{workLedger.start('ticks',1,'parent scope handoff')}catch(error){
    expect(authenticate(error).limiting.some(endpoint=>endpoint.id===parentId)).toBe(true);throw error
   }
   throw Error('parent failed to refuse')
  }
  events.push(row)
 }
 try{
  try{result=withBudget(units,()=>{
   const invoke=()=>admitCountedFamily(m,[a],family,new Set(),clock()+units/fullRate)
   if(kind==='parent')return withDeadline(Math.ceil(clock())+1000,()=>{parentId=workLedger.currentScope()!.id;return invoke()})
   return invoke()
  })}catch(caught){error=caught}
  return {error,result,events,exhausted:exhaustionObserved,refusal:localRefusal}
 }finally{countsDump.on=previous}
}
fullTest('exact local capacity exhaustion during real scope capture is unknown, never invalidation',()=>{
 // Fill by legal integer admissions, not fractional writes or rounded-clock reconstruction.
 const {error,result,events,exhausted,refusal}=run('equal',1000000)
 expect(error).toBeUndefined();expect(exhausted).toBe(true);expect(refusal).toBeDefined();expect(result?.proven).toBe(false)
 const right=events.filter(event=>event.phase==='count-component-result'&&event.law===b.name)
 expect(right.some(event=>event.outcome==='unknown'&&event.reason==='budget-expired')).toBe(true)
 expect(right.every(event=>(event.failed as string[]).length===0&&(event.invalidated as string[]).length===0)).toBe(true)
 expect(events.filter(event=>event.phase==='count-component-attempt'&&event.law===a.name)).toHaveLength(1)
 expect(events.filter(event=>event.phase==='count-prerequisite-memory').at(-1)?.held).toContain(a.name)
})
fullTest('the same native scope with sufficient allowance proves and kernel-checks the family',()=>{
 const {error,result}=run('healthy')
 expect(error).toBeUndefined();expect(result?.proven).toBe(true)
 expect(checkCountedLaws(result!.m,result!.laws,result!.proof!)).toBe(true)
})
fullTest('genuinely invalid scope before the endpoint refuses and invalidates actual users',()=>{
 const {error,events}=run('invalid')
 expect(error).toBeUndefined();expect(intercepted).toBe(true)
 expect(events.some(event=>event.phase==='count-component-result'&&event.law===b.name&&event.outcome==='refused'&&(event.invalidated as string[]).includes(a.name))).toBe(true)
})
fullTest('post-scope inherited phase cancellation propagates rather than becoming local unknown',()=>{
 const {error,events}=run('parent')
 expect(error).toBeInstanceOf(BudgetExpired);expect(intercepted).toBe(true)
 expect(workLedger.capacityRefusal(error)?.limiting.some(endpoint=>endpoint.id===parentId)).toBe(true)
 expect(events.some(event=>event.phase==='count-component-result'&&event.law===b.name)).toBe(false)
})
