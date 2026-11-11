// Isolated process. Native proofs and scope logic stay real; only untrusted
// producers and the timing of one scope call are controlled.
import {expect,mock,test} from 'bun:test'
import {type Law,type Machine,n,same,x} from './machine.ts'
import {admitCountedFamily,countedAttempts,countsDump} from './counts.ts'
import * as strategies from './count-strategies.ts'
import * as planning from './count-prerequisite-plan.ts'
import * as scope from './count-proof-scope.ts'
import * as views from './count-premise-view.ts'
import {coreMeter} from './meter.ts'
import {completeWorkProfile} from './work-profile.ts'
import {BudgetExpired,budgetEnd,checkBudget,clock,fullRate,fullWork,withinDeadline,withBudget,withDeadline} from '../kernel/prove.ts'
const fullTest=completeWorkProfile.enabled?test:test.skip
const a:Law={name:'held left',holds:same(x('left'),n(0))},b:Law={name:'scoped right',holds:same(x('right'),n(0))},family=[a,b]
const m:Machine={name:'scope endpoint',params:[],inputs:[],state:{left:n(0),right:n(0)},step:{state:{left:x('right'),right:x('left')}}}
const original={...strategies},planner={...planning},scoper={...scope},view={...views}
let mode:'equal'|'invalid'|'parent'='equal',intercepted=false,parentEnd=Infinity,equalityObserved=false
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
  if(mode==='parent'){
   coreMeter.checkSteps+=Math.max(1,(parentEnd-clock())*fullRate+1000)
   checkBudget('parent scope boundary');throw Error('parent failed to expire')
  }
  const end=args[4]
  for(let i=0;i<8&&clock()!==end;i++)coreMeter.checkSteps+=(end-clock())*fullRate
  expect(clock()).toBe(end)
  console.log('SCOPE_EQUALITY_BOUNDARIES',JSON.stringify({clock:clock(),end,raw:fullWork(),nativeEnd:budgetEnd(),enclosing:withinDeadline(budgetEnd())}))
  expect(()=>checkBudget('exact local scope equality')).not.toThrow()
  const result=scoper.scopeCountProof(...args)
  expect(result).toBeUndefined();equalityObserved=true;return result
 }
 return scoper.scopeCountProof(...args)
}}))
function run(kind:typeof mode,units=25000000){
 mode=kind;intercepted=false;equalityObserved=false
 const saved=coreMeter.checkSteps,previous=countsDump.on,events:Record<string,unknown>[]=[]
 let error:unknown,result:ReturnType<typeof admitCountedFamily>|undefined
 countsDump.on=event=>events.push(event as Record<string,unknown>)
 try{
  // Align the root to an exact full-clock millisecond. Otherwise converting
  // a fractional endpoint to raw units can expire one ULP before equality.
  const boundary=Math.ceil(fullWork()/fullRate)
  for(let i=0;i<8&&fullWork()/fullRate!==boundary;i++)coreMeter.checkSteps+=boundary*fullRate-fullWork()
  expect(fullWork()/fullRate).toBe(boundary)
  try{result=withBudget(units,()=>{
   const invoke=()=>admitCountedFamily(m,[a],family,new Set(),clock()+units/fullRate)
   if(kind==='parent'){parentEnd=clock()+1000;return withDeadline(parentEnd,invoke)}
   return invoke()
  })}catch(caught){error=caught}
  return {error,result,events,equal:equalityObserved}
 }finally{coreMeter.checkSteps=saved;countsDump.on=previous}
}
fullTest('exact local equality during real scope capture is unknown, never invalidation',()=>{
 // This exact native fixture has clock/end/nativeEnd=2401 and raw=600250.
 // A larger fractional fixture may correctly hit its raw cap one ULP first.
 const {error,result,events,equal}=run('equal',1000000)
 expect(error).toBeUndefined();expect(equal).toBe(true);expect(result?.proven).toBe(false)
 const right=events.filter(event=>event.phase==='count-component-result'&&event.law===b.name)
 expect(right.some(event=>event.outcome==='unknown'&&event.reason==='budget-expired')).toBe(true)
 expect(right.every(event=>(event.failed as string[]).length===0&&(event.invalidated as string[]).length===0)).toBe(true)
 expect(events.filter(event=>event.phase==='count-component-attempt'&&event.law===a.name)).toHaveLength(1)
})
fullTest('genuinely invalid scope before the endpoint refuses and invalidates actual users',()=>{
 const {error,events}=run('invalid')
 expect(error).toBeUndefined();expect(intercepted).toBe(true)
 expect(events.some(event=>event.phase==='count-component-result'&&event.law===b.name&&event.outcome==='refused'&&(event.invalidated as string[]).includes(a.name))).toBe(true)
})
fullTest('scope crossing the inherited phase propagates rather than becoming local unknown',()=>{
 const {error,events}=run('parent')
 expect(error).toBeInstanceOf(BudgetExpired);expect(intercepted).toBe(true)
 expect(events.some(event=>event.phase==='count-component-result'&&event.law===b.name)).toBe(false)
})
