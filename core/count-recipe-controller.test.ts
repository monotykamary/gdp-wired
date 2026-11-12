import {expect,test} from 'bun:test'
import {CountRecipePass,runCountRecipeController,type CountControllerMember} from './count-recipe-controller.ts'
import {CountAttemptWork} from './count-attempt-work.ts'
import {countAttemptStop,planCountRetry} from './count-retry-budget.ts'
import {type LiftedWorkSlice,type LiftedWorkTrace} from './count-lifted-budget.ts'
import {WorkLedger} from './work-admission.ts'
import {type WorkAmount,workAmount,workAdd,workSub} from './work-amount.ts'
import {completeWorkProfile} from './work-profile.ts'
import {type WorkKey,workKeys} from './work-kinds.ts'
const fullTest=completeWorkProfile.enabled?test:test.skip
const bank=()=>new WorkLedger(Object.fromEntries(workKeys.map(key=>[key,1])) as Record<WorkKey,number>)
const a=(n:number)=>workAmount(BigInt(n))
function slice<T>(b:WorkLedger,kind:'case'|'leaf',key:string,allocation:WorkAmount,trace:LiftedWorkTrace,run:()=>T,caseKey?:string):T{
 const state:{item?:LiftedWorkSlice,before?:WorkAmount,completed:boolean,error?:unknown}={completed:false}
 try{return b.withBudget(allocation,()=>{
  const scope=b.currentScope()!
  state.item={kind,key,caseKey,allocation,scopeId:scope.id,rootEpoch:b.snapshot().rootEpoch};state.before=b.actual()
  trace({stage:'start',slice:state.item})
  const result=run();state.completed=true;return result
 })}catch(error){state.error=error;state.completed=false;throw error}
 finally{if(state.item&&state.before)trace({stage:'end',slice:state.item,used:workSub(b.actual(),state.before),completed:state.completed,error:state.error})}
}
fullTest('controller: three distinct soft keys then the same proposal with F-3 tickets',()=>{
 const b=bank(),events:Record<string,unknown>[]=[],members:CountControllerMember[]=[{name:'target',reference:0,recipes:[{id:'lifted',kind:'strategy',required:[],caseKeys:['op:0','op:1','op:2']}]}]
 b.withBudget(a(1200000),()=>{
  const pass=new CountRecipePass<{bytes:string}>(members,'fixed',b)
  const out=runCountRecipeController(pass,['target'],{observe:e=>events.push(e),construct:(_name,_recipe,budget)=>{
   const lease=budget!.lease!
   for(const key of ['op:0','op:1','op:2'])slice(b,'case',key,lease.cases[key]??lease.operation,lease.trace!,()=>b.start('ticks',60000))
   return {payload:{bytes:'unchanged native proposal'},premises:[],checkedReduced:false,checkCost:a(0)}
  },close:rows=>rows[0]!.payload})
  expect(out.result).toEqual({bytes:'unchanged native proposal'})
  expect(events.filter(e=>e.phase==='count-component-attempt')).toHaveLength(4)
  expect(pass.states[0]!.recipes[0]!.tickets.snapshot()).toMatchObject({remaining:3,started:4,terminal:true})
  expect(events.filter(e=>e.phase==='count-recipe-result'&&e.outcome==='unfinished').map(e=>(e.stop as {key:string}).key)).toEqual(['op:0','op:1','op:2'])
 })
})
test('collector: more than64 physical leaves remain one slot and cannot raise on a CASE retry',()=>{
 const b=bank();b.withBudget(a(10000),()=>{
  const usage=new CountAttemptWork([{key:'op:0',allocation:a(1000),used:a(0)},{key:'leaf',allocation:a(10),used:a(0)}],b)
  let error:unknown
  try{slice(b,'case','op:0',a(1000),usage.trace,()=>{
   for(let i=0;i<100;i++)slice(b,'leaf','leaf:'+i,a(10),usage.trace,()=>b.start('ticks',1),'op:0')
   b.start('ticks',1001)
  })}catch(caught){error=caught}
  expect(usage.valid()).toBe(true);expect(usage.slices).toHaveLength(1)
  expect(usage.inventory().find(key=>key.key==='leaf')).toMatchObject({completed:100});const leafUse=usage.keys().find(key=>key.key==='leaf')!.used;expect(leafUse.num).toBeGreaterThan(10n)
  const failed=usage.slices[0]!,plan=planCountRetry(usage.keys(),countAttemptStop(error,[failed],b),[],b)
  expect(plan.kind).toBe('admitted')
  if(plan.kind!=='admitted')throw Error('missing retry plan')
  expect(plan.need).toEqual(workAdd(a(2000),leafUse));expect(plan.keys.map(key=>key.allocation)).toEqual([a(2000),a(10)])
 })
})
fullTest('controller: terminal producer stays consumed across context changes',()=>{
 const b=bank();b.withBudget(a(10000),()=>{
  const pass=new CountRecipePass<string>([{name:'target',reference:0,recipes:[{id:'ordinary',kind:'ordinary'}]}],'first',b)
  let calls=0
  const hooks={construct:()=>{calls++;return undefined},close:()=>false}
  runCountRecipeController(pass,['target'],hooks);pass.reconcile('second');runCountRecipeController(pass,['target'],hooks)
  expect(calls).toBe(1);expect(pass.states[0]!.recipes[0]!.tickets.snapshot().started).toBe(1)
 })
})
fullTest('controller: understated unchecked payload cannot enter G without producing requirements',()=>{
 const b=bank();b.withBudget(a(10000),()=>{
  const pass=new CountRecipePass<string>([{name:'target',reference:0,recipes:[{id:'known',kind:'strategy',required:['dependency']}]},{name:'dependency',reference:1,recipes:[{id:'known',kind:'ordinary',required:['target']}]}],'fixed',b)
  let closes=0
  const out=runCountRecipeController(pass,['target'],{construct:name=>name==='target'?{payload:'unchecked',premises:[],checkedReduced:false,checkCost:a(0)}:undefined,close:()=>{closes++;return true}})
  expect(out.result).toBeUndefined();expect(closes).toBe(0)
 })
})
fullTest('controller: a newly blocked known route cannot start through an open unknown alternative',()=>{
 const b=bank();b.withBudget(a(10000),()=>{
  const pass=new CountRecipePass<string>([
   {name:'target',reference:0,recipes:[{id:'known',kind:'ordinary',required:['dependency']},{id:'unknown',kind:'ordinary'}]},
   {name:'dependency',reference:1,recipes:[{id:'once',kind:'ordinary',required:[]}]}
  ],'fixed',b)
  const target=pass.states[0]!,dependency=pass.states[1]!
  dependency.recipes[0]!.terminal=true
  dependency.held={recipeId:'once',payload:'previous',premises:[],checkedReduced:true,checkCost:a(0)}
  const calls:string[]=[],events:Record<string,unknown>[]=[]
  const out=runCountRecipeController(pass,['target'],{
   preflight:(_name,recipe)=>{if(recipe.id==='known')dependency.held=undefined;return true},
   construct:(name,recipe)=>{calls.push(name+':'+recipe.id);return {payload:'replacement',premises:[],checkedReduced:true,checkCost:a(0)}},
   close:rows=>rows[0]!.payload,observe:event=>events.push(event)
  })
  expect(out.result).toBe('replacement');expect(calls).toEqual(['target:unknown'])
  expect(target.recipes[0]!.tickets.snapshot().started).toBe(0)
  expect(target.recipes[1]!.tickets.snapshot().started).toBe(1)
  expect(events.some(event=>event.phase==='count-component-attempt'&&event.recipe==='known')).toBe(false)
 })
})
fullTest('controller: search metadata cannot consume reserved closing work near the phase boundary',()=>{
 const b=bank();b.withBudget(a(1000),()=>{
  const pass=new CountRecipePass<string>([{name:'target',reference:0,recipes:[{id:'done',kind:'ordinary',required:[]}]}],'fixed',b)
  pass.states[0]!.recipes[0]!.terminal=true
  pass.states[0]!.held={recipeId:'done',payload:'held',premises:[],checkedReduced:true,checkCost:a(0)}
  b.start('ticks',Number(624n-b.actual().num))
  let closing=0
  const out=runCountRecipeController(pass,['target'],{construct:()=>{throw Error('search must not start')},close:rows=>{
   closing++;expect(b.available()!.num).toBeGreaterThanOrEqual(300n)
   b.start('ticks',300,'independent closing work');return rows[0]!.payload
  }})
  expect(out.reason).toBe('phase-cap');expect(out.result).toBe('held');expect(closing).toBe(1)
 })
})
