import {expect,test} from 'bun:test'
import {CountRecipePass,runCountRecipeController} from './count-recipe-controller.ts'
import {BudgetExpired,WorkLedger} from './work-admission.ts'
import {workAmount} from './work-amount.ts'
import {workKeys,type WorkKey} from './work-kinds.ts'
import {completeWorkProfile} from './work-profile.ts'
const full=completeWorkProfile.enabled?test:test.skip,a=(n:number)=>workAmount(BigInt(n))
const bank=()=>new WorkLedger(Object.fromEntries(workKeys.map(key=>[key,1])) as Record<WorkKey,number>)
full('G5: 64 cases decline before a constructor or ticket rather than throwing RangeError',()=>{
 const b=bank();b.withBudget(a(100000),()=>{
  const pass=new CountRecipePass<string>([{name:'target',reference:0,recipes:[{id:'lifted',kind:'strategy',required:[],caseKeys:Array.from({length:64},(_,i)=>'op:'+i)}]}],'fixed',b)
  let calls=0;const events:Record<string,unknown>[]=[]
  const result=runCountRecipeController(pass,['target'],{construct:()=>{calls++;return undefined},close:()=>false,observe:event=>events.push(event)})
  expect(calls).toBe(0);expect(result.failure).toMatchObject({outcome:'decline',reason:'unsupported-case-inventory'})
  expect(pass.states[0]!.recipes[0]!.tickets.snapshot()).toMatchObject({started:0})
  expect(events.some(event=>event.phase==='count-recipe-result'&&event.reason==='unsupported-case-inventory'&&event.maximumCases===63)).toBe(true)
 })
})
full('G5: 63 cases plus the one leaf slot remain schedulable',()=>{
 const b=bank();b.withBudget(a(100000),()=>{
  const pass=new CountRecipePass<string>([{name:'target',reference:0,recipes:[{id:'lifted',kind:'strategy',required:[],caseKeys:Array.from({length:63},(_,i)=>'op:'+i)}]}],'fixed',b)
  let calls=0
  const result=runCountRecipeController(pass,['target'],{construct:()=>{calls++;return undefined},close:()=>false})
  expect(calls).toBe(1);expect(pass.states[0]!.recipes[0]!.keys).toHaveLength(64)
  expect(result.failure?.reason).toBe('constructor-declined')
 })
})
full('G4: capture refusal survives in both the event and controller outcome',()=>{
 const b=bank();b.withBudget(a(100000),()=>{
  const pass=new CountRecipePass<string>([{name:'target',reference:0,recipes:[{id:'ordinary',kind:'ordinary',required:[]}]}],'fixed',b)
  const events:Record<string,unknown>[]=[]
  const result=runCountRecipeController<string,boolean,string>(pass,['target'],{construct:()=> 'offer',capture:()=>undefined,close:()=>false,observe:event=>events.push(event)})
  expect(result.failure).toMatchObject({outcome:'decline',reason:'capture-declined'})
  expect(events.some(event=>event.phase==='count-recipe-result'&&event.reason==='capture-declined')).toBe(true)
  expect(pass.held().size).toBe(0)
 })
})
full('G4: an unauthenticated budget error stays unclassified rather than becoming an enclosing limit',()=>{
 const b=bank();b.withBudget(a(100000),()=>{
  const pass=new CountRecipePass<string>([{name:'target',reference:0,recipes:[{id:'ordinary',kind:'ordinary',required:[]}]}],'fixed',b)
  const result=runCountRecipeController(pass,['target'],{construct:()=>{throw new BudgetExpired('fixture has no capacity receipt')},close:()=>false})
  expect(result.failure).toMatchObject({outcome:'hard-cap',reason:'unclassified',stop:{kind:'hard-cap',reason:'unclassified'}})
 })
})
full('G6: positive closing headroom below the declared measured requirement is unfunded',()=>{
 const b=bank();b.withBudget(a(10000),()=>{
  const pass=new CountRecipePass<string>([{name:'aux',reference:0,recipes:[{id:'ordinary',kind:'ordinary',required:[]}]},{name:'target',reference:1,recipes:[{id:'ordinary',kind:'ordinary'}]}],'fixed',b)
  pass.states[0]!.held={payload:'held',premises:[],checkedReduced:true,checkCost:a(10000),recipeId:'ordinary'}
  pass.states[0]!.recipes[0]!.terminal=true
  pass.states[1]!.recipes[0]!.terminal=true
  let closes=0;const events:Record<string,unknown>[]=[]
  const result=runCountRecipeController(pass,['target'],{construct:()=>undefined,close:()=>{closes++;return false},observe:event=>events.push(event)})
  expect(closes).toBe(0);expect(result.closingRoute).toBe('unfunded');expect(result.failure?.reason).toBe('closing-reserve')
  expect(events.some(event=>event.phase==='count-recipe-closing-reserve'&&event.admitted===false)).toBe(true)
 })
})
