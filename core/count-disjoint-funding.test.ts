import {expect,test} from 'bun:test'
import {CountFundingOwners,countDisjointContext,planDisjointCountRound,runDisjointCountRound,type CountDisjointPlan} from './count-disjoint-funding.ts'
import {CountAttemptTickets} from './count-retry-budget.ts'
import {WorkLedger,BudgetExpired} from './work-admission.ts'
import {workAmount,workAdd,workSub} from './work-amount.ts'
import {type WorkKey,workKeys} from './work-kinds.ts'
const a=(n:number)=>workAmount(BigInt(n))
const bank=()=>new WorkLedger(Object.fromEntries(workKeys.map(key=>[key,1])) as Record<WorkKey,number>)
function fixed(b:WorkLedger,body=6):Extract<CountDisjointPlan,{kind:'admitted'}>{return {kind:'admitted',caps:{cases:new Map([['op:0',a(4)]]),leaf:a(2)},body:a(body),minimumBody:a(0),need:a(body+4),rootEpoch:b.snapshot().rootEpoch,context:countDisjointContext(new CountAttemptTickets(),b)}}
test('disjoint body uses a remaining cumulative allowance, never a fresh segment grant',()=>{
 const b=bank();b.withBudget(a(100),()=>{
  const owners=new CountFundingOwners(fixed(b),b)
  owners.body(()=>b.start('ticks',2));owners.case('op:0',()=>b.start('ticks',1));owners.body(()=>b.start('ticks',2))
  expect(()=>owners.body(()=>b.start('ticks',1))).toThrow(BudgetExpired)
  const receipt=owners.receipt(false)
  expect(receipt.body).toEqual(a(6));expect(receipt.cases.get('op:0')).toEqual(a(2));expect(receipt.sum).toEqual(receipt.round)
 })
})
test('a body cannot wrap a case and owner-free work cannot be silently attributed',()=>{
 const b=bank();b.withBudget(a(100),()=>{
  const owners=new CountFundingOwners(fixed(b,20),b)
  expect(()=>owners.body(()=>owners.case('op:0',()=>undefined))).toThrow('overlapping')
  b.start('ticks',1)
  expect(()=>owners.receipt(false)).toThrow('unowned or overlapping')
 })
})
test('live H includes ancestors and reservations; partial body history does not replace b0',()=>{
 const b=bank();b.withBudget(a(1000),()=>b.withBudget(a(200),()=>{
  const before=b.actual(),tickets=new CountAttemptTickets(),plan=planDisjointCountRound({cases:new Map([['op:0',a(30)]]),leaf:a(2)},a(20),[{completed:false,used:a(1),instance:tickets,rootEpoch:b.snapshot().rootEpoch}],tickets,undefined,b)
  expect(plan.kind).toBe('admitted')
  if(plan.kind!=='admitted')throw Error('missing plan')
  expect(plan.need).toEqual(b.available()!);expect(plan.minimumBody).toEqual(a(20));expect(plan.body).toEqual(workSub(plan.need,a(30)))
  expect(b.actual().num).toBeGreaterThan(before.num)
 }))
})
test('leaf contributes zero to disjoint need and cannot double past its unchanged case',()=>{
 const b=bank();b.withBudget(a(1000),()=>{
  const caps={cases:new Map([['op:0',a(30)]]),leaf:a(20)},stop={kind:'soft-slice' as const,key:'leaf',allocation:a(20),scopeId:4,rootEpoch:b.snapshot().rootEpoch,caseKey:'op:0'}
  expect(planDisjointCountRound(caps,a(1),[],new CountAttemptTickets(),stop,b)).toEqual({kind:'refused',reason:'parent'})
  const plan=planDisjointCountRound({...caps,leaf:a(10)},a(1),[],new CountAttemptTickets(),{...stop,allocation:a(10)},b)
  if(plan.kind!=='admitted')throw Error('missing plan')
  expect(plan.caps.leaf).toEqual(a(20));expect(plan.caps.cases.get('op:0')).toEqual(a(30));expect(workAdd(plan.body,a(30))).toEqual(plan.need)
 })
})
test('body hard-stop policy leaves unused case credit untouched and cannot retry',()=>{
 const b=bank();b.withBudget(a(1000),()=>{
  const tickets=new CountAttemptTickets(),plan=planDisjointCountRound({cases:new Map([['op:0',a(100)]]),leaf:a(5)},a(10),[],tickets,undefined,b)
  if(plan.kind!=='admitted')throw Error('missing plan')
  const output=runDisjointCountRound(plan,tickets,owners=>{
   owners.case('op:0',()=>b.start('ticks',1))
   owners.body(()=>b.start('ticks',1000))
   return {kind:'proposal',value:'unreachable'}
  },b)
  expect(output.result.kind).toBe('hard-cap');expect(tickets.snapshot()).toMatchObject({terminal:true,started:1,remaining:6})
  expect(output.receipt?.sum).toEqual(output.receipt?.round);expect(b.available()!.num).toBeGreaterThan(0n)
 })
})
test('body-owned leaf stop is hard, but actual case-owned leaf records its parent',()=>{
 for(const bodyOwned of [true,false]){
  const b=bank();b.withBudget(a(1000),()=>{
   const tickets=new CountAttemptTickets(),plan=planDisjointCountRound({cases:new Map([['op:0',a(100)]]),leaf:a(5)},a(10),[],tickets,undefined,b)
   if(plan.kind!=='admitted')throw Error('missing plan')
   const out=runDisjointCountRound(plan,tickets,owners=>{
    const leaf=()=>owners.leaf('physical-leaf',()=>b.start('ticks',6))
    if(bodyOwned)owners.body(leaf);else owners.case('op:0',leaf)
    return {kind:'proposal',value:0}
   },b)
   expect(out.result.kind).toBe(bodyOwned?'hard-cap':'unfinished')
   if(out.result.kind==='unfinished')expect(out.result.stop).toMatchObject({kind:'soft-slice',key:'leaf',caseKey:'op:0',physicalKey:'physical-leaf'})
   expect(out.receipt?.sum).toEqual(out.receipt?.round)
  })
 }
})
test('stale plan or newly one-unit-short ancestor starts neither ticket nor body',()=>{
 const b=bank();let plan:CountDisjointPlan|undefined
 b.withBudget(a(1000),()=>{
  const tickets=new CountAttemptTickets();plan=planDisjointCountRound({cases:new Map([['op:0',a(20)]]),leaf:a(2)},a(1),[],tickets,undefined,b)
  if(plan.kind!=='admitted')throw Error('missing plan')
  let calls=0
  b.withBudget(workSub(plan.need,a(1)),()=>expect(runDisjointCountRound(plan!,tickets,()=>{calls++;return {kind:'decline',reason:'not entered'}},b).result.kind).toBe('not-started'))
  expect(calls).toBe(0);expect(tickets.snapshot().started).toBe(0)
 })
 b.withBudget(a(1000),()=>expect(runDisjointCountRound(plan!,new CountAttemptTickets(),()=>({kind:'decline',reason:'not entered'}),b).result.kind).toBe('not-started'))
})
test('a prepared disjoint plan is tied to its ticket instance and exact parent, not just headroom',()=>{
 const b=bank(),tickets=new CountAttemptTickets(),other=new CountAttemptTickets();let calls=0
 b.withBudget(a(1000),()=>{
  let plan:CountDisjointPlan|undefined
  b.withBudget(a(200),()=>{
   plan=planDisjointCountRound({cases:new Map([['op:0',a(20)]]),leaf:a(2)},a(5),[],tickets,undefined,b)
   const foreign=runDisjointCountRound(plan,other,()=>{calls++;return {kind:'proposal',value:0}},b)
   expect(foreign.result.kind).toBe('not-started')
  })
  b.withBudget(a(200),()=>{
   const sibling=runDisjointCountRound(plan!,tickets,()=>{calls++;return {kind:'proposal',value:0}},b)
   expect(sibling.result.kind).toBe('not-started')
  })
  expect(calls).toBe(0);expect(tickets.snapshot().started).toBe(0);expect(other.snapshot().started).toBe(0)
 })
})
test('false eligibility or changed eligibility context consumes no disjoint ticket or producer',()=>{
 for(const changedContext of [false,true]){
  const b=bank();b.withBudget(a(1000),()=>{
   const tickets=new CountAttemptTickets(),plan=planDisjointCountRound({cases:new Map([['op:0',a(20)]]),leaf:a(2)},a(5),[],tickets,undefined,b)
   let calls=0,checks=0
   const out=runDisjointCountRound(plan,tickets,()=>{calls++;return {kind:'proposal',value:0}},b,()=>{
    checks++;if(changedContext)b.withBudget(a(5),()=>undefined)
    return changedContext
   })
   expect(out.result).toEqual({kind:'not-started',reason:changedContext?'context':'ineligible'})
   expect(checks).toBe(1);expect(calls).toBe(0);expect(tickets.snapshot()).toMatchObject({started:0,remaining:7,terminal:false})
   expect(out.receipt?.complete).toBe(false);expect(out.receipt?.sum).toEqual(out.receipt?.round)
  })
 }
})
test('an unfinished attempt cannot reuse its old disjoint plan or renew a ticket without preparation',()=>{
 const b=bank();b.withBudget(a(1000),()=>{
  const tickets=new CountAttemptTickets(),plan=planDisjointCountRound({cases:new Map([['op:0',a(20)]]),leaf:a(2)},a(5),[],tickets,undefined,b)
  const first=runDisjointCountRound(plan,tickets,owners=>{owners.case('op:0',()=>b.start('ticks',21));return {kind:'proposal',value:0}},b)
  expect(first.result.kind).toBe('unfinished');expect(tickets.snapshot()).toMatchObject({started:1,terminal:false})
  let calls=0
  const again=runDisjointCountRound(plan,tickets,()=>{calls++;return {kind:'proposal',value:0}},b)
  expect(again.result.kind).toBe('not-started');expect(calls).toBe(0);expect(tickets.snapshot().started).toBe(1)
 })
})
test('terminal ticket settlement is body-owned before receipt sealing, including a hard body stop',()=>{
 for(const interrupted of [false,true]){
  const b=bank();b.withBudget(a(1000),()=>{
   const tickets=new CountAttemptTickets(),plan=interrupted?{...fixed(b,6),context:countDisjointContext(tickets,b)}:
    planDisjointCountRound({cases:new Map([['op:0',a(20)]]),leaf:a(2)},a(10),[],tickets,undefined,b)
   const finish=tickets.finish.bind(tickets);let endings=0,atFinish=a(0)
   tickets.finish=result=>{
    endings++;expect(b.snapshot().activeEndpoints).toHaveLength(3)
    atFinish=b.actual();finish(result)
   }
   const out=runDisjointCountRound(plan,tickets,owners=>{
    owners.case('op:0',()=>b.start('ticks',interrupted?1:2))
    owners.body(()=>b.start('ticks',3))
    return {kind:'proposal',value:0}
   },b)
   expect(out.result.kind).toBe(interrupted?'hard-cap':'proposal');expect(endings).toBe(1)
   expect(out.receipt?.complete).toBe(!interrupted)
   expect(out.receipt?.body).toEqual(a(interrupted?6:10))
   expect(workSub(b.actual(),atFinish)).toEqual(a(1))
   expect(out.receipt?.sum).toEqual(out.receipt?.round)
   expect(tickets.snapshot().terminal).toBe(true)
  })
 }
})
