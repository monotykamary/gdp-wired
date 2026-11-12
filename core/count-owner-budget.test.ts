// Section46.16–46.17 exact-unit boundary tests. These explicit b0 values are
// fixtures, not production policy. Run this file separately from module mocks.
import {beforeAll,expect,test} from 'bun:test'
import {WorkLedger,workLedger} from './work-admission.ts'
import {proposeCountStrategiesForClosing} from './count-strategies.ts'
import {type WorkKey,workKeys} from './work-kinds.ts'
import {type WorkAmount,workAmount,workAdd,workSub,compareWork} from './work-amount.ts'
import {CountAttemptTickets,planCountRetry,type CountAttemptStop} from './count-retry-budget.ts'
import {type CountDisjointPlan,type CountBodyHistory} from './count-disjoint-funding.ts'
import {completeWorkProfile} from './work-profile.ts'
import {liftedWorkLeaseBudget,withLiftedCase,withLiftedLeaf,liftedLeaseOptions} from './count-lifted-budget.ts'
import {type Law,type Machine,n,same,x} from './machine.ts'
import {type CountFamilyProof} from './count-proof-scope.ts'
import {type CountCert,checkCountedLaws,countedObligations,mcGoal} from '../kernel/kernel.ts'
import {grow,withBudget} from '../kernel/prove.ts'
const a=(n:number)=>workAmount(BigInt(n))
// Runner-only settlement: owner entry + classification + ticket + receipt.
// This tail stays INSIDE plan.body; direct CountFundingOwners reserves zero.
const RUNNER_TERMINAL_TICKS=4
const unitBank=()=>new WorkLedger(Object.fromEntries(workKeys.map(key=>[key,1])) as Record<WorkKey,number>)
const ownerModule='./count-disjoint-funding.ts'
const ownersApi=async()=>{
 const api=await import(ownerModule) as typeof import('./count-disjoint-funding.ts')
 return {...api,fixed:(b:WorkLedger,tickets:CountAttemptTickets,body:number,cases:ReadonlyMap<string,WorkAmount>,leaf=2):Extract<CountDisjointPlan,{kind:'admitted'}>=>{
  let total=a(body);for(const cap of cases.values())total=workAdd(total,cap)
  return {kind:'admitted',caps:{cases,leaf:a(leaf)},body:a(body),minimumBody:a(0),need:total,rootEpoch:b.snapshot().rootEpoch,context:api.countDisjointContext(tickets,b)}
 }}
}
function admitted(plan:CountDisjointPlan):asserts plan is Extract<CountDisjointPlan,{kind:'admitted'}>{
 expect(plan.kind).toBe('admitted');if(plan.kind!=='admitted')throw Error('fixture admission refused: '+plan.reason)
}
function soft(b:WorkLedger,key:string,allocation:number,caseKey?:string):Extract<CountAttemptStop,{kind:'soft-slice'}>{
 return {kind:'soft-slice',key,allocation:a(allocation),scopeId:1,rootEpoch:b.snapshot().rootEpoch,...(caseKey?{caseKey}:{})}
}
beforeAll(()=>{expect(completeWorkProfile.enabled).toBe(true);expect(workLedger.weights.ticks).toEqual(a(1))})

test('46.16a: a case retry changes one cap, not aggregate leaf use or another key cap',()=>{
 const b=unitBank();b.withBudget(a(1000),()=>{
  const keys=[{key:'op:0',allocation:a(10),used:a(9)},{key:'op:1',allocation:a(20),used:a(21)},{key:'leaf',allocation:a(2),used:a(97)}]
  const plan=planCountRetry(keys,soft(b,'op:0',10),[{scope:'test ancestor',remaining:a(900)}],b)
  expect(plan.kind).toBe('admitted');if(plan.kind!=='admitted')throw Error('fixture refusal')
  expect(plan.keys.map(k=>[k.key,k.allocation])).toEqual([['op:0',a(20)],['op:1',a(20)],['leaf',a(2)]])
  expect(plan.funding).toEqual([{key:'op:0',amount:a(20)},{key:'op:1',amount:a(21)},{key:'leaf',amount:a(97)}])
  expect(plan.need).toEqual(a(138))
  expect(keys[2]!.allocation).toEqual(a(2));expect(keys[2]!.used).toEqual(a(97))
 })
})

test('46.17.1: T301-shaped stopped replacement retries under C+body, with leaf counted once',async()=>{
 const {planDisjointCountRound,runDisjointCountRound}=await ownersApi(),b=unitBank()
 b.withBudget(a(960),()=>{
  const tickets=new CountAttemptTickets(),caps={cases:new Map(Array.from({length:7},(_,i)=>['op:'+i,a(32)] as const)),leaf:a(8)}
  const first=planDisjointCountRound(caps,a(297),[],tickets,undefined,b);admitted(first)
  const stopped=runDisjointCountRound(first,tickets,owners=>{
   owners.case('op:0',()=>b.start('ticks',63));return {kind:'proposal',value:'unreachable'}
  },b)
  expect(stopped.result.kind).toBe('unfinished');expect(stopped.receipt?.complete).toBe(false)
  expect(stopped.receipt?.body).toEqual(a(2+RUNNER_TERMINAL_TICKS))
  expect(stopped.receipt?.sum).toEqual(a(3+RUNNER_TERMINAL_TICKS))
  if(stopped.result.kind!=='unfinished'||!stopped.receipt)throw Error('missing unique case stop')
  const history:CountBodyHistory[]=[{completed:false,used:stopped.receipt.body,instance:tickets,rootEpoch:b.snapshot().rootEpoch}]
  const retry=planDisjointCountRound(caps,a(297),history,tickets,stopped.result.stop,b);admitted(retry)
  expect(retry.caps.cases.get('op:0')).toEqual(a(64));expect(retry.caps.leaf).toEqual(a(8))
  expect(retry.minimumBody).toEqual(a(297))
  expect(workSub(retry.need,retry.body)).toEqual(a(256)) // NOT 256+leaf
  const done=runDisjointCountRound(retry,tickets,owners=>{
   owners.case('op:0',()=>b.start('ticks',63))
   for(let i=1;i<7;i++)owners.case('op:'+i,()=>b.start('ticks',1))
   owners.body(()=>b.start('ticks',297))
   return {kind:'proposal',value:'same callback completed'}
  },b)
  expect(done.result).toEqual({kind:'proposal',value:'same callback completed'})
  expect(done.receipt?.body).toEqual(a(300+RUNNER_TERMINAL_TICKS))
  expect(done.receipt?.cases.get('op:0')).toEqual(a(64))
  expect(done.receipt?.sum).toEqual(a(376+RUNNER_TERMINAL_TICKS))
  expect(done.receipt?.sum).toEqual(done.receipt?.round)
  expect(tickets.snapshot()).toMatchObject({started:2,remaining:5,terminal:true})
 })
})

test('46.17.2: H exactly one below C-prime+body floor starts no body and spends no ticket',async()=>{
 const {planDisjointCountRound,runDisjointCountRound}=await ownersApi(),b=unitBank()
 // Header+one-key validation cost 2, leaving H=13. C-prime=8, b0=6.
 b.withBudget(a(15),()=>{
  const tickets=new CountAttemptTickets(),before=b.actual()
  const plan=planDisjointCountRound({cases:new Map([['op:0',a(4)]]),leaf:a(1)},a(6),[],tickets,soft(b,'op:0',4),b)
  expect(b.available()).toEqual(a(13));expect(workSub(b.actual(),before)).toEqual(a(2))
  expect(plan).toEqual({kind:'refused',reason:'headroom'})
  let body=0
  const out=runDisjointCountRound(plan,tickets,()=>{body++;return {kind:'proposal',value:0}},b)
  expect(out.result.kind).toBe('not-started');expect(body).toBe(0)
  expect(tickets.snapshot()).toMatchObject({started:0,remaining:7,terminal:false})
 })
})

test('46.17.3: disjoint case retry keeps every other cap and leaf bit-identical',async()=>{
 const {planDisjointCountRound}=await ownersApi(),b=unitBank()
 b.withBudget(a(1000),()=>{
  const caps={cases:new Map([['op:0',a(40)],['op:1',a(30)]]),leaf:a(7)}
  const next=planDisjointCountRound(caps,a(20),[],new CountAttemptTickets(),soft(b,'op:0',40),b);admitted(next)
  expect(next.caps.cases.get('op:0')).toEqual(a(80));expect(next.caps.cases.get('op:1')).toEqual(caps.cases.get('op:1'))
  expect(next.caps.leaf).toEqual(caps.leaf);expect(caps.cases.get('op:0')).toEqual(a(40))
  expect(workSub(next.need,next.body)).toEqual(a(110))
 })
})

test('46.17.4: doubled leaf needs an actual unchanged case parent and cannot raise it',async()=>{
 const {planDisjointCountRound}=await ownersApi()
 for(const parent of [9,10]){
  const b=unitBank();b.withBudget(a(1000),()=>{
   const caps={cases:new Map([['op:0',a(parent)],['op:1',a(40)]]),leaf:a(5)},tickets=new CountAttemptTickets()
   const next=planDisjointCountRound(caps,a(20),[],tickets,soft(b,'leaf',5,'op:0'),b)
   if(parent===9)expect(next).toEqual({kind:'refused',reason:'parent'})
   else{admitted(next);expect(next.caps.leaf).toEqual(a(10));expect([...next.caps.cases]).toEqual([...caps.cases]);expect(workSub(next.need,next.body)).toEqual(a(50))}
   expect(planDisjointCountRound(caps,a(20),[],tickets,soft(b,'leaf',5),b)).toEqual({kind:'refused',reason:'parent'})
  })
 }
})

function nativeProof():{m:Machine,law:Law,proof:CountFamilyProof}{
 const law:Law={name:'native owner fixture',holds:same(x('value'),n(0))}
 const m:Machine={name:'native owner accounting',params:[],inputs:[],state:{value:n(0)},step:{state:{value:n(0)}}}
 const certs:Record<string,CountCert>={}
 for(const {goal,decls}of countedObligations(m,[law],{[law.name]:{}},0)){
  const base={reads:[],insts:[]},expanded=mcGoal(goal.hyps,decls,base)
  if(!expanded)throw Error('fixture expansion failed')
  const found=grow(expanded,new Map(),{nodes:0,until:Infinity})
  if(!('tree'in found))throw Error('native owner fixture failed')
  certs[goal.name]={...base,tree:found.tree}
 }
 return {m,law,proof:{instances:{[law.name]:{}},certs}}
}
test('46.17.5: real native callback propagates owners without double case scopes; exact sum includes native work',async()=>{
 const {planDisjointCountRound,runDisjointCountRound}=await ownersApi()
 // Keep the native work root independent of Bun/process wall timeouts.
 withBudget(25_000_000,()=>{
  const tickets=new CountAttemptTickets(),caps={cases:new Map([['op:0',a(4_000_000)],['op:1',a(4_000_000)]]),leaf:a(1_000_000)}
  const plan=planDisjointCountRound(caps,a(100_000),[],tickets);admitted(plan)
  const out=runDisjointCountRound(plan,tickets,owners=>{
   const budget=liftedWorkLeaseBudget(a(25_000_000),{owners,cases:Object.fromEntries(plan.caps.cases),leaf:plan.caps.leaf})
   const depth=workLedger.snapshot().activeEndpoints.length
   const built=withLiftedCase(Infinity,budget,false,'op:0',()=>{
    expect(workLedger.snapshot().activeEndpoints).toHaveLength(depth+1)
    return withLiftedLeaf(Infinity,liftedLeaseOptions(budget,'op:0'),500,'native-leaf',()=>{
     expect(workLedger.snapshot().activeEndpoints).toHaveLength(depth+2)
     return nativeProof()
    })
   })
   withLiftedCase(Infinity,budget,false,'op:1',()=>workLedger.start('ticks',3))
   owners.body(()=>expect(checkCountedLaws(built.m,[built.law],built.proof)).toBe(true))
   return {kind:'proposal',value:built.proof}
  })
  expect(out.result.kind).toBe('proposal');expect(out.receipt?.complete).toBe(true)
  const receipt=out.receipt!
  expect(receipt.sum).toEqual(receipt.round)
  expect(receipt.sum).toEqual([...receipt.cases.values()].reduce(workAdd,receipt.body))
  expect(compareWork(receipt.cases.get('op:0')!,a(2))).toBeGreaterThan(0)
  expect(compareWork(receipt.body,a(2+RUNNER_TERMINAL_TICKS))).toBeGreaterThan(0)
 })
})

test('46.17.6: body stop is hard even with unused case credit and round headroom',async()=>{
 const {runDisjointCountRound,fixed}=await ownersApi(),b=unitBank()
 b.withBudget(a(100),()=>{
  const tickets=new CountAttemptTickets(),plan=fixed(b,tickets,6+RUNNER_TERMINAL_TICKS,new Map([['op:0',a(4)]]))
  const out=runDisjointCountRound(plan,tickets,owners=>{
   owners.case('op:0',()=>b.start('ticks',1))
   owners.body(()=>b.start('ticks',6))
   return {kind:'proposal',value:'unreachable'}
  },b)
  expect(out.result.kind).toBe('hard-cap');expect(out.receipt?.complete).toBe(false)
  expect(out.receipt?.body).toEqual(a(3+RUNNER_TERMINAL_TICKS))
  expect(out.receipt?.cases.get('op:0')).toEqual(a(2))
  expect(out.receipt?.sum).toEqual(a(5+RUNNER_TERMINAL_TICKS))
  expect(out.receipt?.sum).toEqual(out.receipt?.round)
  expect(compareWork(workSub(plan.need,out.receipt!.round),a(0))).toBeGreaterThan(0)
  expect(tickets.snapshot()).toMatchObject({started:1,remaining:6,terminal:true})
  let calls=0
  const again=runDisjointCountRound(plan,tickets,()=>{calls++;return {kind:'proposal',value:0}},b)
  expect(again.result.kind).toBe('not-started');expect(calls).toBe(0)
 })
})

test('46.17.7: ownerless or body-owned leaf stops are hard; only a real case can renew leaf',async()=>{
 const {runDisjointCountRound,fixed}=await ownersApi()
 for(const parent of ['none','body','case'] as const){
  const b=unitBank();b.withBudget(a(1000),()=>{
   const tickets=new CountAttemptTickets(),plan=fixed(b,tickets,100,new Map([['op:0',a(50)]]),3)
   const out=runDisjointCountRound(plan,tickets,owners=>{
    const leaf=()=>owners.leaf('physical-leaf',()=>b.start('ticks',4))
    if(parent==='body')owners.body(leaf);else if(parent==='case')owners.case('op:0',leaf);else leaf()
    return {kind:'proposal',value:'unreachable'}
   },b)
   expect(out.result.kind).toBe(parent==='case'?'unfinished':'hard-cap')
   expect(out.receipt?.body).toEqual(a((parent==='body'?4:2)+RUNNER_TERMINAL_TICKS))
   expect(out.receipt?.sum).toEqual(a((parent==='none'?2:4)+RUNNER_TERMINAL_TICKS))
   expect(out.receipt?.sum).toEqual(out.receipt?.round)
   if(out.result.kind==='unfinished')expect(out.result.stop).toMatchObject({key:'leaf',caseKey:'op:0',physicalKey:'physical-leaf'})
   expect(tickets.snapshot().terminal).toBe(parent!=='case')
  })
 }
})

test('46.17.8: separated body segments share one cumulative budget with no case give-back',async()=>{
 const {runDisjointCountRound,fixed}=await ownersApi(),b=unitBank()
 b.withBudget(a(1000),()=>{
  const tickets=new CountAttemptTickets(),plan=fixed(b,tickets,8+RUNNER_TERMINAL_TICKS,new Map([['op:0',a(20)]]))
  const out=runDisjointCountRound(plan,tickets,owners=>{
   owners.body(()=>b.start('ticks',1));owners.case('op:0',()=>b.start('ticks',1));owners.body(()=>b.start('ticks',1))
   owners.body(()=>b.start('ticks',2)) // only 1 productive unit remains; terminal 4 is protected
   return {kind:'proposal',value:'unreachable'}
  },b)
  expect(out.result.kind).toBe('hard-cap');expect(out.receipt?.body).toEqual(a(7+RUNNER_TERMINAL_TICKS))
  expect(out.receipt?.cases.get('op:0')).toEqual(a(2));expect(out.receipt?.sum).toEqual(a(9+RUNNER_TERMINAL_TICKS))
  expect(out.receipt?.sum).toEqual(out.receipt?.round)
  expect(compareWork(workSub(a(20),out.receipt!.cases.get('op:0')!),a(0))).toBeGreaterThan(0)
 })
})

test('46.17: runner reserves settlement inside an unchanged body cap, not a fresh allowance',async()=>{
 const {runDisjointCountRound,fixed}=await ownersApi(),b=unitBank()
 b.withBudget(a(100),()=>{
  const tickets=new CountAttemptTickets(),plan=fixed(b,tickets,RUNNER_TERMINAL_TICKS,new Map([['op:0',a(20)]]))
  const before=b.actual();let calls=0
  const out=runDisjointCountRound(plan,tickets,()=>{calls++;return {kind:'decline',reason:'no productive body fits'}},b)
  expect(plan.body).toEqual(a(4));expect(plan.caps.cases.get('op:0')).toEqual(a(20))
  expect(out.result).toMatchObject({kind:'not-started',reason:'precommit'});expect(calls).toBe(0)
  expect(out.receipt?.body).toEqual(a(RUNNER_TERMINAL_TICKS));expect(out.receipt?.complete).toBe(false)
  expect(out.receipt?.sum).toEqual(out.receipt?.round);expect(workSub(b.actual(),before)).toEqual(a(4))
  expect(tickets.snapshot()).toMatchObject({started:0,remaining:7,terminal:false})
 })
})

test('46.17: direct owners default to no terminal reserve and can use their whole declared body',async()=>{
 const {CountFundingOwners,fixed}=await ownersApi(),b=unitBank()
 b.withBudget(a(100),()=>{
  const tickets=new CountAttemptTickets(),plan=fixed(b,tickets,4,new Map([['op:0',a(20)]])),owners=new CountFundingOwners(plan,b)
  owners.body(()=>b.start('ticks',3)) // one owner-entry tick + three productive ticks
  const receipt=owners.receipt(true)
  expect(receipt.body).toEqual(a(4));expect(receipt.sum).toEqual(a(4));expect(receipt.round).toEqual(a(4))
  expect(tickets.snapshot().started).toBe(0)
 })
})

test('46.17: repeated segments of the same case do not replenish its cap',async()=>{
 const {runDisjointCountRound,fixed}=await ownersApi(),b=unitBank()
 b.withBudget(a(1000),()=>{
  const tickets=new CountAttemptTickets()
  const out=runDisjointCountRound(fixed(b,tickets,50,new Map([['op:0',a(9)]])),tickets,owners=>{
   owners.case('op:0',()=>b.start('ticks',2));owners.case('op:0',()=>b.start('ticks',2));owners.case('op:0',()=>b.start('ticks',4))
   return {kind:'proposal',value:'unreachable'}
  },b)
  expect(out.result.kind).toBe('unfinished');expect(out.receipt?.cases.get('op:0')).toEqual(a(7))
  expect(out.receipt?.body).toEqual(a(2+RUNNER_TERMINAL_TICKS))
  expect(out.receipt?.sum).toEqual(a(9+RUNNER_TERMINAL_TICKS))
  if(out.result.kind==='unfinished')expect(out.result.stop).toMatchObject({key:'op:0',allocation:a(9)})
  expect(out.receipt?.sum).toEqual(out.receipt?.round)
 })
})

test('46.17: interrupted body is not b_min; only largest completed same-instance body counts',async()=>{
 const {planDisjointCountRound}=await ownersApi(),b=unitBank()
 b.withBudget(a(2000),()=>{
  const tickets=new CountAttemptTickets(),rootEpoch=b.snapshot().rootEpoch,caps={cases:new Map([['op:0',a(30)]]),leaf:a(3)}
  const partial:CountBodyHistory={completed:false,used:a(900),instance:tickets,rootEpoch}
  const incomplete=planDisjointCountRound(caps,a(7),[partial],tickets,undefined,b);admitted(incomplete)
  expect(incomplete.minimumBody).toEqual(a(7))
  const done=planDisjointCountRound(caps,a(100),[partial,{completed:true,used:a(12),instance:tickets,rootEpoch},{completed:true,used:a(18),instance:tickets,rootEpoch}],tickets,undefined,b);admitted(done)
  expect(done.minimumBody).toEqual(a(18))
  for(const foreign of [{...partial,completed:true,instance:new CountAttemptTickets()},{...partial,completed:true,rootEpoch:rootEpoch+1}]){
   expect(planDisjointCountRound(caps,a(7),[foreign],tickets,undefined,b)).toEqual({kind:'refused',reason:'inventory'})
  }
 })
})

test('46.17: rescope/stamps/closing remain outside the callback receipt and protected before H',async()=>{
 const {planDisjointCountRound,runDisjointCountRound}=await ownersApi(),b=unitBank()
 b.withBudget(a(1000),()=>{
  b.withBudget(a(600),()=>{
   const tickets=new CountAttemptTickets(),plan=planDisjointCountRound({cases:new Map([['op:0',a(100)]]),leaf:a(5)},a(40),[],tickets,undefined,b);admitted(plan)
   const available=b.available()
   expect(available).not.toBeNull();if(available===null)throw Error('fixture requires a live finite scope')
   expect(plan.need).toEqual(available);expect(compareWork(plan.need,a(600))).toBeLessThan(0)
   const out=runDisjointCountRound(plan,tickets,owners=>{
    owners.case('op:0',()=>b.start('ticks',5));owners.body(()=>b.start('ticks',10));return {kind:'proposal',value:0}
   },b)
   expect(out.result.kind).toBe('proposal');expect(out.receipt?.sum).toEqual(out.receipt?.round)
   const receipt=out.receipt!,before=b.actual()
   b.start('ticks',20,'post-proposal rescope and stamps')
   expect(workSub(b.actual(),before)).toEqual(a(20));expect(receipt.round).toEqual(receipt.sum)
  })
  // This protected root credit was never included in the construction H.
  b.withBudget(a(300),()=>b.start('ticks',250,'closing'))
  expect(compareWork(b.actual(),a(1000))).toBeLessThan(0)
 })
})

test('46.17: owner overlap, unowned work and wrong leaf parent cannot become a soft renewal',async()=>{
 const {runDisjointCountRound,fixed}=await ownersApi()
 for(const defect of ['overlap','gap','parent'] as const){
  const b=unitBank();b.withBudget(a(1000),()=>{
   const tickets=new CountAttemptTickets(),plan=fixed(b,tickets,100,new Map([['op:0',a(50)],['op:1',a(50)]]))
   const out=runDisjointCountRound(plan,tickets,owners=>{
    if(defect==='overlap')owners.body(()=>owners.case('op:0',()=>undefined))
    if(defect==='gap')b.start('ticks',1,'unowned callback work')
    if(defect==='parent')owners.case('op:0',()=>owners.leaf('physical',()=>undefined,'op:1'))
    return {kind:'proposal',value:'unreachable'}
   },b)
   expect(out.result.kind).toBe('hard-cap');expect(tickets.snapshot().terminal).toBe(true)
  })
 }
})

test('46.17: native producer rejects a foreign owner bank before any body or request',async()=>{
 const {CountFundingOwners,fixed}=await ownersApi(),b=unitBank()
 withBudget(25_000_000,()=>b.withBudget(a(1000),()=>{
  const tickets=new CountAttemptTickets(),owners=new CountFundingOwners(fixed(b,tickets,100,new Map([['op:0',a(50)]])),b),before=b.actual()
  const law:Law={name:'foreign-bank target',holds:same(x('value'),n(0))}
  const m:Machine={name:'foreign-bank fixture',params:[],inputs:[],state:{value:n(0)},step:{state:{value:n(0)}}}
  const budget=liftedWorkLeaseBudget(a(1000),{owners}),calls={requests:0}
  expect(()=>proposeCountStrategiesForClosing(m,[law],law,Infinity,()=>{calls.requests++;throw Error('foreign-owner request must not run')},undefined,Infinity,[law],budget)).toThrow('native work ledger')
  expect(owners.ownsBank(workLedger)).toBe(false);expect(b.actual()).toEqual(before);expect(calls.requests).toBe(0)
 }))
})

test('D3: plan for tickets A cannot start tickets B, even with identical fresh counters',async()=>{
 const {planDisjointCountRound,runDisjointCountRound}=await ownersApi(),b=unitBank()
 b.withBudget(a(2000),()=>{
  const ticketsA=new CountAttemptTickets(),ticketsB=new CountAttemptTickets(),caps={cases:new Map([['op:0',a(40)]]),leaf:a(4)}
  const plan=planDisjointCountRound(caps,a(40),[],ticketsA,undefined,b);admitted(plan)
  const beforeA=ticketsA.snapshot(),beforeB=ticketsB.snapshot();let calls=0
  const wrong=runDisjointCountRound(plan,ticketsB,()=>{calls++;return {kind:'decline',reason:'wrong instance entered'}},b)
  expect(wrong.result.kind).toBe('not-started');expect(calls).toBe(0)
  expect(ticketsA.snapshot()).toEqual(beforeA);expect(ticketsB.snapshot()).toEqual(beforeB)
  // Positive control is a fresh plan under the same valid instance/context,
  // not replay of possibly depleted funding from the rejected admission.
  const fresh=planDisjointCountRound(caps,a(40),[],ticketsA,undefined,b);admitted(fresh)
  const valid=runDisjointCountRound(fresh,ticketsA,owners=>{
   owners.body(()=>b.start('ticks',1));return {kind:'decline',reason:'valid callback'}
  },b)
  expect(valid.result.kind).toBe('decline');expect(ticketsA.snapshot().started).toBe(1)
 })
})

test('D3: numerically equal root epochs on another ledger do not authorize a prepared plan',async()=>{
 const {planDisjointCountRound,runDisjointCountRound}=await ownersApi(),aBank=unitBank(),bBank=unitBank()
 aBank.withBudget(a(2000),()=>{
  const tickets=new CountAttemptTickets(),caps={cases:new Map([['op:0',a(40)]]),leaf:a(4)}
  const plan=planDisjointCountRound(caps,a(40),[],tickets,undefined,aBank);admitted(plan)
  bBank.withBudget(a(2000),()=>{
   expect(bBank.snapshot().rootEpoch).toBe(aBank.snapshot().rootEpoch)
   const before=tickets.snapshot();let calls=0
   const out=runDisjointCountRound(plan,tickets,()=>{calls++;return {kind:'decline',reason:'foreign ledger entered'}},bBank)
   expect(out.result.kind).toBe('not-started');expect(calls).toBe(0);expect(tickets.snapshot()).toEqual(before)
  })
 })
})

test('D3: exited parent context cannot be replaced by a funded sibling in the same root',async()=>{
 const {planDisjointCountRound,runDisjointCountRound}=await ownersApi(),b=unitBank()
 b.withBudget(a(2000),()=>{
  const tickets=new CountAttemptTickets();let plan:CountDisjointPlan|undefined,parentId:number|undefined
  b.withBudget(a(500),()=>{
   parentId=b.currentScope()!.id
   plan=planDisjointCountRound({cases:new Map([['op:0',a(40)]]),leaf:a(4)},a(40),[],tickets,undefined,b);admitted(plan)
  })
  b.withBudget(a(500),()=>{
   expect(b.currentScope()!.id).not.toBe(parentId)
   const before=tickets.snapshot();let calls=0
   const out=runDisjointCountRound(plan!,tickets,()=>{calls++;return {kind:'decline',reason:'sibling parent entered'}},b)
   expect(out.result.kind).toBe('not-started');expect(calls).toBe(0);expect(tickets.snapshot()).toEqual(before)
  })
 })
})

test('D3: false last-moment eligibility spends no ticket or producer work',async()=>{
 const {planDisjointCountRound,runDisjointCountRound}=await ownersApi(),b=unitBank()
 b.withBudget(a(2000),()=>{
  const tickets=new CountAttemptTickets(),caps={cases:new Map([['op:0',a(40)]]),leaf:a(4)}
  const plan=planDisjointCountRound(caps,a(40),[],tickets,undefined,b);admitted(plan)
  const before=tickets.snapshot();let checks=0,calls=0
  const out=runDisjointCountRound(plan,tickets,()=>{calls++;return {kind:'decline',reason:'ineligible producer entered'}},b,()=>{
   checks++;expect(tickets.snapshot()).toEqual(before);return false
  })
  expect(checks).toBe(1);expect(out.result.kind).toBe('not-started')
  expect(out.receipt?.body).toEqual(a(1+RUNNER_TERMINAL_TICKS))
  expect(out.receipt?.sum).toEqual(a(1+RUNNER_TERMINAL_TICKS));expect(out.receipt?.complete).toBe(false)
  expect(calls).toBe(0);expect(tickets.snapshot()).toEqual(before)
  const fresh=planDisjointCountRound(caps,a(40),[],tickets,undefined,b);admitted(fresh)
  const allowed=runDisjointCountRound(fresh,tickets,owners=>{
   calls++;owners.body(()=>b.start('ticks',1));return {kind:'decline',reason:'eligible control'}
  },b,()=>true)
  expect(allowed.result.kind).toBe('decline');expect(calls).toBe(1);expect(tickets.snapshot().started).toBe(1)
  expect(allowed.receipt?.body).toEqual(a(4+RUNNER_TERMINAL_TICKS));expect(allowed.receipt?.complete).toBe(true)
 })
})

test('D3: ticket generation is checked again after the eligibility callback',async()=>{
 const {planDisjointCountRound,runDisjointCountRound}=await ownersApi(),b=unitBank()
 b.withBudget(a(2000),()=>{
  const tickets=new CountAttemptTickets(),plan=planDisjointCountRound({cases:new Map([['op:0',a(40)]]),leaf:a(4)},a(40),[],tickets,undefined,b);admitted(plan)
  let calls=0,checks=0
  const out=runDisjointCountRound(plan,tickets,()=>{calls++;return {kind:'decline',reason:'changed generation entered'}},b,()=>{
   checks++;expect(tickets.start()).toBe(true);tickets.finish('unfinished');return true
  })
  expect(checks).toBe(1);expect(out.result.kind).toBe('not-started');expect(calls).toBe(0)
  expect(out.receipt?.body).toEqual(a(1+RUNNER_TERMINAL_TICKS))
  expect(out.receipt?.sum).toEqual(a(1+RUNNER_TERMINAL_TICKS));expect(out.receipt?.complete).toBe(false)
  expect(tickets.snapshot()).toMatchObject({started:1,remaining:6,terminal:false})
 })
})

test('D3: changing the same ticket instance after preparation invalidates that prepared round',async()=>{
 const {planDisjointCountRound,runDisjointCountRound}=await ownersApi(),b=unitBank()
 b.withBudget(a(2000),()=>{
  const tickets=new CountAttemptTickets(),plan=planDisjointCountRound({cases:new Map([['op:0',a(40)]]),leaf:a(4)},a(40),[],tickets,undefined,b);admitted(plan)
  expect(tickets.start()).toBe(true);tickets.finish('unfinished')
  const before=tickets.snapshot();let calls=0
  const out=runDisjointCountRound(plan,tickets,()=>{calls++;return {kind:'decline',reason:'stale attempt entered'}},b)
  expect(out.result.kind).toBe('not-started');expect(calls).toBe(0);expect(tickets.snapshot()).toEqual(before)
 })
})

test('46.17: spent live headroom and a stale root cannot spend a prepared ticket',async()=>{
 const {planDisjointCountRound,runDisjointCountRound}=await ownersApi(),b=unitBank(),tickets=new CountAttemptTickets()
 let saved:CountDisjointPlan|undefined
 b.withBudget(a(1000),()=>{
  saved=planDisjointCountRound({cases:new Map([['op:0',a(40)]]),leaf:a(4)},a(40),[],tickets,undefined,b);admitted(saved)
  // Keep the SAME bank, ticket generation and parent scope. Only live H
  // decreases; rejection must not be accidentally supplied by the context gate.
  b.start('ticks',1,'work between preparation and atomic admission')
  expect(b.available()).toEqual(workSub(saved.need,a(1)))
  let calls=0
  const out=runDisjointCountRound(saved,tickets,()=>{calls++;return {kind:'proposal',value:0}},b)
  expect(out.result).toMatchObject({kind:'not-started',reason:'headroom'})
  expect(calls).toBe(0);expect(tickets.snapshot().started).toBe(0)
 })
 b.withBudget(a(1000),()=>{
  const out=runDisjointCountRound(saved!,tickets,()=>{throw Error('stale callback started')},b)
  expect(out.result).toMatchObject({kind:'not-started',reason:'missing-root'})
  expect(tickets.snapshot().started).toBe(0)
 })
})
