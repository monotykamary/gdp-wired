import {expect,test} from 'bun:test'
import {CountAttemptTickets,countAttemptStop,planCountRetry,type CountRetryKey} from './count-retry-budget.ts'
import {BudgetExpired,WorkLedger} from './work-admission.ts'
import {runCountRetryRound} from './count-retry-round.ts'
import {workAmount} from './work-amount.ts'
import {type WorkKey,workKeys} from './work-kinds.ts'
const bank=()=>new WorkLedger(Object.fromEntries(workKeys.map(key=>[key,1])) as Record<WorkKey,number>)
const amount=(n:number)=>workAmount(BigInt(n))
function stopAt(b:WorkLedger,cap:number,outer=100){
 return b.withBudget(amount(outer),()=>{let id=0,error:unknown
  try{b.withBudget(amount(cap),()=>{id=b.currentScope()!.id;b.start('ticks',cap+1)})}catch(e){error=e}
  return countAttemptStop(error,[{key:'a',allocation:amount(cap),scopeId:id,rootEpoch:b.snapshot().rootEpoch}],b)
 })
}
test('initial unfinished consumes a ticket and every started round decreases it',()=>{
 const tickets=new CountAttemptTickets(6)
 for(let i=0;i<4;i++){
  const before=tickets.snapshot().remaining;expect(tickets.start()).toBe(true)
  expect(tickets.snapshot().remaining).toBe(before-1)
  tickets.finish(i===3?'proposal':'unfinished')
 }
 expect(tickets.snapshot()).toEqual({remaining:3,started:4,active:false,terminal:true})
 expect(tickets.start()).toBe(false)
})
test('F=0 and F=6 have exactly one initial plus F retries, never renewable',()=>{
 for(const fuel of [0,6]){
  const tickets=new CountAttemptTickets(fuel);let runs=0
  while(tickets.start()){runs++;tickets.finish('unfinished')}
  expect(runs).toBe(fuel+1);expect(tickets.snapshot().terminal).toBe(true)
  expect(()=>tickets.finish('unfinished')).toThrow()
 }
})
test('successful but stranded and ordinary decline instances are terminal',()=>{
 for(const outcome of ['proposal','decline','hard-cap'] as const){
  const tickets=new CountAttemptTickets();expect(tickets.start()).toBe(true);tickets.finish(outcome)
  expect(tickets.start()).toBe(false);expect(tickets.snapshot().started).toBe(1)
  expect(tickets.snapshot().remaining).toBe(6)
 }
})
test('only authenticated strictly local capacity becomes soft-slice',()=>{
 const b=bank();expect(stopAt(b,2).kind).toBe('soft-slice')
 expect(stopAt(b,2,2).kind).toBe('hard-cap')
 expect(countAttemptStop(new BudgetExpired('leaf a'),[],b).kind).toBe('hard-cap')
})
test('retry doubles only the raised key and funds all other previous use exactly',()=>{
 const b=bank(),keys:CountRetryKey[]=[{key:'a',allocation:amount(2),used:amount(2)},
  {key:'b',allocation:amount(3),used:amount(4)},{key:'c',allocation:amount(1),used:amount(0)}]
 b.withBudget(amount(200),()=>{
  const plan=planCountRetry(keys,{kind:'soft-slice',key:'a',allocation:amount(2),scopeId:1,rootEpoch:1},[{scope:'member',remaining:amount(20)}],b)
  expect(plan.kind).toBe('admitted')
  if(plan.kind!=='admitted')throw Error('missing retry plan')
  expect(plan.need).toEqual(amount(9));expect(plan.keys.map(key=>key.allocation)).toEqual([amount(4),amount(3),amount(1)]);expect(plan.funding?.map(key=>key.amount)).toEqual([amount(4),amount(4),amount(1)])
 })
})
test('prepared one-unit-short ancestor or live reservation starts no callback and spends nothing',()=>{
 const b=bank(),keys=[{key:'a',allocation:amount(2),used:amount(2)}],stop={kind:'soft-slice' as const,key:'a',allocation:amount(2),scopeId:1,rootEpoch:1}
 b.withBudget(amount(1000),()=>{
  const plan=planCountRetry(keys,stop,[{scope:'member',remaining:amount(100)}],b)
  expect(plan.kind).toBe('admitted');const before=b.actual();let entered=0
  const body=()=>{entered++;return {kind:'proposal' as const,value:1}}
  for(const ancestor of ['member','component','tier']){
   const tickets=new CountAttemptTickets()
   b.withBudget(amount(3),()=>expect(runCountRetryRound(plan,tickets,body,{bank:b})).toEqual({kind:'not-started',reason:'headroom'}))
   expect(tickets.snapshot().started,ancestor).toBe(0)
  }
  const hold=Number(b.available()!.num/b.available()!.den)-3
  b.withChunk('ticks',hold,()=>{
   const reserved=b.reserved(),tickets=new CountAttemptTickets()
   expect(runCountRetryRound(plan,tickets,body,{bank:b})).toEqual({kind:'not-started',reason:'headroom'})
   expect(b.reserved()).toEqual(reserved);expect(tickets.snapshot().started).toBe(0)
  })
  expect(entered).toBe(0);expect(b.actual()).toEqual(before)
 })
})
test('paid preparation is separate, and unexpected repeated body work cannot exceed the round',()=>{
 const b=bank(),keys=[{key:'a',allocation:amount(2),used:amount(2)}]
 b.withBudget(amount(1000),()=>{
  const initial=b.actual(),plan=planCountRetry(keys,{kind:'soft-slice',key:'a',allocation:amount(2),scopeId:1,rootEpoch:1},[],b)
  expect(b.actual().num>initial.num).toBe(true);const before=b.actual(),tickets=new CountAttemptTickets();let entered=0
  const result=runCountRetryRound(plan,tickets,()=>{entered++;b.start('ticks',2);b.start('ticks',2);return {kind:'proposal',value:1}},{bank:b})
  expect(result.kind).toBe('hard-cap');expect(entered).toBe(1)
  expect(b.actual().num-before.num).toBeLessThanOrEqual(4n);expect(b.reserved().num).toBe(0n)
  expect(tickets.snapshot()).toMatchObject({remaining:6,started:1,terminal:true})
 })
})
test('old-root causes and prepared plans cannot authorize a new root',()=>{
 const b=bank(),captured=b.withBudget(amount(1000),()=>{
  let error:unknown,scopeId=0;const rootEpoch=b.snapshot().rootEpoch
  try{b.withBudget(amount(2),()=>{scopeId=b.currentScope()!.id;b.start('ticks',3)})}catch(e){error=e}
  const slice={key:'a',allocation:amount(2),scopeId,rootEpoch},stop=countAttemptStop(error,[slice],b)
  expect(stop.kind).toBe('soft-slice')
  const plan=planCountRetry([{key:'a',allocation:amount(2),used:amount(0)}],stop,[],b)
  expect(plan.kind).toBe('admitted');return {error,slice,stop,plan}
 })
 expect(countAttemptStop(captured.error,[captured.slice],b).kind).toBe('hard-cap')
 const tickets=new CountAttemptTickets();let entered=0;const run=()=>{entered++;return {kind:'proposal' as const,value:1}}
 const before=b.actual();expect(runCountRetryRound(captured.plan,tickets,run,{bank:b})).toEqual({kind:'not-started',reason:'missing-root'});expect(b.actual()).toEqual(before)
 b.withBudget(amount(1000),()=>{
  expect(countAttemptStop(captured.error,[captured.slice],b).kind).toBe('hard-cap')
  expect(planCountRetry([{key:'a',allocation:amount(2),used:amount(0)}],captured.stop,[],b)).toMatchObject({kind:'refused',reason:'missing-root'})
  const before=b.actual();expect(runCountRetryRound(captured.plan,tickets,run,{bank:b})).toEqual({kind:'not-started',reason:'missing-root'});expect(b.actual()).toEqual(before)
 })
 expect(entered).toBe(0);expect(tickets.snapshot().started).toBe(0)
})
test('an authenticated root refusal cannot be relabelled as a soft slice',()=>{
 const b=bank();b.withBudget(amount(2),()=>{
  const scopeId=b.currentScope()!.id,rootEpoch=b.snapshot().rootEpoch;let error:unknown
  try{b.start('ticks',3)}catch(e){error=e}
  expect(countAttemptStop(error,[{key:'fake-case',allocation:amount(2),scopeId,rootEpoch}],b).kind).toBe('hard-cap')
 })
})

test('unknown or changed keys and unbounded roots cannot mint a retry grant',()=>{
 const b=bank(),keys=[{key:'a',allocation:amount(2),used:amount(0)}]
 expect(planCountRetry(keys,{kind:'soft-slice',key:'x',allocation:amount(2),scopeId:1,rootEpoch:1},[],b)).toMatchObject({kind:'refused',reason:'unknown-key'})
 expect(planCountRetry(keys,{kind:'soft-slice',key:'a',allocation:amount(1),scopeId:1,rootEpoch:1},[],b)).toMatchObject({kind:'refused',reason:'changed-slice'})
 expect(planCountRetry(keys,{kind:'soft-slice',key:'a',allocation:amount(2),scopeId:1,rootEpoch:1},[],b)).toMatchObject({kind:'refused',reason:'missing-root'})
})
