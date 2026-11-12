import {afterEach,beforeEach,expect,spyOn,test} from 'bun:test'
import {type Goal,check} from '../kernel/kernel.ts'
import {atMost,n,plus,same,x} from './machine.ts'
import {minimalViewFirst} from './count-minimal-view.ts'
import * as replay from './count-replay-skeleton.ts'
import {rebasePath} from './count-rebase-path.ts'
import {rowsAt} from '../kernel/prove.ts'
import {env,solve} from './solver.ts'
import {completeWorkProfile} from './work-profile.ts'
import {workAmount} from './work-amount.ts'
import {BudgetExpired,workAdmissionSnapshot,workLedger} from './work-admission.ts'
import {liftedLeaseOptions,liftedWorkLeaseBudget,withLiftedCase,withLiftedLeaf,type LiftedWorkSlice} from './count-lifted-budget.ts'
const flags=['GDP_COUNT_REPLAY_FORWARD','GDP_COUNT_G1_OWNED_DEFER','GDP_COUNT_C2_LEMMAS','GDP_COUNT_C2_REPLAY','GDP_COUNT_DEFER_CHECKS'] as const
let saved:(string|undefined)[]=[]
beforeEach(()=>{saved=flags.map(key=>env[key]);for(const key of flags)env[key]='1'})
afterEach(()=>{flags.forEach((key,i)=>{if(saved[i]===undefined)delete env[key];else env[key]=saved[i]})})
const leased=completeWorkProfile.enabled?test:test.skip
const original=workAmount(100_000_000n)
for(const [deferCheck,deferReplayCheck,wanted]of [[false,false,false],[true,false,false],[false,true,false],[true,true,true]]as const)leased('owned replay lease forwarding '+deferCheck+'/'+deferReplayCheck,()=>{
 const plan=liftedWorkLeaseBudget(original),base=replay.replayLinearSkeleton;let seen:boolean|undefined
 const spy=spyOn(replay,'replayLinearSkeleton').mockImplementation((...args)=>{seen=args[4]?.deferCheck;return base(...args)})
 try{workLedger.withBudget(original,()=>{
  const epoch=workAdmissionSnapshot().rootEpoch
  withLiftedCase(Infinity,plan,false,'op:5',()=>withLiftedLeaf(Infinity,liftedLeaseOptions(plan,'op:5'),500,'leaf:replacement:forward-test',()=>{
   const before=workAdmissionSnapshot(),sum=plus(x('a'),x('b')),full:Goal={name:'full',hyps:[atMost(x('a'),n(0)),atMost(x('b'),n(0)),atMost(n(1),sum)]},small:Goal={name:'small',hyps:[atMost(sum,n(0)),atMost(n(1),sum)]}
   const result=minimalViewFirst(full,small,new Map(),Infinity,undefined,new Map(),{deferCheck,deferReplayCheck})
   expect(seen).toBe(wanted);expect(result.kind).toBe('proof');expect(result.tree&&check(full,result.tree)).toBe(true)
   expect(workAdmissionSnapshot().rootEpoch).toBe(epoch)
   expect(workAdmissionSnapshot().activeEndpoints.map(e=>e.id)).toEqual(before.activeEndpoints.map(e=>e.id))
  }))
  expect(workAdmissionSnapshot().activeEndpoints).toHaveLength(1)
 })}finally{spy.mockRestore()}
})
leased('owned replay lease cannot certify a contradictory projection of a satisfiable full goal',()=>{
 const plan=liftedWorkLeaseBudget(original)
 workLedger.withBudget(original,()=>withLiftedCase(Infinity,plan,false,'op:5',()=>withLiftedLeaf(Infinity,liftedLeaseOptions(plan,'op:5'),500,'leaf:replacement:bad-projection',()=>{
  const full:Goal={name:'sat',hyps:[same(x('a'),n(0))]},small:Goal={name:'invalid projection',hyps:[atMost(n(1),n(0))]}
  const result=minimalViewFirst(full,small,new Map(),Infinity,undefined,new Map(),{deferCheck:true,deferReplayCheck:true})
  expect(result.kind).toBe('rejected');expect(result.tree).toBeUndefined()
 })))
})
leased('owned replay propagates exact leaf exhaustion without a new root or fallback credit',()=>{
 const slices:LiftedWorkSlice[]=[],plan=liftedWorkLeaseBudget(original,{leaf:workAmount(1n),observe:s=>slices.push(s)})
 workLedger.withBudget(original,()=>{
  const epoch=workAdmissionSnapshot().rootEpoch;let caught:unknown
  try{withLiftedCase(Infinity,plan,false,'op:5',()=>{
   const sum=plus(x('a'),x('b')),full:Goal={name:'full',hyps:[atMost(x('a'),n(0)),atMost(x('b'),n(0)),atMost(n(1),sum)]},small:Goal={name:'small',hyps:[atMost(sum,n(0)),atMost(n(1),sum)]}
   withLiftedLeaf(Infinity,liftedLeaseOptions(plan,'op:5'),500,'leaf:replacement:tiny',()=>minimalViewFirst(full,small,new Map(),Infinity,undefined,new Map(),{deferCheck:true,deferReplayCheck:true}))
  })}catch(error){caught=error}
  expect(caught).toBeInstanceOf(BudgetExpired)
  const failure=workLedger.capacityRefusal(caught),leaf=slices.find(s=>s.kind==='leaf')
  expect(leaf).toBeDefined();expect(failure?.limiting.map(({kind,id})=>({kind,id}))).toEqual([{kind:'scope',id:leaf!.scopeId}])
  expect(workAdmissionSnapshot().rootEpoch).toBe(epoch);expect(workAdmissionSnapshot().activeEndpoints).toHaveLength(1)
 })
})
for(const flag of [undefined,'0','true'])leased('replay forwarding OFF preserves pre-forward bytes with C2 and G1 ON: '+String(flag),()=>{
 if(flag===undefined)delete env.GDP_COUNT_REPLAY_FORWARD;else env.GDP_COUNT_REPLAY_FORWARD=flag
 const plan=liftedWorkLeaseBudget(original)
 workLedger.withBudget(original,()=>withLiftedCase(Infinity,plan,false,'op:5',()=>withLiftedLeaf(Infinity,liftedLeaseOptions(plan,'op:5'),500,'leaf:replacement:forward-off',()=>{
  const root=new Map(),sum=plus(x('a'),x('b')),full:Goal={name:'full',hyps:[atMost(x('a'),n(0)),atMost(x('b'),n(0)),atMost(n(1),sum)]},small:Goal={name:'small',hyps:[atMost(sum,n(0)),atMost(n(1),sum)]}
  const direct=solve(rowsAt(small,root),2000);expect(direct.kind).toBe('refuted');if(direct.kind!=='refuted')throw Error('fixture did not refute')
  const base=replay.replayLinearSkeleton,before=rebasePath(small,{leaf:direct.steps},root,root,Infinity,full)??base(full,{leaf:direct.steps},root,Infinity)
  let forwarded:unknown='not called',argc=0
  const spy=spyOn(replay,'replayLinearSkeleton').mockImplementation((...args)=>{forwarded=args[4];argc=args.length;return base(...args)})
  try{
   const result=minimalViewFirst(full,small,root,Infinity,undefined,root,{deferCheck:true,deferReplayCheck:true})
   expect(env.GDP_COUNT_C2_REPLAY).toBe('1');expect(env.GDP_COUNT_DEFER_CHECKS).toBe('1');expect(env.GDP_COUNT_G1_OWNED_DEFER).toBe('1')
   expect(argc).toBe(4);expect(forwarded).toBeUndefined();expect(result.kind).toBe('proof')
   expect(JSON.stringify(result.tree)).toBe(JSON.stringify(before));expect(result.tree&&check(full,result.tree,root)).toBe(true)
  }finally{spy.mockRestore()}
 })))
})
