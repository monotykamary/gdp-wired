import {expect,spyOn,test} from 'bun:test'
import {type CountCert,type Goal,check,checkMC} from '../kernel/kernel.ts'
import {type Law,type Machine,atMost,n,plus,same,x} from './machine.ts'
import {deferIntermediateCountChecks,finishCountStrategy} from './count-strategy.ts'
import {minimalViewFirst} from './count-minimal-view.ts'
import {rebaseLiftedLoadCandidate} from './count-lifted-load.ts'
import {rebasePath} from './count-rebase-path.ts'
import * as replay from './count-replay-skeleton.ts'
import {rowsAt} from '../kernel/prove.ts'
import {env,solve} from './solver.ts'
import {stabilizeGuardedTree} from './count-stabilize-tree.ts'
import {completeWorkProfile} from './work-profile.ts'
import {workAmount,compareWork,workFromExact} from './work-amount.ts'
import {workAdmissionSnapshot,workLedger} from './work-admission.ts'
import {liftedLeaseOptions,liftedWorkLeaseBudget,withLiftedCase,withLiftedLeaf} from './count-lifted-budget.ts'
const withG1Flag=<T>(value:string|undefined,run:()=>T):T=>{
 const keys=['GDP_COUNT_G1_OWNED_DEFER','GDP_COUNT_REPLAY_FORWARD','GDP_COUNT_C2_LEMMAS','GDP_COUNT_C2_REPLAY','GDP_COUNT_DEFER_CHECKS'] as const,old=keys.map(key=>env[key])
 for(const key of keys)env[key]='1'
 if(value===undefined)delete env.GDP_COUNT_G1_OWNED_DEFER;else env.GDP_COUNT_G1_OWNED_DEFER=value
 try{return run()}finally{keys.forEach((key,i)=>{if(old[i]===undefined)delete env[key];else env[key]=old[i]})}
}
const leased=completeWorkProfile.enabled?test:test.skip
const inLeaf=<T>(run:()=>T):T=>{
 const original=workAmount(100_000_000n),plan=liftedWorkLeaseBudget(original)
 return workLedger.withBudget(original,()=>withLiftedCase(Infinity,plan,false,'op:1',()=>withLiftedLeaf(Infinity,liftedLeaseOptions(plan,'op:1'),500,'leaf:load:g1-test',()=>{
  const before=workAdmissionSnapshot(),result=run(),after=workAdmissionSnapshot()
  expect(after.rootEpoch).toBe(before.rootEpoch)
  expect(after.activeEndpoints.map(e=>e.id)).toEqual(before.activeEndpoints.map(e=>e.id))
  expect(after.activeEndpoints).toHaveLength(3)
  expect(compareWork(workFromExact(after.actual),workFromExact(before.actual))).toBeGreaterThanOrEqual(0)
  return result
 })))
}
leased('G1 lease: both explicit composition options are required',()=>inLeaf(()=>{
 for(const compose of [false,true])for(const defer of [false,true])expect(deferIntermediateCountChecks({deferToComposition:compose,deferIntermediateChecks:defer})).toBe(compose&&defer)
}))
leased('G1 lease: deferred minimal and stabilization proposals do not gain native authority',()=>inLeaf(()=>{
 const goal:Goal={name:'satisfiable',hyps:[atMost(n(0),x('a'))]},empty:Goal={name:'empty',hyps:[]},root=new Map(),fake=()=>({tree:{leaf:[]},nodes:0})
 expect(minimalViewFirst(goal,empty,root,Infinity,fake).tree).toBeUndefined()
 const proposed=minimalViewFirst(goal,empty,root,Infinity,fake,root,{deferCheck:true})
 expect(proposed.tree).toBeDefined();expect(proposed.tree&&check(goal,proposed.tree,root)).toBe(false)
 const tree={leaf:[]},roots=new Map([[tree,root]])
 expect(stabilizeGuardedTree(goal,tree,[],[],roots,Infinity).tree).toBeUndefined()
 const stable=stabilizeGuardedTree(goal,tree,[],[],roots,Infinity,{deferCheck:true})
 expect(stable.tree).toBeDefined();expect(stable.tree&&check(goal,stable.tree,root)).toBe(false)
}))
leased('G1 lease: standalone finish still checks; unchecked composition is not a certificate',()=>inLeaf(()=>{
 const m:Machine={name:'constant fixture',params:[],inputs:[],state:{},maps:{},step:{}},law:Law={name:'constant',holds:same(n(0),n(0))},cert:CountCert={reads:[],insts:[],tree:{leaf:[]}}
 expect(finishCountStrategy(m,[law],law,{},'none',cert,Infinity,()=>cert,undefined,{deferIntermediateChecks:true})).toBeUndefined()
 const proposal=finishCountStrategy(m,[law],law,{},'none',cert,Infinity,()=>cert,undefined,{deferToComposition:true,deferIntermediateChecks:true})
 expect(proposal?.status).toBe('unchecked')
 expect(checkMC([law.holds],[],proposal!.certs['constant @step']!)).toBe(false)
}))
for(const compose of [false,true])for(const defer of [false,true])leased('fresh load fallback forwards composition deferral '+compose+'/'+defer,()=>withG1Flag('1',()=>inLeaf(()=>{
 const root=new Map(),sum=plus(x('a'),x('b')),full:Goal={name:'full',hyps:[atMost(x('a'),n(0)),atMost(x('b'),n(0)),atMost(n(1),sum)]},small:Goal={name:'small',hyps:[atMost(sum,n(0)),atMost(n(1),sum)]}
 const direct=solve(rowsAt(small,root),2000);expect(direct.kind).toBe('refuted');if(direct.kind!=='refuted')throw Error('fixture did not refute')
 const hint={leaf:direct.steps};expect(rebasePath(small,hint,root,root,Infinity,full)).toBeUndefined()
 const original=replay.replayLinearSkeleton;let calls=0,seen:boolean|undefined
 const spy=spyOn(replay,'replayLinearSkeleton').mockImplementation((...args)=>{calls++;seen=args[4]?.deferCheck;return original(...args)})
 try{const tree=rebaseLiftedLoadCandidate(small,hint,root,Infinity,full,{deferToComposition:compose,deferIntermediateChecks:defer})
  expect(calls).toBe(1);expect(seen).toBe(compose&&defer);expect(tree).toBeDefined();expect(tree&&check(full,tree,root)).toBe(true)
 }finally{spy.mockRestore()}
})))
leased('fresh load fallback still rejects a false minimal projection with G1 enabled',()=>withG1Flag('1',()=>inLeaf(()=>{
 const full:Goal={name:'sat',hyps:[same(x('a'),n(0))]},small:Goal={name:'invalid projection',hyps:[atMost(n(1),n(0))]},root=new Map()
 const direct=solve(rowsAt(small,root),2000);expect(direct.kind).toBe('refuted');if(direct.kind!=='refuted')throw Error('fixture did not refute')
 const tree=rebaseLiftedLoadCandidate(small,{leaf:direct.steps},root,Infinity,full,{deferToComposition:true,deferIntermediateChecks:true})
 expect(tree).toBeUndefined()
})))
for(const flag of [undefined,'0','true'])leased('G1 OFF preserves pre-G1 bytes with C2 and replay forwarding ON: '+String(flag),()=>withG1Flag(flag,()=>inLeaf(()=>{
 const root=new Map(),sum=plus(x('a'),x('b')),full:Goal={name:'full',hyps:[atMost(x('a'),n(0)),atMost(x('b'),n(0)),atMost(n(1),sum)]},small:Goal={name:'small',hyps:[atMost(sum,n(0)),atMost(n(1),sum)]}
 const direct=solve(rowsAt(small,root),2000);expect(direct.kind).toBe('refuted');if(direct.kind!=='refuted')throw Error('fixture did not refute')
 const hint={leaf:direct.steps},original=replay.replayLinearSkeleton
 // Exact pre-G1 expression, including its four-argument checked fallback.
 const before=rebasePath(small,hint,root,root,Infinity,full)??original(full,hint,root,Infinity)
 let calls=0,forwarded:unknown='not called',argc=0
 const spy=spyOn(replay,'replayLinearSkeleton').mockImplementation((...args)=>{calls++;forwarded=args[4];argc=args.length;return original(...args)})
 try{
  const after=rebaseLiftedLoadCandidate(small,hint,root,Infinity,full,{deferToComposition:true,deferIntermediateChecks:true})
  expect(env.GDP_COUNT_C2_REPLAY).toBe('1');expect(env.GDP_COUNT_DEFER_CHECKS).toBe('1');expect(env.GDP_COUNT_REPLAY_FORWARD).toBe('1')
  expect(calls).toBe(1);expect(argc).toBe(4);expect(forwarded).toBeUndefined()
  expect(JSON.stringify(after)).toBe(JSON.stringify(before));expect(after).toBeDefined();expect(after&&check(full,after,root)).toBe(true)
 }finally{spy.mockRestore()}
})))
