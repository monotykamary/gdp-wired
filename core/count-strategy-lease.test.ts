import {expect,test} from 'bun:test'
import {type C,type E,type Machine,all,any,atMost,get,ite,less,minus,n,not,plus,same,times,x} from './machine.ts'
import {quorumLaws,quorumLawProvenance} from './quorum-laws.ts'
import {countedAttempts,certFor} from './counts.ts'
import {proveCountStrategies,proposeCountStrategiesForClosing} from './count-strategies.ts'
import {liftedWorkLeaseBudget,type LiftedWorkBudget,type LiftedWorkSlice} from './count-lifted-budget.ts'
import {completeWorkProfile} from './work-profile.ts'
import {BudgetExpired,workLedger} from './work-admission.ts'
import {workAmount,workShare,compareWork} from './work-amount.ts'
import {checkMC,countedObligations} from '../kernel/kernel.ts'
import {env} from './solver.ts'
// Same bounded native frame shape as F's sealed exact-plan control, reached
// through A's production dispatcher instead of calling the composer directly.
function fixture(){
 const bit=(c:C)=>ite(c,n(1),n(0)),cell=(r:E,k:E)=>same(get('Rows',plus(times(8,r),k)),n(1)),member=(k:E)=>atMost(n(1),get('Proposal',k))
 const cnt=(body:(k:E)=>C)=>({j:'j',key:'k',below:x('size'),body:bit(body(x('k')))}),read=(name:string)=>get(name,n(0))
 const original:Machine={name:'exact dispatch frame',params:['size'],inputs:['row','left','right'],state:{},maps:{Rows:0,Epoch:0,Written:0,Version:0},inputMaps:['Proposal'],
  counts:{rowCount:cnt(k=>cell(x('row'),k)),members:cnt(member),diff:cnt(k=>all(cell(x('row'),k),not(member(k)))),reverse:cnt(k=>all(member(k),not(cell(x('row'),k)))),meet:cnt(k=>all(cell(x('row'),k),member(k)))},
  assume:all(less(x('row'),x('size')),less(read('rowCount'),times(2,read('members'))),atMost(times(2,x('left')),read('rowCount')),less(read('rowCount'),plus(times(2,x('left')),n(2))),atMost(times(2,x('right')),read('members')),less(read('members'),plus(times(2,x('right')),n(2)))),
  step:{flags:{eligible:{op:'all',key:'voter',c:any(not(member(x('voter'))),all(less(get('Epoch',x('voter')),plus(get('Epoch',x('row')),n(1))),atMost(get('Version',x('voter')),get('Version',x('row')))))},elect:{op:'flag',name:'eligible'},change:less(read('meet'),plus(minus(plus(x('left'),n(1)),read('diff')),minus(plus(x('right'),n(1)),read('reverse'))))},maps:{Written:{each:'z',value:ite(all({op:'flag',name:'elect'},same(x('z'),x('row'))),plus(get('Epoch',x('row')),n(1)),get('Written',x('z')))},Rows:{each:'z',value:ite(all({op:'flag',name:'change'},atMost(times(8,x('row')),x('z')),less(x('z'),plus(times(8,x('row')),n(8)))),bit(member(minus(x('z'),times(8,x('row'))))),get('Rows',x('z')))}}}}
 const g=quorumLaws(original,true),m={...original,counts:{...original.counts,...g.counts}},law=g.laws.find(l=>quorumLawProvenance(l)?.disabled)!
 m.pre=all(atMost(n(1),x('size')),atMost(x('size'),n(8)));m.inputs.push('operation');m.assume=all(m.assume!,any(...[11,12,13].map(value=>same(x('operation'),n(value)))));m.step={...m.step,maps:{}}
 return {m,family:g.laws,law}
}
function flags<T>(run:()=>T):T{
 const names=['GDP_COUNT_STRATEGIES','GDP_COUNT_LIFTED','GDP_COUNT_LIFTED_PREREQUISITES','GDP_COUNT_C2_REPLAY','GDP_COUNT_FINAL_DEFER_CHECKS'] as const,old=names.map(name=>env[name])
 for(const name of names)env[name]=name==='GDP_COUNT_LIFTED_PREREQUISITES'||name==='GDP_COUNT_FINAL_DEFER_CHECKS'?'0':'1'
 try{return run()}finally{names.forEach((name,i)=>{if(old[i]===undefined)delete env[name];else env[name]=old[i]})}
}
const full=completeWorkProfile.enabled?test:test.skip
full('exact production dispatch retains the supplied case and leaf plan despite an expired legacy deadline',()=>flags(()=>{
 const original=workAmount(1_000_000_000n)
 workLedger.withBudget(original,()=>{
  const {m,family,law}=fixture(),slices:LiftedWorkSlice[]=[],plan=liftedWorkLeaseBudget(original,{observe:s=>slices.push(s)})
  const proof=proveCountStrategies(m,family,law,0,(goal,decls)=>certFor(goal,decls,false,0,()=>true),undefined,0,family,plan)
  expect(proof).toBeDefined();if(!proof)return
  expect(slices.filter(s=>s.kind==='case').map(s=>s.key)).toEqual(['op:11','op:12','op:13'])
  expect(slices.some(s=>s.kind==='leaf')).toBe(true)
  for(const slice of slices)expect(compareWork(slice.allocation,workShare(original,1n,slice.kind==='case'?30n:120n))).toBe(0)
  for(const packet of countedObligations(m,family,{[law.name]:proof.instances},family.indexOf(law)))expect(checkMC(packet.goal.hyps,packet.decls,proof.certs[packet.goal.name]!)).toBe(true)
 })
}))
full('counted attempt exact seam forwards the original plan without reconstructing a numeric allowance',()=>flags(()=>{
 const original=workAmount(1_000_000_000n)
 workLedger.withBudget(original,()=>{
  const {m,family,law}=fixture(),slices:LiftedWorkSlice[]=[],plan=liftedWorkLeaseBudget(original,{observe:s=>slices.push(s)})
  const attempts=countedAttempts(m,[],new Set(),0,true,new Set([law]),0,undefined,family),proof=attempts.exactStrategy(law,family,plan)
  expect(proof).toBeDefined();expect(slices.filter(s=>s.kind==='case')).toHaveLength(3)
  if(proof)for(const packet of countedObligations(m,family,{[law.name]:proof.instances},family.indexOf(law)))expect(checkMC(packet.goal.hyps,packet.decls,proof.certs[packet.goal.name]!)).toBe(true)
 })
}))
full('explicit plans never silently fall back to a numeric or rootless invocation',()=>flags(()=>{
 const {m,family,law}=fixture(),request:Parameters<typeof proveCountStrategies>[4]=(goal,decls)=>certFor(goal,decls,false,0,()=>true)
 const plan=liftedWorkLeaseBudget(workAmount(1_000_000n))
 expect(()=>proveCountStrategies(m,family,law,0,request,undefined,0,family,plan)).toThrow('live FULL lease plan')
 workLedger.withBudget(workAmount(1_000_000n),()=>{
  expect(()=>proveCountStrategies(m,family,law,0,request)).toThrow(BudgetExpired)
  expect(()=>proposeCountStrategiesForClosing(m,family,law,0,request,undefined,0,family,{...plan,lease:undefined} as LiftedWorkBudget)).toThrow('live FULL lease plan')
 })
}))
