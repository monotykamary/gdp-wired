// First F5 emitter: discover and check frame operations from the original
// machine. Other operation kinds decline; no saved proof or supplied transport
// can fill a missing case. The shared composer runs only for an exhaustive set.
import {traceNow} from './trace-clock.ts'
import {type LiftedWorkBudget,liftedLeaseOptions,liftedWorkBudget,withLiftedCase,withLiftedLeaf} from './count-lifted-budget.ts'
import {type Law, type Machine, all, n, same, x} from './machine.ts'
import {countsForReads} from './count-facts.ts'
import {startWork} from './work-admission.ts'
import {workMap} from './work-collections.ts'
import {countFrameConditions, fixedCountFrameCase, ownCountLawInstance, proveCountFrameGoal} from './count-frames.ts'
import {type CountStrategyProof, type CountRequestBuilder, type CountStrategyOptions} from './count-strategy.ts'
import {composeCountOperationProofs, type FixedOperationProof} from './count-case-compose.ts'
import {discoverLiftedCountGuard, discoverLiftedCountOperations} from './count-lifted-shape.ts'
import {type CountCert, type Instances, checkMC, countedObligations, frameOk, linear, mcGoal} from '../kernel/kernel.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {add,k,env,type Lin} from './solver.ts'
import {clock, fullRate, fullWork, late, withDeadline} from '../kernel/prove.ts'
import {proveLiftedCountLoad} from './count-lifted-load.ts'
import {proveLiftedCountCopy} from './count-lifted-copy.ts'
import {proveLiftedCountIncrement} from './count-lifted-increment.ts'
import {proveLiftedCountReplacement} from './count-lifted-replacement.ts'
import {recordCountStrategyPremises} from './count-strategy-premises.ts'
import {observeCountOperation} from './count-operation-observation.ts'
// A checked fixed-operation STEP fragment, not a standalone INIT/STEP proof.
export function proveLiftedCountFrame(m: Machine, family: Law[], law: Law, until: number, requestFor: CountRequestBuilder, observe?: (event: Record<string, unknown>) => void, options: CountStrategyOptions = {}): CountStrategyProof | undefined {
 return withDeadline(until, () => {
  const shape = discoverLiftedCountGuard(m, law, family, observe), choice = fixedCountFrameCase(m)
  if (!shape || !choice || !family.includes(law) || late(until)) {observe?.({stage: 'frame-decline', reason: !shape ? 'shape' : !choice ? 'operation' : 'scope-or-time'}); return}
  const instances = ownCountLawInstance(law, {}), step = countedObligations(m, family, {[law.name]: instances}, family.indexOf(law)).at(-1)!
  const request = requestFor(step.goal, step.decls), counts = countsForReads(step.decls, request.reads), targets = new Set(shape.countMaps), when = countFrameConditions(choice)
  if (!counts) {observe?.({stage: 'frame-decline', reason: 'counts'}); return}
  const post = request.reads.filter(read => read[1].endsWith('#') && targets.has(read[1].slice(0, -1)))
  // An unchanged post formula can reuse the pre count directly, leaving no
  // post-labelled read at all. Refute that actual goal; do not invent a frame.
  if (!post.length) {
   const goal = mcGoal(step.goal.hyps, step.decls, request), result = goal && withLiftedLeaf(until,options,Infinity,'leaf:frame:direct',end=>growCdcl(goal,new Map(),{nodes:0,until:end}))
   if (!result || !('tree' in result)) {observe?.({stage: 'frame-decline', reason: 'direct-search', outcome: result && 'stuck' in result ? result.stuck : 'encoding'}); return}
   const cert = {...request, tree: result.tree}
   return checkMC(step.goal.hyps, step.decls, cert) && !late(until) ? {instances, certs: {[step.goal.name]: cert}} : undefined
  }
  const extraWhen:Lin[]=[]
  for (const [,map,key] of post) {
   const declaration=step.decls.find(decl=>decl.map===map)
   if (!declaration?.base) continue
   if (key.op!=='add' || key.a.op!=='mul' || key.a.k!==declaration.base) return
   const low=linear(key.b,new Map()); if(!low) return
   extraWhen.push(add(low,k(1-declaration.base)))
  }
  const framedWhen=[...when,...extraWhen]
  const missing = post.filter(([name, map, key]) => {
   const pre = request.reads.find(read => read[1] === map.slice(0, -1) && JSON.stringify(read[2]) === JSON.stringify(key))
   return !pre || !frameOk(counts, {post: name, pre: pre[0], when:framedWhen})
  })
  if (missing.length) {observe?.({stage: 'frame-decline', reason: 'unframed-count', reads: missing.map(read => read[1])}); return}
  const run=(end:number)=>proveCountFrameGoal(step.goal,step.decls,request,choice,targets,end,undefined,{extraWhen,leafUnits:options.leafUnits})
  const cert=options.leafWork?withLiftedLeaf(until,options,100,'leaf:frame:framed',run):run(until)
  observe?.({stage: 'frame-search', checked: !!cert})
  return cert ? {instances, certs: {[step.goal.name]: cert}} : undefined
 })
}
// INIT is built from the actual lifted target, not the vote-map assumption of
// the older two-count strategy. Every zero proposal is an ordinary CountInst.
export function proveLiftedCountInitial(m: Machine, family: Law[], law: Law, instances: Instances, until: number, requestFor: CountRequestBuilder): CountCert | undefined {
 if (late(until)) return
 const initial = countedObligations(m, family, {[law.name]: instances}, family.indexOf(law))[0]
 if (!initial) return
 const base = requestFor(initial.goal, initial.decls), counts = countsForReads(initial.decls, base.reads)
 if (!counts) return
 const scope = JSON.stringify([m, family, instances, base]); let prefix = 'liftedInitial$'
 while (scope.includes(prefix)) prefix = '$' + prefix
 const request = {...base, insts: counts.map((count, index) => ({wit: prefix + index, below: count.below, terms: [[1, count.v] as [number, string]], unit: 0})), picks: []}
 const goal = mcGoal(initial.goal.hyps, initial.decls, request), result = goal && growCdcl(goal, new Map(), {nodes: 0, until})
 if (!result || !('tree' in result)) return
 const cert = {...request, tree: result.tree}
 return checkMC(initial.goal.hyps, initial.decls, cert) && !late(until) ? cert : undefined
}
export function proveLiftedCountComposition(m: Machine, family: Law[], law: Law, until: number, requestFor: CountRequestBuilder, observe?: (event: Record<string, unknown>) => void, workAllowance: number | LiftedWorkBudget = Math.max(0,until-clock())): CountStrategyProof | undefined {
 const budget=typeof workAllowance==='number'?liftedWorkBudget(workAllowance):workAllowance
 if(budget.lease?.owners)return proveOwnerFundedLiftedComposition(m,family,law,requestFor,observe,budget)
 if(budget.lease)until=Infinity
 return withDeadline(until, () => {
  if(!family.includes(law))return
  const shape = discoverLiftedCountGuard(m, law, family, observe), plan = shape && discoverLiftedCountOperations(m, shape)
  if (!shape || !plan || late(until)) return
  const cases: FixedOperationProof[] = []
  const rank:Record<string,number>={'frame-or-phase':0,load:1,copy:2,'threshold-increment':3,'threshold-replace':4,replacement:4}
  for (const operation of [...plan].sort((a,b)=>rank[a.kind]!-rank[b.kind]!||a.value-b.value)) {
   if (late(until)) return
   if(operation.kind==='replacement'||operation.kind==='threshold-replace'&&env.GDP_COUNT_LIFTED_REPLACEMENT!=='1'){observe?.({stage:'lifted-operation',value:operation.value,kind:operation.kind,proposed:false,reason:'replacement emitter unavailable'});return}
   const fixed = {...m, assume: all(...(m.assume ? [m.assume] : []), same(x(operation.name), n(operation.value)))}, emit = operation.kind==='load'?proveLiftedCountLoad:operation.kind==='copy'?proveLiftedCountCopy:operation.kind==='threshold-replace'?proveLiftedCountReplacement:proveLiftedCountIncrement
   const before=fullWork(),wall=observe?traceNow():0,key='op:'+operation.value,report=observe?(event:Record<string,unknown>)=>observe({value:operation.value,...event}):undefined
   const owned=env.GDP_COUNT_C2_REPLAY==='1',caseOptions=liftedLeaseOptions(budget,key)
   const proof=observeCountOperation({owner:law.name,value:operation.value,kind:operation.kind},()=>withLiftedCase(until,budget,operation.kind==='frame-or-phase',key,end=>operation.kind==='frame-or-phase'?proveLiftedCountFrame(fixed,family,law,end,requestFor,report,caseOptions):emit(fixed,family,law,end,requestFor,report,{...caseOptions,deferToComposition:env.GDP_COUNT_LIFTED_REPLACEMENT==='1',deferIntermediateChecks:env.GDP_COUNT_DEFER_CHECKS==='1',deferOwnedReplacementLemmas:owned,batchOwnedReplacementPruning:owned,deferOwnedReplacementReplay:owned,slicedLemmas:env.GDP_COUNT_C2_LEMMAS==='1',emitterFramePool:env.GDP_COUNT_EMITTER_FRAME_POOL==='1'})))
   observe?.({stage: 'lifted-operation', value: operation.value, kind: operation.kind, proposed: !!proof, units: (fullWork()-before)/fullRate, wallMs: traceNow()-wall})
   if (!proof) return
   cases.push({value: operation.value, proof})
  }
  if (cases.length !== plan.length) return
  const initialBefore=fullWork(),initialWall=observe?traceNow():0,initial = proveLiftedCountInitial(m, family, law, cases[0]!.proof.instances, until, requestFor)
  observe?.({stage: 'lifted-initial', checked: !!initial, units: (fullWork()-initialBefore)/fullRate, wallMs: traceNow()-initialWall})
  if (!initial) return
  const compositionBefore=fullWork(),compositionWall=observe?traceNow():0,result=composeCountOperationProofs({original: m, machine: m, shape: shape.countShape, restrictions: [], inputCounts: {}}, family, law, cases, until, requestFor, observe?(stage, value) => observe({stage, value}):undefined, {initial,...(budget.lease?{propagateBudgetExpiry:true}:{}),...(env.GDP_COUNT_C2_LEMMAS==='1'?{slicedLemmas:true}:{})})
  observe?.({stage:'lifted-composition',checked:!!result,units:(fullWork()-compositionBefore)/fullRate,wallMs:traceNow()-compositionWall})
  return result&&recordCountStrategyPremises(family,result)
 })
}
// Explicit next-pin route only. Each non-case segment consumes the SAME
// cumulative body budget; case and leaf helpers run outside those segments.
// The ordinary lease path above is left unchanged until policy activation.
function proveOwnerFundedLiftedComposition(m:Machine,family:Law[],law:Law,requestFor:CountRequestBuilder,
 observe:((event:Record<string,unknown>)=>void)|undefined,budget:LiftedWorkBudget):CountStrategyProof|undefined{
 const owners=budget.lease!.owners!,until=Infinity
 const prepared=owners.body(()=>{
  let present=false
  for(const candidate of family){startWork('ticks',1,'owned lifted owner lookup');if(candidate===law){present=true;break}}
  if(!present)return
  const shape=discoverLiftedCountGuard(m,law,family,observe),plan=shape&&discoverLiftedCountOperations(m,shape)
  if(!shape||!plan||late(until))return
  const rank:Record<string,number>={'frame-or-phase':0,load:1,copy:2,'threshold-increment':3,'threshold-replace':4,replacement:4}
  const ordered=workMap(plan,operation=>operation,'owned lifted operation copy')
  // Stable insertion sorting is fully charged, unlike a native sort's opaque
  // pre-comparator copies. This preserves the existing kind/value ordering.
  for(let i=1;i<ordered.length;i++){
   startWork('ticks',1,'owned lifted operation sort');const item=ordered[i]!;let j=i
   while(j>0){
    startWork('ticks',1,'owned lifted operation compare');const previous=ordered[j-1]!
    if(rank[previous.kind]!<rank[item.kind]!||rank[previous.kind]===rank[item.kind]&&previous.value<=item.value)break
    startWork('ticks',1,'owned lifted operation move');ordered[j]=previous;j--
   }
   startWork('ticks',1,'owned lifted operation insert');ordered[j]=item
  }
  return {shape,ordered,cases:[] as FixedOperationProof[]}
 })
 if(!prepared)return
 for(const operation of prepared.ordered){
  const setup=owners.body(()=>{
   startWork('ticks',1,'owned lifted case setup')
   if(late(until))return
   if(operation.kind==='replacement'||operation.kind==='threshold-replace'&&env.GDP_COUNT_LIFTED_REPLACEMENT!=='1'){
    observe?.({stage:'lifted-operation',value:operation.value,kind:operation.kind,proposed:false,reason:'replacement emitter unavailable'});return
   }
   const fixed={...m,assume:all(...(m.assume?[m.assume]:[]),same(x(operation.name),n(operation.value)))}
   const emit=operation.kind==='load'?proveLiftedCountLoad:operation.kind==='copy'?proveLiftedCountCopy:operation.kind==='threshold-replace'?proveLiftedCountReplacement:proveLiftedCountIncrement
   const key='op:'+operation.value,report=observe?(event:Record<string,unknown>)=>observe({value:operation.value,...event}):undefined
   return {fixed,emit,key,report,before:fullWork(),wall:observe?traceNow():0,owned:env.GDP_COUNT_C2_REPLAY==='1',options:liftedLeaseOptions(budget,key)}
  })
  if(!setup)return
  const proof=withLiftedCase(until,budget,operation.kind==='frame-or-phase',setup.key,end=>
   observeCountOperation({owner:law.name,value:operation.value,kind:operation.kind},()=>operation.kind==='frame-or-phase'
    ?proveLiftedCountFrame(setup.fixed,family,law,end,requestFor,setup.report,setup.options)
    :setup.emit(setup.fixed,family,law,end,requestFor,setup.report,{...setup.options,deferToComposition:env.GDP_COUNT_LIFTED_REPLACEMENT==='1',deferIntermediateChecks:env.GDP_COUNT_DEFER_CHECKS==='1',deferOwnedReplacementLemmas:setup.owned,batchOwnedReplacementPruning:setup.owned,deferOwnedReplacementReplay:setup.owned,slicedLemmas:env.GDP_COUNT_C2_LEMMAS==='1',emitterFramePool:env.GDP_COUNT_EMITTER_FRAME_POOL==='1'})))
  const retained=owners.body(()=>{
   startWork('ticks',1,'owned lifted case result')
   observe?.({stage:'lifted-operation',value:operation.value,kind:operation.kind,proposed:!!proof,units:(fullWork()-setup.before)/fullRate,wallMs:traceNow()-setup.wall})
   if(!proof)return false
   prepared.cases.push({value:operation.value,proof});return true
  })
  if(!retained)return
 }
 return owners.body(()=>{
  startWork('ticks',1,'owned lifted final phases')
  if(prepared.cases.length!==prepared.ordered.length||!prepared.cases.length)return
  const initialBefore=fullWork(),initialWall=observe?traceNow():0
  const initial=proveLiftedCountInitial(m,family,law,prepared.cases[0]!.proof.instances,until,requestFor)
  observe?.({stage:'lifted-initial',checked:!!initial,units:(fullWork()-initialBefore)/fullRate,wallMs:traceNow()-initialWall})
  if(!initial)return
  const compositionBefore=fullWork(),compositionWall=observe?traceNow():0
  const result=composeCountOperationProofs({original:m,machine:m,shape:prepared.shape.countShape,restrictions:[],inputCounts:{}},family,law,prepared.cases,until,requestFor,
   observe?(stage,value)=>observe({stage,value}):undefined,{initial,propagateBudgetExpiry:true,...(env.GDP_COUNT_C2_LEMMAS==='1'?{slicedLemmas:true}:{})})
  observe?.({stage:'lifted-composition',checked:!!result,units:(fullWork()-compositionBefore)/fullRate,wallMs:traceNow()-compositionWall})
  return result&&recordCountStrategyPremises(family,result)
 })
}
