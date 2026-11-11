// First F5 emitter: discover and check frame operations from the original
// machine. Other operation kinds decline; no saved proof or supplied transport
// can fill a missing case. The shared composer runs only for an exhaustive set.
import {traceNow} from './trace-clock.ts'
import {type Law, type Machine, all, n, same, x} from './machine.ts'
import {countsForReads} from './count-facts.ts'
import {countFrameConditions, fixedCountFrameCase, ownCountLawInstance, proveCountFrameGoal} from './count-frames.ts'
import {type CountStrategyProof, type CountRequestBuilder} from './count-strategy.ts'
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
// A checked fixed-operation STEP fragment, not a standalone INIT/STEP proof.
export function proveLiftedCountFrame(m: Machine, family: Law[], law: Law, until: number, requestFor: CountRequestBuilder, observe?: (event: Record<string, unknown>) => void): CountStrategyProof | undefined {
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
   const goal = mcGoal(step.goal.hyps, step.decls, request), result = goal && growCdcl(goal, new Map(), {nodes: 0, until})
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
  const cert = proveCountFrameGoal(step.goal, step.decls, request, choice, targets, until, undefined, {extraWhen})
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
export function proveLiftedCountComposition(m: Machine, family: Law[], law: Law, until: number, requestFor: CountRequestBuilder, observe?: (event: Record<string, unknown>) => void): CountStrategyProof | undefined {
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
   const before=fullWork(),wall=observe?traceNow():0,end=Math.min(until,clock()+(operation.kind==='frame-or-phase'?500:2000)),report=observe?(event:Record<string,unknown>)=>observe({value:operation.value,...event}):undefined
   const proof=operation.kind==='frame-or-phase'?proveLiftedCountFrame(fixed,family,law,end,requestFor,report):emit(fixed,family,law,end,requestFor,report,{deferToComposition:env.GDP_COUNT_LIFTED_REPLACEMENT==='1',deferIntermediateChecks:env.GDP_COUNT_DEFER_CHECKS==='1',slicedLemmas:env.GDP_COUNT_C2_LEMMAS==='1',emitterFramePool:env.GDP_COUNT_EMITTER_FRAME_POOL==='1'})
   observe?.({stage: 'lifted-operation', value: operation.value, kind: operation.kind, proposed: !!proof, units: (fullWork()-before)/fullRate, wallMs: traceNow()-wall})
   if (!proof) return
   cases.push({value: operation.value, proof})
  }
  if (cases.length !== plan.length) return
  const initialBefore=fullWork(),initialWall=observe?traceNow():0,initial = proveLiftedCountInitial(m, family, law, cases[0]!.proof.instances, until, requestFor)
  observe?.({stage: 'lifted-initial', checked: !!initial, units: (fullWork()-initialBefore)/fullRate, wallMs: traceNow()-initialWall})
  if (!initial) return
  const compositionBefore=fullWork(),compositionWall=observe?traceNow():0,result=composeCountOperationProofs({original: m, machine: m, shape: shape.countShape, restrictions: [], inputCounts: {}}, family, law, cases, until, requestFor, observe?(stage, value) => observe({stage, value}):undefined, {initial,...(env.GDP_COUNT_C2_LEMMAS==='1'?{slicedLemmas:true}:{})})
  observe?.({stage:'lifted-composition',checked:!!result,units:(fullWork()-compositionBefore)/fullRate,wallMs:traceNow()-compositionWall})
  return result&&recordCountStrategyPremises(family,result)
 })
}
