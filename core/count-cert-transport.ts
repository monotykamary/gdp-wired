import {searchNow as countedSearchNow,WallExpired} from './wall.ts'
// Untrusted integration helpers for complete counted certificates. The kernel
// still checks the emitted ordinary tree and independent conditional cuts.
import {type CountCert,type CountDecl,type Goal,type Path,canon,framePath,lemmaPath} from '../kernel/kernel.ts'
import {BudgetExpired,usedHyps,widen} from '../kernel/prove.ts'
import {collectConditionalCertificate,markConditionalProof,transportConditionalProof,type ConditionalTransportOptions,type ConditionalTransportDecline} from './count-recovery/conditional-proof.ts'
import {emitReplayDiagnostic,replayCertificateId,withReplayDiagnosticContext} from './count-replay-diagnostic.ts'
import {workLedger} from './work-admission.ts'
import {countsForReads} from './count-facts.ts'

export type CountTransportOptions=ConditionalTransportOptions&Readonly<{declarations?:{from:CountDecl[],to:CountDecl[]}}>

export function transportCountCertificate(from:Goal,to:Goal,cert:CountCert,until:number,options?:CountTransportOptions):CountCert|undefined{
 if(countedSearchNow()>=until)return undefined
 if(cert.frames?.length||cert.monos?.length||cert.lins?.length){
  // Derive counts only for cut-bearing certificates, from the caller's exact
  // source/target declarations and the original read header. No empty fallback.
  const declarations=options?.declarations
  const source=declarations&&countsForReads(declarations.from,cert.reads),target=declarations&&countsForReads(declarations.to,cert.reads)
  const native=declarations?(source&&target?{from:{counts:source},to:{counts:target}}:undefined):options?.native
  return replayCountCertificate(from,to,cert,until,{...options,native})
 }
 if(!cert.lemmas?.length){const tree=widen(from,to,cert.tree);return tree&&countedSearchNow()<until?{...cert,tree}:undefined}
 const marked=markConditionalProof(from,cert.tree,cert.lemmas),tree=transportConditionalProof(from,to,marked,new Map(),new Map(),until)
 const combined=tree&&collectConditionalCertificate(to,tree,until)
 return combined?{...cert,...combined}:undefined
}

// Across-round retention must never repair a missing premise by searching.
// The exact conditional transporter also handles ordinary trees with no cuts.
export function replayCountCertificate(from:Goal,to:Goal,cert:CountCert,until:number,options?:ConditionalTransportOptions):CountCert|undefined{
 let detail:ConditionalTransportDecline|undefined
 const notify=(value:ConditionalTransportDecline)=>{detail??=value;try{options?.onDecline?.(value)}catch{/* diagnostic callback only */}}
 const replay=()=>{
  if(countedSearchNow()>=until){notify({stage:"transport",part:"main",reason:"deadline"});return undefined}
  const cutBearing=!!(cert.frames?.length||cert.monos?.length||cert.lins?.length)
  if(cutBearing&&!options?.native){notify({stage:'cut-validation',part:'main',reason:'missing-native-count-context'});return undefined}
  // Cut arrays remain the original certificate's, not caller-supplied assumptions.
  const native=options?.native&&{from:{...options.native.from,frames:cert.frames,monos:cert.monos,lins:cert.lins},to:{...options.native.to,frames:cert.frames,monos:cert.monos,lins:cert.lins}}
  const context={...options,native,onDecline:notify}
  const marked=markConditionalProof(from,cert.tree,cert.lemmas??[])
  const tree=transportConditionalProof(from,to,marked,new Map(),new Map(),until,context)
  const combined=tree&&collectConditionalCertificate(to,tree,until,context)
  return combined?{...cert,...combined}:undefined
 }
 // The original error and its ledger-authenticated endpoint provenance survive
 // nested pre-check/kernel catches; legacy callers retain their old boundary.
 return withReplayDiagnosticContext(options?.diagnostic??{},()=>{
  const result=options?.rethrowBudgetExpired?workLedger.withCapacityRefusalBoundary(replay):replay()
  if(!result)emitReplayDiagnostic({kind:'certificate-decline',certificateId:replayCertificateId(cert),cutCounts:{frames:cert.frames?.length??0,lemmas:cert.lemmas?.length??0,monos:cert.monos?.length??0,lins:cert.lins?.length??0},prefix:{source:detail?.stage==='cut-validation'?'not-built':options?.native?'framePath':'lemmaPath',target:detail?.stage==='cut-validation'?'not-built':options?.native?'framePath':'lemmaPath'},detail:detail??{stage:'transport',part:'main',reason:'unclassified'},certificate:cert,sourceGoal:from,targetGoal:to,sourceCounts:options?.native?.from.counts,targetCounts:options?.native?.to.counts})
  return result
 })
}

export function countedCertificateHyps(goal:Goal,cert:CountCert):Set<number>|undefined{
 if(!cert.lemmas?.length&&!cert.frames?.length&&!cert.monos?.length&&!cert.lins?.length)return usedHyps(goal,cert.tree)
 try{
  const found=new Set<number>(),seen=new WeakSet<object>()
  const visit=(tree:CountCert['tree'],path:Path):boolean=>{
   if(seen.has(tree))return false
   seen.add(tree)
   if('split'in tree){
    const id=canon(tree.split),yes=new Map(path).set(id,{lin:tree.split,holds:true}),no=new Map(path).set(id,{lin:tree.split,holds:false})
    const valid=visit(tree.yes,yes)&&visit(tree.no,no);seen.delete(tree);return valid
   }
   for(const i of usedHyps(goal,tree,cert.frames?.length||cert.monos?.length||cert.lins?.length?framePath(cert.frames??[],cert.lemmas??[],path,cert.monos??[],cert.lins??[]):lemmaPath(cert.lemmas??[],path)))found.add(i)
   seen.delete(tree);return true
  }
  if(!visit(cert.tree,new Map()))return undefined
  // Every listed cut is checked, even when the main tree does not cite it.
  // Its explicit source slice must survive dependency pruning as a whole.
  for(const lemma of cert.lemmas??[]){
   if(lemma.slice===undefined){for(let i=0;i<goal.hyps.length;i++)found.add(i);continue}
   for(const i of lemma.slice){if(!Number.isSafeInteger(i)||i<0||i>=goal.hyps.length)return undefined;found.add(i)}
  }
  return found
 }catch(error){
  // Cancellation is not malformed metadata. Preserve the original error,
  // including the allocator's identity-bound capacity-refusal provenance.
  if(error instanceof BudgetExpired||error instanceof WallExpired)throw error
  return undefined
 }
}
