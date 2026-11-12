import {searchNow as countedSearchNow,WallExpired} from './wall.ts'
// Untrusted integration helpers for complete counted certificates. The kernel
// still checks the emitted ordinary tree and independent conditional cuts.
import {type CountCert,type Goal,type Path,canon,lemmaPath} from '../kernel/kernel.ts'
import {BudgetExpired,usedHyps,widen} from '../kernel/prove.ts'
import {collectConditionalCertificate,markConditionalProof,transportConditionalProof,type ConditionalTransportOptions} from './count-recovery/conditional-proof.ts'
import {workLedger} from './work-admission.ts'

export function transportCountCertificate(from:Goal,to:Goal,cert:CountCert,until:number):CountCert|undefined{
 if(countedSearchNow()>=until)return undefined
 if(!cert.lemmas?.length){const tree=widen(from,to,cert.tree);return tree&&countedSearchNow()<until?{...cert,tree}:undefined}
 const marked=markConditionalProof(from,cert.tree,cert.lemmas),tree=transportConditionalProof(from,to,marked,new Map(),new Map(),until)
 const combined=tree&&collectConditionalCertificate(to,tree,until)
 return combined?{...cert,...combined}:undefined
}

// Across-round retention must never repair a missing premise by searching.
// The exact conditional transporter also handles ordinary trees with no cuts.
export function replayCountCertificate(from:Goal,to:Goal,cert:CountCert,until:number,options?:ConditionalTransportOptions):CountCert|undefined{
 const replay=()=>{
  if(countedSearchNow()>=until)return undefined
  const marked=markConditionalProof(from,cert.tree,cert.lemmas??[])
  const tree=transportConditionalProof(from,to,marked,new Map(),new Map(),until,options)
  const combined=tree&&collectConditionalCertificate(to,tree,until,options)
  return combined?{...cert,...combined}:undefined
 }
 // The original error and its ledger-authenticated endpoint provenance survive
 // nested pre-check/kernel catches; legacy callers retain their old boundary.
 return options?.rethrowBudgetExpired?workLedger.withCapacityRefusalBoundary(replay):replay()
}

export function countedCertificateHyps(goal:Goal,cert:CountCert):Set<number>|undefined{
 if(!cert.lemmas?.length)return usedHyps(goal,cert.tree)
 try{
  const found=new Set<number>(),seen=new WeakSet<object>()
  const visit=(tree:CountCert['tree'],path:Path):boolean=>{
   if(seen.has(tree))return false
   seen.add(tree)
   if('split'in tree){
    const id=canon(tree.split),yes=new Map(path).set(id,{lin:tree.split,holds:true}),no=new Map(path).set(id,{lin:tree.split,holds:false})
    const valid=visit(tree.yes,yes)&&visit(tree.no,no);seen.delete(tree);return valid
   }
   for(const i of usedHyps(goal,tree,lemmaPath(cert.lemmas!,path)))found.add(i)
   seen.delete(tree);return true
  }
  if(!visit(cert.tree,new Map()))return undefined
  // Every listed cut is checked, even when the main tree does not cite it.
  // Its explicit source slice must survive dependency pruning as a whole.
  for(const lemma of cert.lemmas){
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
