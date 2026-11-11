// Untrusted, exact transport from case-local sliced lemmas to the joint goal.
// Only the known fixed-operation assumption may be discharged into scope.when.
// All other missing/ambiguous/merged hypotheses decline. Native checkMC remains
// the authority over both the remapped lemma proof and the complete main tree.
import {type C} from './machine.ts'
import {type Lin} from './solver.ts'
import {type Goal,type LemmaCut,type Path,canon} from '../kernel/kernel.ts'
import {late} from '../kernel/prove.ts'
import {rebasePath} from './count-rebase-path.ts'
export function transportCountLemmas(source:Goal,target:Goal,lemmas:LemmaCut[],scope:{assumed:C,retained?:C,when:Lin[]},until:number):LemmaCut[]|undefined{
 const key=(v:unknown)=>JSON.stringify(v),at=new Map<string,number[]>()
 target.hyps.forEach((hyp,i)=>{const k=key(hyp);at.set(k,[...(at.get(k)??[]),i])})
 const root=(cut:Lin,when:Lin[]):Path=>{const out:Path=new Map();let n=0;for(const atom of[{lin:cut,holds:false},...when.map(lin=>({lin,holds:true}))]){const id=canon(atom.lin);out.set(out.has(id)?'@'+n++:id,atom)}return out}
 const out:LemmaCut[]=[]
 for(const lemma of lemmas){
  if(late(until))return
  const original=lemma.slice??source.hyps.map((_,i)=>i),slice:number[]=[],used=new Set<number>()
  for(const i of original){
   if(!Number.isSafeInteger(i)||i<0||i>=source.hyps.length)return
   const hyp=source.hyps[i]!,found=at.get(key(hyp))
   if(found?.length===1){if(used.has(found[0]!))return;used.add(found[0]!);slice.push(found[0]!);continue}
   if(found?.length||key(hyp)!==key(scope.assumed)){console.log('LEMMA_TRANSPORT_DECLINE '+JSON.stringify({stage:'hyp-map',index:i,matches:found?.length??0,hyp:key(hyp).slice(0,4000),assumed:key(scope.assumed).slice(0,4000)}));return}
   if(scope.retained){const retained=at.get(key(scope.retained));if(retained?.length!==1||used.has(retained[0]!))return;used.add(retained[0]!);slice.push(retained[0]!)}
  }
  const when=[...scope.when,...lemma.when],tree=rebasePath({...source,hyps:original.map(i=>source.hyps[i]!)},lemma.tree,root(lemma.cut,lemma.when),root(lemma.cut,when),until,{...target,hyps:slice.map(i=>target.hyps[i]!)})
  if(!tree){console.log('LEMMA_TRANSPORT_DECLINE '+JSON.stringify({stage:'tree-reindex',original,slice,when:when.length}));return}
  out.push({...lemma,when,slice,tree})
 }
 return out
}
