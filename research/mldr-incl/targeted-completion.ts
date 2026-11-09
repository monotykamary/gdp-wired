// Disposable ordering experiment. Returns existing universal instances only.
import {type E,type Law,type Machine,walkOnce} from '../../core/machine.ts'
import {type CountCert,type CountDecl,type Instances,assumed} from '../../kernel/kernel.ts'
import {completeCountLawInstances} from '../../core/count-completion.ts'
import {memberInclusions} from '../../core/count-recovery/member-inclusions.ts'
export function targetedCompletion(m:Machine,laws:Law[],at:Instances,terms:E[],decls:CountDecl[],packet:Pick<CountCert,'reads'>,more:()=>boolean){
 const offered=completeCountLawInstances(laws,at,terms,l=>{let yes=false;walkOnce(l.holds,(o:any)=>{if(o.op==='get'&&m.counts?.[o.map])yes=true});return yes},more)
 const proposed:{law:string,tuple:E[],score:number}[]=[]
 for(const add of offered.added){
  if(!more())break
  const law=laws.find(l=>l.name===add.law)!;const reads:CountCert['reads']=packet.reads.map(r=>[...r]),known=new Set(reads.map(r=>JSON.stringify(r.slice(1))))
  walkOnce(assumed([law],{[law.name]:add.tuple}),(o:any)=>{if(o.op==='get'&&decls.some(d=>d.map===o.map)){const id=JSON.stringify([o.map,o.key]);if(!known.has(id)){known.add(id);reads.push(['proposal$'+reads.length,o.map,o.key])}}})
  const newIds=new Set(reads.slice(packet.reads.length).map(r=>r[0]));let score=0
  for(const hint of memberInclusions(m,decls,reads,more))if(newIds.has(hint.negative)){
   const read=reads.find(r=>r[0]===hint.negative)!,d=decls.find(d=>d.map===read[1])!;let size=0;walkOnce(d.body,(o:any)=>{if(o.op)size++});score=Math.max(score,size)
  }
  if(score)proposed.push({...add,score})
 }
 const best=Math.max(0,...proposed.map(p=>p.score)),chosen=proposed.filter(p=>p.score===best).slice(0,8);let next=at
 for(const add of chosen){if(next===at)next={...at};next[add.law]=[...next[add.law]??[],...add.tuple]}
 return {at:next,added:chosen}
}
