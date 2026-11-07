// Extend an untrusted count-certificate proposal without renaming any read or
// witness already used by a proof tree. All new instances still go through mcGoal
// and checkMC; this only keeps proposal identities stable across model rounds.
import {walkOnce} from './machine.ts'
import {type CountCert} from '../kernel/kernel.ts'
type Proposal=Pick<CountCert,'reads'|'insts'>
export function appendCountCert(current:Proposal,next:Proposal,context:unknown):boolean {
  const used=new Set([...current.reads.map(r=>r[0]),...current.insts.map(i=>i.wit)])
  walkOnce([context,current,next],(o:any)=>{if(o.op==='var')used.add(o.name)})
  let serial=0
  const fresh=(prefix:string):string=>{let name:string;do{name=`${prefix}$${serial++}`}while(used.has(name));used.add(name);return name}
  const key=(r:Proposal['reads'][number])=>JSON.stringify(r.slice(1))
  const byKey=new Map(current.reads.map(r=>[key(r),r[0]])),renamed=new Map<string,string>()
  let changed=false
  for(const read of next.reads){
    let name=byKey.get(key(read))
    if(name===undefined){name=fresh('countRead');current.reads.push([name,read[1],read[2]]);byKey.set(key(read),name);changed=true}
    renamed.set(read[0],name)
  }
  const signature=(i:Proposal['insts'][number])=>JSON.stringify([i.unit,i.below,[...i.terms].sort((a,b)=>a[1].localeCompare(b[1])||a[0]-b[0])])
  const have=new Set(current.insts.map(signature))
  for(const instance of next.insts){
    const terms=instance.terms.map(([k,id])=>[k,renamed.get(id)??id] as [number,string]),candidate={...instance,terms},sig=signature(candidate)
    if(have.has(sig))continue
    current.insts.push({...candidate,wit:fresh('countWitness')});have.add(sig);changed=true
  }
  return changed
}
