// Untrusted search preference only. The original goal and its clauses are unchanged.
import {type CountCert} from '../../kernel/kernel.ts'
type Packet=Pick<CountCert,'reads'|'insts'>
const signature=(below:unknown,terms:Packet['insts'][number]['terms'])=>JSON.stringify([below,[...terms].sort((a,b)=>a[1].localeCompare(b[1])||a[0]-b[0])])
function compensatedMatches(cert:Packet):{index:number,key:string}[]{
 const reads=new Map(cert.reads.map(r=>[r[0],r])),matches:{index:number,key:string}[]=[]
 cert.insts.forEach((q,index)=>{
  if(q.unit!==0||q.terms.length!==3)return
  const positive=q.terms.filter(([z])=>z===1),negative=q.terms.filter(([z])=>z===-1)
  if(positive.length!==1||negative.length!==2)return
  const post=reads.get(positive[0]![1]);if(!post?.[1].endsWith('#'))return
  for(let i=0;i<negative.length;i++){
   const old=reads.get(negative[i]![1]),request=negative[1-i]!
   if(old?.[1]!==post[1].slice(0,-1)||JSON.stringify(old[2])!==JSON.stringify(post[2]))continue
   const input=reads.get(request[1]);if(!input||input[1].endsWith('#'))continue
   matches.push({index,key:signature(q.below,[positive[0]!,request])})
  }
 })
 return matches
}
export function compensatedTransportIndices(cert:Packet):Set<number>{
 return new Set(compensatedMatches(cert).map(m=>m.index))
}
export function shadowedTransportIndices(cert:Packet):Set<number>{
 const shadowed=new Set(compensatedMatches(cert).map(m=>m.key))
 return new Set(cert.insts.flatMap((q,i)=>q.unit===0&&q.terms.length===2&&shadowed.has(signature(q.below,q.terms))?[i]:[]))
}
