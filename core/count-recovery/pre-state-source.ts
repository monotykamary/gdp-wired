// A weaker pre-state source for a field ceiling. Preserve original terms and
// CInst order, remove post-dependent assumptions and instances at discarded
// witnesses. The caller must transport and check the tree in its full goal.
import {type C} from '../machine.ts'
import {type CountCert,type Goal,type Path} from '../../kernel/kernel.ts'
import {piecesAt,walkLive} from './live-dependencies.ts'
type Proposal=Pick<CountCert,'reads'|'insts'>
export function preStateCountSource(goal:Goal,cert:Proposal,claim:C,path:Path,extra:C[]=[]):{goal:Goal,cert:Proposal}{
 const post=cert.reads.filter(r=>r[1].endsWith('#')),postIds=new Set(post.map(r=>r[0])),postMaps=new Set(post.map(r=>r[1]))
 const keep=cert.insts.map((q,index)=>({q,index})).filter(({q})=>q.terms.every(([,id])=>!postIds.has(id))),indices=new Set(keep.map(({index})=>index))
 const discarded=new Set(cert.insts.filter((_,i)=>!indices.has(i)).map(q=>q.wit)),offset=goal.hyps.length-cert.insts.length
 const weaken=(c:C):C|undefined=>{
  if(c.op==='and'){
   const xs=c.xs.flatMap(child=>{const kept=weaken(child);return kept?[kept]:[]})
   return xs.length?{...c,xs}:undefined
  }
  let invalid=false
  walkLive(c,path,(o:any)=>{if(o.op==='get'&&postMaps.has(o.map)||o.op==='var'&&(postIds.has(o.name)||discarded.has(o.name)))invalid=true})
  return invalid?undefined:c
 }
 const hyps=goal.hyps.slice(0,offset).flatMap(c=>piecesAt(c,path)).flatMap(c=>{const kept=weaken(c);return kept?[kept]:[]})
 return {goal:{...goal,hyps:[...hyps,...extra,claim,...keep.map(({index})=>goal.hyps[offset+index]!)]},cert:{reads:cert.reads.filter(r=>!postIds.has(r[0])),insts:keep.map(({q})=>q)}}
}
