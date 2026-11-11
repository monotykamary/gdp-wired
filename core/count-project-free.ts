// Untrusted query projection. Only split conjunctions and prune disjuncts the
// existing path decides false. Callers must rebase and check the full goal.
import {type C,walkOnce} from './machine.ts'
import {type Path,truth} from '../kernel/kernel.ts'
export function projectCountFree(hyps:C[],path:Path,countMaps:ReadonlySet<string>,otherWitnesses:ReadonlySet<string>=new Set(),cofactor=false):C[]{
 const atPath=(c:C):C[]=>{
  if(cofactor&&truth(c,path)===true)return []
  if(c.op==='and')return c.xs.flatMap(atPath)
  if(c.op==='or'){
   if(c.xs.some(x=>truth(x,path)===true))return []
   const live=c.xs.filter(x=>truth(x,path)!==false)
   if(live.length===1)return atPath(live[0]!)
  }
  let keep=true;walkOnce(c,(node:any)=>{if(node.op==='get'&&countMaps.has(node.map)||node.op==='var'&&otherWitnesses.has(node.name))keep=false})
  return keep?[c]:[]
 }
 return hyps.flatMap(atPath)
}
