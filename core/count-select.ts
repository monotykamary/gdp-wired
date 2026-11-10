// Untrusted arithmetic-core selection; selected bounds are not accepted facts.
import {type C} from './machine.ts'
import {type Goal,type Path} from '../kernel/kernel.ts'
import {clock,usedHyps} from '../kernel/prove.ts'
import {modelSequence} from '../kernel/model-sequence.ts'
import {REFUTED} from '../kernel/cdcl.ts'

export type CountBoundCandidate={index:number,bound:C}
export type CountBoundSelection={indices:number[],assumed:number,fallback:boolean}
// The arithmetic oracle chooses proposals, never facts. In rank order, add
// candidate bounds until its refutation core names the ones worth deriving.
export function selectCountBounds(base:Goal,candidates:CountBoundCandidate[],until:number,options:{path?:Path,queryMs?:number,trace?:(event:Record<string,unknown>)=>void}={}):CountBoundSelection|undefined{
 const path=options.path??new Map(),ask=modelSequence(path),started=clock()
 for(let n=candidates.length?1:0;n<=candidates.length&&clock()<until;n++){
  const goal={...base,hyps:[...base.hyps,...candidates.slice(0,n).map(c=>c.bound)]},q=ask(goal,Math.min(until,clock()+(options.queryMs??200)))
  const used='tree'in q?usedHyps(goal,q.tree,path):q.why===REFUTED&&q.core?new Set(q.core):undefined
  if(used){
   const indices=candidates.slice(0,n).filter((_,i)=>used.has(base.hyps.length+i)).map(c=>c.index)
   options.trace?.({stage:'count-core-select',pool:candidates.length,assumed:n,indices,ms:Math.round(clock()-started)})
   return {indices,assumed:n,fallback:false}
  }
  if('tree'in q||q.stuck!=='sat')break
 }
 if(clock()>=until)return undefined
 const indices=candidates.map(c=>c.index)
 options.trace?.({stage:'count-core-select',pool:candidates.length,indices,fallback:true,ms:Math.round(clock()-started)})
 return {indices,assumed:indices.length,fallback:true}
}
