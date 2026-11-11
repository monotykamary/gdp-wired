// A proposer only: late-added guarded facts can change input-row indices.
// Reindex complete branch proofs against the final facts, then check them.
import {type FrameCut,type Goal,type LinCut,type Path,type Tree,canon,check,framePath} from '../kernel/kernel.ts'
import {late} from '../kernel/prove.ts'
import {rebasePath} from './count-rebase-path.ts'
export function stabilizeGuardedTree(goal:Goal,tree:Tree,frames:FrameCut[],lins:LinCut[],roots:ReadonlyMap<Tree,Path>,until:number,options:{deferCheck?:boolean}={}):{tree?:Tree,rebased:number,failed:boolean}{
 let rebased=0,failed=false
 const visit=(t:Tree,path:Path):Tree|undefined=>{
  if(late(until)){failed=true;return}
  const before=roots.get(t)
  if(before){
   const after=framePath(frames,[],path,[],lins)
   if(!options.deferCheck&&check(goal,t,after))return t
   const fixed=rebasePath(goal,t,before,after,until)
   if(fixed&&(options.deferCheck||check(goal,fixed,after))){rebased++;return fixed}
   failed=true;return
  }
  if('leaf'in t){failed=true;return}
  const id=canon(t.split),yes=visit(t.yes,new Map(path).set(id,{lin:t.split,holds:true}))
  const no=yes&&visit(t.no,new Map(path).set(id,{lin:t.split,holds:false}))
  return yes&&no?{split:t.split,yes,no}:undefined
 }
 return {tree:visit(tree,new Map()),rebased,failed}
}
