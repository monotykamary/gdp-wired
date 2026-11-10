// Untrusted exact reindexing after removing path assumptions. This never
// searches and never certifies a result; the caller must check the final tree.
import {type Goal,type Path,type Tree,canon} from '../../kernel/kernel.ts'
import {type Step} from '../solver.ts'
import {late} from '../../kernel/prove.ts'
import {rowsAt,wallTree} from './ops.ts'
export function rebasePath(g:Goal,tree:Tree,from:Path,to:Path,until:number,target:Goal=g):Tree|undefined{
 return wallTree(target===g?'pin-pruning':'source-reindexing',()=>{
  const indices=new WeakMap<object,Map<string,number>>()
  const visit=(t:Tree,a:Path,b:Path):Tree|undefined=>{
   if(late(until))return undefined
   if(!('leaf'in t)){
    const id=canon(t.split),known=b.get(id)?.holds
    if(known!==undefined)return visit(known?t.yes:t.no,new Map(a).set(id,{lin:t.split,holds:known}),b)
    const yes=visit(t.yes,new Map(a).set(id,{lin:t.split,holds:true}),new Map(b).set(id,{lin:t.split,holds:true}))
    const no=yes&&visit(t.no,new Map(a).set(id,{lin:t.split,holds:false}),new Map(b).set(id,{lin:t.split,holds:false}))
    return yes&&no?{split:t.split,yes,no}:undefined
   }
   const before=rowsAt(g,a),after=rowsAt(target,b)
   let at=indices.get(after)
   if(!at){at=new Map();after.forEach((r,i)=>{const id=canon(r.lin);if(!at!.has(id))at!.set(id,i)});indices.set(after,at)}
   const map=(i:number)=>i<before.length?at!.get(canon(before[i]!.lin)):i-before.length+after.length
   const leaf:Step[]=[]
   for(const step of t.leaf){
    if(step.kind!=='input'){leaf.push(step);continue}
    const index=map(step.index);if(index===undefined)return undefined
    leaf.push({...step,index})
   }
   const products:[number,number][]=[]
   for(const [a,b]of t.products??[]){const x=map(a),y=map(b);if(x===undefined||y===undefined)return undefined;products.push([x,y])}
   return {leaf,...(t.products?{products}:{}),...(t.squares?{squares:t.squares}:{})}
  }
  return visit(tree,from,to)
 })
}

// Cuts are listed in the order they extended the path. Drop a cut only when
// its retained branch can be reindexed without that assumption. Rejected or
// timed-out proposals retain the original exhaustive split and its proof.
export function pruneForcedCuts(g:Goal,tree:Tree,root:Path,cuts:{split:Record<string,number>,no:Tree}[],until:number):{tree:Tree,removed:number}{
 const paths:Path[]=[new Map(root)];for(const cut of cuts)paths.push(new Map(paths.at(-1)!).set(canon(cut.split),{lin:cut.split,holds:true}))
 let out=tree,removed=0
 for(let i=cuts.length-1;i>=0;i--){
  const cut=cuts[i]!,shorter=rebasePath(g,out,paths[i+1]!,paths[i]!,until)
  if(shorter){out=shorter;removed++}else out={split:cut.split,yes:out,no:cut.no}
 }
 return {tree:out,removed}
}
