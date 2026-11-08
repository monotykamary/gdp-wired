// Untrusted exact reindexing after removing path assumptions. This never
// searches and never certifies a result; the caller must check the final tree.
import {type Goal,type Path,type Tree,canon} from '../../kernel/kernel.ts'
import {type Step} from '../../core/solver.ts'
import {late} from '../../kernel/prove.ts'
import {rowsAt,wallTree} from './wall-profile.ts'
export function rebasePath(g:Goal,tree:Tree,from:Path,to:Path,until:number):Tree|undefined{
 return wallTree('pin-pruning',()=>{
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
   const before=rowsAt(g,a),after=rowsAt(g,b)
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
