// Diagnostic only: report the first rejection made by the existing checker.
// This does not change any proof tree or count as a certificate.
import {type Goal,type Path,type Tree,canon,check,leafConstraints,withProducts} from '../../kernel/kernel.ts'
export function treeMetrics(tree:Tree):{nodes:number,leaves:number,steps:number,depth:number,unique:number}{
 const seen=new Map<Tree,{nodes:number,leaves:number,steps:number,depth:number}>()
 const visit=(t:Tree):{nodes:number,leaves:number,steps:number,depth:number}=>{
  const cached=seen.get(t);if(cached)return cached
  const a='leaf'in t?undefined:visit(t.yes),b='leaf'in t?undefined:visit(t.no)
  const result='leaf'in t?{nodes:1,leaves:1,steps:t.leaf.length,depth:0}:{nodes:1+a!.nodes+b!.nodes,leaves:a!.leaves+b!.leaves,steps:a!.steps+b!.steps,depth:1+Math.max(a!.depth,b!.depth)}
  seen.set(t,result);return result
 }
 return {...visit(tree),unique:seen.size}
}
export function diagnoseTree(g:Goal,tree:Tree,root:Path=new Map()):object|undefined{
 const walk=(t:Tree,path:Path,leaves:boolean):object|undefined=>{
  if('leaf'in t){
   if(!leaves||check(g,t,path))return undefined
   const rows=withProducts(leafConstraints(g,path),t.products??[],t.squares)
   return {kind:'leaf',path:[...path],steps:t.leaf,inputs:t.leaf.flatMap(s=>s.kind==='input'?[{index:s.index,lin:rows[s.index]?.lin}]:[])}
  }
  const id=canon(t.split)
  if(path.has(id))return {kind:'duplicate-split',id,path:[...path]}
  if(Object.keys(t.split).every(k=>k==='1'))return {kind:'constant-split',id}
  return walk(t.yes,new Map(path).set(id,{lin:t.split,holds:true}),leaves)??walk(t.no,new Map(path).set(id,{lin:t.split,holds:false}),leaves)
 }
 return walk(tree,root,false)??walk(tree,root,true)
}
