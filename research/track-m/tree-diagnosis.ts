// Diagnostic only: report the first rejection made by the existing checker.
// This does not change any proof tree or count as a certificate.
import {type Goal,type Path,type Tree,canon,check,leafConstraints,withProducts} from '../../kernel/kernel.ts'
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
