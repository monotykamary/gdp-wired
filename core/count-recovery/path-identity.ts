// Exact structural path identities, local to one weakly owned goal. This is
// the same ordered (key, holds, canon(lin)) word as the former JSON cache key.
// Common cut prefixes share nodes; no complete serialized path is retained.
// No hash, lossy prefix, capacity eviction or mutable-Path-identity shortcut.
import {type Path,canon} from '../../kernel/kernel.ts'
type Node={parent?:Node,atom?:object,next?:WeakMap<object,WeakRef<Node>>}
type Choices=Map<boolean,Map<string,object>>
export class ExactPathIdentity {
 private readonly atoms=new Map<string,Choices>()
 private readonly root:Node={}
 private atomCount=0
 private nodeCount=1
 get(path:Path):object{
  let node=this.root
  for(const[key,a]of path){
   // Canonicalization is still executed once for EVERY entry on EVERY lookup,
   // in the original order, including hits and interrupted constructions.
   const text=canon(a.lin)
   let choices=this.atoms.get(key)
   if(!choices)this.atoms.set(key,choices=new Map())
   let values=choices.get(a.holds)
   if(!values)choices.set(a.holds,values=new Map())
   let atom=values.get(text)
   if(!atom){values.set(text,atom={});this.atomCount++}
   const next=node.next??(node.next=new WeakMap())
   let child=next.get(atom)?.deref()
   if(!child){child={parent:node,atom};next.set(atom,new WeakRef(child));this.nodeCount++}
   node=child
  }
  return node
 }
 // Intrinsic structural counts for the focused sharing test, not an RSS claim.
 shape():Readonly<{atoms:number,nodes:number}>{return {atoms:this.atomCount,nodes:this.nodeCount}}
}
