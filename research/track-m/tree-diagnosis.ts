// Diagnostic only: report the first rejection made by the existing checker.
// This does not change any proof tree or count as a certificate.
import {type CountCert,type Goal,type Path,type Tree,canon,check,columnTerm,leafConstraints,linear,withProducts} from '../../kernel/kernel.ts'
import {walkOnce} from '../../core/machine.ts'
import {type Lin,add,scale} from '../../core/solver.ts'
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
// Structural provenance, not a new proof rule: count-row leaves lie below a
// failed CInst comparison or a split mentioning its arbitrary row witness.
// All other leaves are arithmetic/control leaves. Both are linear refutations.
export function countLeafKinds(tree:Tree,cert:Pick<CountCert,'reads'|'insts'>,root:Path=new Map()):{countRowLeaves:number,arithmeticLeaves:number}{
 const badFalse=new Set<string>(),badTrue=new Set<string>(),wits=new Set(cert.insts.map(i=>i.wit)),read=new Map(cert.reads.map(r=>[r[0],r])),witnessColumns=new Map<string,boolean>()
 const register=(lin:Lin)=>{badFalse.add(canon(lin));const inverse=scale(lin,-1);inverse['1']=(inverse['1']??0)+1;badTrue.add(canon(inverse))}
 for(const inst of cert.insts){
  let raw:Lin=inst.unit?{'1':-inst.unit}:{},cells:Lin={...raw},complete=true
  for(const [coefficient,id]of inst.terms){raw=add(raw,{[id]:coefficient});const r=read.get(id),l=r&&linear({op:'get',map:r[1],key:r[2]},root);if(l)cells=add(cells,scale(l,coefficient));else complete=false}
  register(raw);if(complete)register(cells)
 }
 const witness=(lin:Lin)=>Object.keys(lin).some(name=>{
  if(witnessColumns.has(name))return witnessColumns.get(name)!
  let found=wits.has(name);const term=columnTerm(name)
  if(term)walkOnce(term,(o:any)=>{if(o.op==='var'&&wits.has(o.name))found=true})
  witnessColumns.set(name,found);return found
 })
 const active=[...root].some(([id,p])=>p.holds?badTrue.has(id):badFalse.has(id))
 let countRowLeaves=0,arithmeticLeaves=0
 const visit=(t:Tree,count:boolean):void=>{
  if('leaf'in t){if(count)countRowLeaves++;else arithmeticLeaves++;return}
  const id=canon(t.split),both=count||witness(t.split)
  visit(t.yes,both||badTrue.has(id));visit(t.no,both||badFalse.has(id))
 }
 visit(tree,active);return {countRowLeaves,arithmeticLeaves}
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
