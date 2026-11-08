// Untrusted instantiation of an ordinary subtree. Rename its columns and match
// each used row at the destination; no solver, axiom, or symmetry rule is used.
// The caller must check the emitted full tree (or its enclosing certificate).
import {type E,x} from '../machine.ts'
import {type Lin,type Step,add,scale} from '../solver.ts'
import {times} from '../../kernel/reader.ts'
import {type Goal,type Path,type Tree,canon,canonFlip,cellParts,columnTerm,factorsOf,isCell,linear,substE} from '../../kernel/kernel.ts'
import {late,rowsAt} from '../../kernel/prove.ts'
export function renameProof(goal:Goal,tree:Tree,from:Path,to:Path,names:Record<string,string>,until:number):Tree|undefined{
 const vars=Object.fromEntries(Object.entries(names).map(([a,b])=>[a,x(b)])),terms=new WeakMap<E,E>(),indices=new WeakMap<object,Map<string,number>>()
 const renamed=(e:E):E=>{let next=terms.get(e);if(!next){next=substE(e,{vars,maps:{},flags:{}});terms.set(e,next)}return next}
 const form=(lin:Lin,path:Path):Lin|undefined=>{
  let out:Lin={}
  for(const [name,k]of Object.entries(lin)){const next=column(name,path);if(!next)return undefined;out=add(out,scale(next,k))}
  return out
 }
 const column=(name:string,path:Path):Lin|undefined=>{
  if(name==='1')return {'1':1}
  const term=columnTerm(name);if(term)return linear(renamed(term),path)
  const factors=factorsOf(name)
  if(factors.length>1){let out:Lin={'1':1};for(const factor of factors){const next=column(factor,path),product=next&&times(out,next);if(!product)return undefined;out=product}return out}
  if(isCell(name)){
   const cell=cellParts(name),parts=cell.keys??(cell.key?[cell.key]:[]),keys=parts.map(key=>form(key,path))
   if(!keys.length||keys.some(key=>!key))return undefined
   const key=cell.keys?`⟨${keys.map(key=>canon(key!)).join('|')}⟩`:canon(keys[0]!)
   return {[`${cell.map}[${key}]`]:1}
  }
  return {[Object.hasOwn(names,name)?names[name]!:name]:1}
 }
 const visit=(t:Tree,a:Path,b:Path):Tree|undefined=>{
  if(late(until))return undefined
  if('split'in t){
   const split=form(t.split,b);if(!split)return undefined
   const old=canon(t.split),id=canon(split),known=Object.keys(split).every(k=>k==='1')?(split['1']??0)<=0:b.has(id)?b.get(id)!.holds:b.has(canonFlip(split))?!b.get(canonFlip(split))!.holds:undefined
   if(known!==undefined)return visit(known?t.yes:t.no,new Map(a).set(old,{lin:t.split,holds:known}),b)
   const yes=visit(t.yes,new Map(a).set(old,{lin:t.split,holds:true}),new Map(b).set(id,{lin:split,holds:true}))
   const no=yes&&visit(t.no,new Map(a).set(old,{lin:t.split,holds:false}),new Map(b).set(id,{lin:split,holds:false}))
   return yes&&no?{split,yes,no}:undefined
  }
  const before=rowsAt(goal,a),after=rowsAt(goal,b)
  let at=indices.get(after);if(!at){at=new Map();after.forEach((row,i)=>{const id=canon(row.lin);if(!at!.has(id))at!.set(id,i)});indices.set(after,at)}
  const index=(i:number):number|undefined=>{if(!Number.isInteger(i)||i<0)return undefined;if(i>=before.length)return i-before.length+after.length;const row=form(before[i]!.lin,b);return row&&at!.get(canon(row))}
  const leaf:Step[]=[],products:[number,number][]=[],squares:Lin[]=[]
  for(const step of t.leaf){if(step.kind!=='input')leaf.push(step);else{const i=index(step.index);if(i===undefined)return undefined;leaf.push({...step,index:i})}}
  for(const [i,j]of t.products??[]){const a=index(i),b=index(j);if(a===undefined||b===undefined)return undefined;products.push([a,b])}
  for(const square of t.squares??[]){const next=form(square,b);if(!next)return undefined;squares.push(next)}
  return {leaf,...(t.products?{products}:{}),...(t.squares?{squares}:{})}
 }
 return visit(tree,from,to)
}
