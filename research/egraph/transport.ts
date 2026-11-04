// Solver-free alpha transport and row reindexing. Final kernel checking is mandatory.
import type {E} from '../../core/machine.ts'
import {add,scale,type Lin} from '../../core/solver.ts'
import {canon,cellParts,columnTerm,factorsOf,isCell,isMonomial,leafConstraints,linear,substE,type Goal,type Path,type Tree} from '../../kernel/kernel.ts'
import type {Meter} from './match.ts'
export function renameLinear(lin:Lin,names:Record<string,string>,path:Path,meter:Meter):Lin{
  const multiply=(a:Lin,b:Lin):Lin=>{let out:Lin={};for(const [x,c]of Object.entries(a))for(const [y,d]of Object.entries(b)){meter.tick();const key=[...(x==='1'?[]:factorsOf(x)),...(y==='1'?[]:factorsOf(y))].sort().join('*')||'1';out=add(out,{[key]:c*d})}return out}
  const symbol=(name:string):Lin=>{
    meter.tick()
    if(name==='1')return {'1':1}
    if(isMonomial(name))return factorsOf(name).reduce<Lin>((p,f)=>multiply(p,symbol(f)),{'1':1})
    if(isCell(name)){const p=cellParts(name),key=p.keys?'⟨'+p.keys.map(k=>canon(renameLinear(k,names,path,meter))).join('|')+'⟩':canon(renameLinear(p.key!,names,path,meter));return {[`${p.map}[${key}]`]:1}}
    if(name.startsWith('⟦')){
      const e=columnTerm(name);if(!e)throw Error('unresolved source term column')
      const vars=Object.fromEntries(Object.entries(names).map(([a,b])=>[a,{op:'var',name:b} as E]))
      const out=linear(substE(e,{vars,maps:{},flags:{}}),path);if(!out)throw Error('unresolved renamed term');return out
    }
    return {[names[name]??name]:1}
  }
  let out:Lin={};for(const [name,c]of Object.entries(lin)){meter.tick();out=add(out,scale(symbol(name),c))}
  if(Object.values(out).some(c=>!Number.isSafeInteger(c)))throw Error('unsafe transported coefficient')
  return out
}
export function transportTree(part:Goal,whole:Goal,tree:Tree,names:Record<string,string>,meter:Meter,sp:Path=new Map(),tp:Path=new Map()):Tree{
  meter.tick()
  const original=leafConstraints(part,sp),target=leafConstraints(whole,tp)
  for(let i=0;i<original.length+target.length;i++)meter.tick()
  if('split'in tree){
    const split=renameLinear(tree.split,names,tp,meter),sid=canon(tree.split),tid=canon(split)
    if(tp.has(tid)||Object.keys(split).every(k=>k==='1'))throw Error('collapsed transported cut')
    return {split,yes:transportTree(part,whole,tree.yes,names,meter,new Map(sp).set(sid,{lin:tree.split,holds:true}),new Map(tp).set(tid,{lin:split,holds:true})),no:transportTree(part,whole,tree.no,names,meter,new Map(sp).set(sid,{lin:tree.split,holds:false}),new Map(tp).set(tid,{lin:split,holds:false}))}
  }
  const index=new Map<string,number>();target.forEach((r,i)=>{const key=canon(r.lin);if(!index.has(key))index.set(key,i)})
  const reindex=(i:number):number=>{
    if(!Number.isInteger(i)||i<0)throw Error('invalid source row index')
    if(i>=original.length)return i-original.length+target.length
    const j=index.get(canon(renameLinear(original[i]!.lin,names,tp,meter)));if(j===undefined)throw Error('renamed source row absent from canonical goal');return j
  }
  return {leaf:tree.leaf.map(s=>s.kind==='input'?{...s,index:reindex(s.index)}:s),...(tree.products?{products:tree.products.map(([a,b]):[number,number]=>[reindex(a),reindex(b)])}:{}),...(tree.squares?{squares:tree.squares.map(s=>renameLinear(s,names,tp,meter))}:{})}
}
