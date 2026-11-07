// Untrusted row-equality case proposals. Every ordering branch is covered and
// every reused recipe is widened and checked at its destination path.
import {type C,type E,type Machine,walkOnce,x} from '../../core/machine.ts'
import {type CountCert,type Goal,type Path,type Tree,canon,check,linear,truth} from '../../kernel/kernel.ts'
import {clock,widen,withDeadline} from '../../kernel/prove.ts'
import {scale,sub} from '../../core/solver.ts'
export type RowPair=readonly [E,E]
export function rowPairs(m:Machine,cert:Pick<CountCert,'reads'>):RowPair[]{
 const ranks=new Map<string,number>(),inputs=new Set(m.inputs)
 walkOnce(m.step.maps,(o:any)=>{if(o.op==='get'&&o.key.op==='var'&&inputs.has(o.key.name))ranks.set(o.key.name,(ranks.get(o.key.name)??0)+1)})
 const actor=[...ranks].sort((a,b)=>b[1]-a[1]||a[0].localeCompare(b[0]))[0]?.[0]
 if(!actor)return []
 const names=new Set<string>(),read=cert.reads.find(r=>r[1].endsWith('#'))
 if(read)walkOnce(read[2],(o:any)=>{if(o.op==='var'&&!inputs.has(o.name)&&!m.params.includes(o.name))names.add(o.name)})
 return [...names].slice(0,2).map(name=>[x(name),x(actor)] as const)
}
export function proveRowCases(g:Goal,root:Path,pairs:RowPair[],until:number,prove:(path:Path,until:number)=>Tree|undefined,trace?:(e:object)=>void):Tree|undefined{
 if(!pairs.length||clock()>=until)return undefined
 const cache=new Map<string,{path:Path,tree:Tree}>()
 const leaf=(path:Path,key:string):Tree|undefined=>{
  if(clock()>=until)return undefined
  const begun=clock(),old=cache.get(key)
  if(old){
   const t=withDeadline(Math.min(until,clock()+50),()=>widen(g,g,old.tree,{},old.path,path))
   if(t&&check(g,t,path)){trace?.({stage:'row-case',key,cached:true,ms:Math.round(clock()-begun),checked:true});return t}
  }
  const t=prove(path,Math.min(until,clock()+1500)),checked=!!t&&check(g,t,path)
  trace?.({stage:'row-case',key,cached:false,ms:Math.round(clock()-begun),checked})
  if(!t||!checked)return undefined
  cache.set(key,{path:new Map(path),tree:t});return t
 }
 const split=(pair:RowPair,path:Path,yes:(p:Path)=>Tree|undefined,no:(p:Path)=>Tree|undefined):Tree|undefined=>{
  const condition:C={op:'=',a:pair[0],b:pair[1]},known=truth(condition,path)
  if(known!==undefined)return known?yes(path):no(path)
  const a=linear(pair[0],path),b=linear(pair[1],path);if(!a||!b)return undefined
  const diff=sub(a,b),back=scale(diff,-1)
  const branch=(lin:typeof diff,p:Path,on:(q:Path)=>Tree|undefined,off:(q:Path)=>Tree|undefined):Tree|undefined=>{
   const id=canon(lin),had=p.get(id)?.holds
   if(had!==undefined)return had?on(p):off(p)
   const y=on(new Map(p).set(id,{lin,holds:true}));if(!y)return undefined
   const n=off(new Map(p).set(id,{lin,holds:false}));return n?{split:lin,yes:y,no:n}:undefined
  }
  return branch(diff,path,p=>branch(back,p,yes,no),no)
 }
 // Try the primary-equal case without a secondary split. Its returned proof
 // must cover every secondary key. The other two logical cases are shared
 // between the less-than and greater-than representations of disequality.
 const out=split(pairs[0]!,root,p=>leaf(p,'equal'),p=>pairs.length<2?leaf(p,'different'):split(pairs[1]!,p,q=>leaf(q,'different/equal'),q=>leaf(q,'different/different')))
 return out&&check(g,out,root)?out:undefined
}
