// Untrusted row-equality case proposals. Every ordering branch is covered and
// every reused recipe is widened and checked at its destination path.
import {type C,type E,type Machine,n,same,walkOnce,x} from '../machine.ts'
import {type CountCert,type Goal,type Path,type Tree,canon,linear,substC,substE,truth} from '../../kernel/kernel.ts'
import {clock,withDeadline} from '../../kernel/prove.ts'
import {scale,sub} from '../solver.ts'
import {walkLive} from './live-dependencies.ts'
import {wallTree,check} from './ops.ts'
import {renameProof} from './rename-proof.ts'
export type RowPair=readonly [E,E]
// Prefer exact scalar destinations, including constant-index initialization.
export function activeWriteKey(m:Machine,root:Path):E|undefined{
 const flags:Record<string,C>={},found=new Map<string,{key:E,rank:number}>()
 for(const [name,c]of Object.entries(m.step.flags??{}))flags[name]=c.op==='all'?same(x(`?${name}`),n(1)):substC(c,{vars:{},maps:{},flags})
 for(const write of Object.values(m.step.maps??{})){
  if(!('each'in write))continue
  walkLive(substE(write.value,{vars:{},maps:{},flags}),root,(o:any)=>{
   if(o.op!=='if'||truth(o.c,root)!==undefined)return
   walkLive(o.c,root,(c:any)=>{
    if(c.op!=='='||truth(c,root)!==undefined)return
    for(const [at,key]of [[c.a,c.b],[c.b,c.a]] as [E,E][]){
     if(at.op!=='var'||at.name!==write.each)continue
     let scalar=true;walkOnce(key,(e:any)=>{if(e.op==='get'||e.op==='var'&&e.name===write.each)scalar=false})
     if(!scalar)continue
     const id=JSON.stringify(key),had=found.get(id);found.set(id,{key,rank:(had?.rank??0)+1})
    }
   })
  })
 }
 return [...found.values()].sort((a,b)=>b.rank-a.rank)[0]?.key
}
export function activeWriteRow(m:Machine,root:Path):string|undefined{
 const exact=activeWriteKey(m,root);if(exact?.op==='var'&&m.inputs.includes(exact.name))return exact.name
 const flags:Record<string,C>={},inputs=new Set(m.inputs),ranks=new Map<string,number>()
 for(const [name,c]of Object.entries(m.step.flags??{}))flags[name]=c.op==='all'?same(x(`?${name}`),n(1)):substC(c,{vars:{},maps:{},flags})
 for(const write of Object.values(m.step.maps??{})){
  if(!('each'in write))continue
  const body=substE(write.value,{vars:{},maps:{},flags})
  walkLive(body,root,(o:any)=>{
   if(o.op!=='if'||truth(o.c,root)!==undefined)return
   walkLive(o.c,root,(c:any)=>{
    if(!['=','<','<='].includes(c.op)||truth(c,root)!==undefined)return
    let indexed=false,cell=false;const found=new Set<string>()
    walkOnce(c,(e:any)=>{if(e.op==='get')cell=true;if(e.op==='var'){if(e.name===write.each)indexed=true;if(inputs.has(e.name))found.add(e.name)}})
    if(indexed&&!cell){for(const name of found)ranks.set(name,(ranks.get(name)??0)+1)}
   })
  })
 }
 return [...ranks].sort((a,b)=>b[1]-a[1]||a[0].localeCompare(b[0]))[0]?.[0]
}
export function rowPairs(m:Machine,cert:Pick<CountCert,'reads'>,root:Path=new Map(),fieldClaim?:C):RowPair[]{
 const ranks=new Map<string,number>(),inputs=new Set(m.inputs)
 walkOnce(m.step.maps,(o:any)=>{if(o.op==='get'&&o.key.op==='var'&&inputs.has(o.key.name))ranks.set(o.key.name,(ranks.get(o.key.name)??0)+1)})
 const fallback=[...ranks].sort((a,b)=>b[1]-a[1]||a[0].localeCompare(b[0]))[0]?.[0],exact=activeWriteKey(m,root),named=exact?undefined:activeWriteRow(m,root)??fallback,actor=exact??(named?x(named):undefined)
 if(!actor)return []
 const names=new Set<string>(),read=cert.reads.find(r=>r[1].endsWith('#'))
 if(read)walkOnce(read[2],(o:any)=>{if(o.op==='var'&&!inputs.has(o.name)&&!m.params.includes(o.name))names.add(o.name)})
 else if(fieldClaim)walkLive(fieldClaim,root,(o:any)=>{
  if(o.op==='get'&&o.map in (m.step.maps??{})&&o.key.op==='var'&&!inputs.has(o.key.name)&&!m.params.includes(o.key.name))names.add(o.key.name)
 })
 return [...names].slice(0,2).map(name=>[x(name),actor] as const)
}
export const proveRowCases:typeof proveRowCasesImpl=(...args)=>wallTree('row-case-reconstruction',()=>proveRowCasesImpl(...args))
function proveRowCasesImpl(g:Goal,root:Path,pairs:RowPair[],until:number,prove:(path:Path,until:number)=>Tree|undefined,trace?:(e:object)=>void,options:{deferToCaller?:boolean,splitEqual?:boolean}={}):Tree|undefined{
 if(!pairs.length||clock()>=until)return undefined
 const cache=new Map<string,{path:Path,tree:Tree}>(),history=new Map<string,{path:Path,tree:Tree}[]>()
 const renaming:Record<string,string>={},pair=pairs.length===2?pairs:undefined
 let mirror=!!pair
 if(pair)for(let i=0;i<2;i++){
  const a=pair[0]![i]!,b=pair[1]![i]!
  if(JSON.stringify(a)===JSON.stringify(b))continue
  if(a.op!=='var'||b.op!=='var'||renaming[a.name]&&renaming[a.name]!==b.name||renaming[b.name]&&renaming[b.name]!==a.name){mirror=false;break}
  renaming[a.name]=b.name;renaming[b.name]=a.name
 }
 const leaf=(path:Path,key:string):Tree|undefined=>{
  if(clock()>=until)return undefined
  const begun=clock(),old=cache.get(key)
  if(old){
   const t=withDeadline(Math.min(until,clock()+50),()=>renameProof(g,old.tree,old.path,path,{},Math.min(until,clock()+50)))
   const accepted=!!t&&(options.deferToCaller||check(g,t,path))
   if(accepted&&t){trace?.({stage:'row-case',key,cached:true,ms:Math.round(clock()-begun),checked:!options.deferToCaller,proposed:true,deferred:!!options.deferToCaller});return t}
  }
  const opposite=key.split('/').reverse().join('/')
  const compatible=(old:{path:Path})=>{
   const vars=Object.fromEntries(Object.entries(renaming).map(([a,b])=>[a,x(b)]));let score=0
   for(const [a,b]of pairs){
    const left=linear(a,old.path),right=linear(b,old.path),nextLeft=linear(substE(a,{vars,maps:{},flags:{}}),path),nextRight=linear(substE(b,{vars,maps:{},flags:{}}),path)
    if(!left||!right||!nextLeft||!nextRight)continue
    for(const sign of [1,-1]){
     const source=old.path.get(canon(scale(sub(left,right),sign)))?.holds,target=path.get(canon(scale(sub(nextLeft,nextRight),sign)))?.holds
     if(source!==undefined&&target!==undefined)score+=source===target?1:-1
    }
   }
   return score
  }
  if(mirror&&key.includes('/'))for(const old of [...history.get(opposite)??[]].reverse().sort((a,b)=>compatible(b)-compatible(a))){
   const t=renameProof(g,old.tree,old.path,path,renaming,Math.min(until,clock()+50))
   const accepted=!!t&&(options.deferToCaller||check(g,t,path))
   if(accepted&&t){trace?.({stage:'row-mirror',from:opposite,to:key,ms:Math.round(clock()-begun),checked:!options.deferToCaller,proposed:true,deferred:!!options.deferToCaller});cache.set(key,{path:new Map(path),tree:t});return t}
  }
  const t=prove(path,Math.min(until,clock()+1500)),accepted=!!t&&(options.deferToCaller||check(g,t,path))
  trace?.({stage:'row-case',key,cached:false,ms:Math.round(clock()-begun),checked:!options.deferToCaller&&accepted,proposed:!!t,deferred:!!options.deferToCaller})
  if(!t||!accepted)return undefined
  const entry={path:new Map(path),tree:t};cache.set(key,entry);history.set(key,[...history.get(key)??[],entry]);return t
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
 const out=split(pairs[0]!,root,p=>options.splitEqual&&pairs[1]?split(pairs[1],p,q=>leaf(q,'equal/equal'),q=>leaf(q,'equal/different')):leaf(p,'equal'),p=>pairs.length<2?leaf(p,'different'):split(pairs[1]!,p,q=>leaf(q,'different/equal'),q=>leaf(q,'different/different')))
 // A composing caller may check this entire proposal after adding its cuts.
 return options.deferToCaller?out:out&&check(g,out,root)?out:undefined
}
