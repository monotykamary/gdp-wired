// Untrusted action/parameter proposals from the machine's own flag shapes.
import {type C,type Machine,any,same,n,walkOnce,x} from '../machine.ts'
import {type Path,substC,substE,truth} from '../../kernel/kernel.ts'
import {walkLive} from './live-dependencies.ts'
export function actionGuard(m:Machine,selector:string,value:number|undefined):C|undefined{
 if(value===undefined)return undefined
 const flags=Object.fromEntries(Object.entries(m.step.flags??{}).map(([name,q])=>[name,q.op==='all'?same(x(`?${name}`),n(1)):q]))
 const guards:C[]=[]
 for(const q of Object.values(m.step.flags??{})){
  if(q.op==='all')continue
  let matches=false
  walkOnce(q,(o:any)=>{if(o.op==='='&&[[o.a,o.b],[o.b,o.a]].some(([a,b])=>a.op==='var'&&a.name===selector&&b.op==='const'&&b.value===value))matches=true})
  if(matches)guards.push(substC(q,{vars:{},maps:{},flags}))
 }
 return guards.length===1?guards[0]:guards.length?any(...guards):undefined
}
export function activeCarried(m:Machine,path:Path):Set<string>{
 const out=new Set<string>(),inputs=new Set(m.inputMaps??[])
 for(const [name,q]of Object.entries(m.step.flags??{})){
  if(q.op!=='all'||truth(same(x(`?${name}`),n(1)),path)!==true)continue
  walkOnce(q.c,(o:any)=>{if(o.op==='get'&&inputs.has(o.map))out.add(o.map)})
 }
 if(!out.size&&m.inputMaps?.[0])out.add(m.inputMaps[0])
 return out
}

// A live same-map read indexed by another input is a copy, unlike the
// unchanged per-member fallback. Its equal-row case may need both keys split.
export function copiesRows(m:Machine,root:Path):boolean{
 const flags:Record<string,C>={};let copy=false
 for(const [name,c]of Object.entries(m.step.flags??{}))flags[name]=c.op==='all'?same(x(`?${name}`),n(1)):substC(c,{vars:{},maps:{},flags})
 for(const [map,write]of Object.entries(m.step.maps??{})){
  if(!('each'in write))continue
  walkLive(substE(write.value,{vars:{},maps:{},flags}),root,(o:any)=>{
   if(o.op!=='get'||o.map!==map)return
   walkOnce(o.key,(key:any)=>{if(key.op==='var'&&key.name!==write.each&&m.inputs.includes(key.name))copy=true})
  })
 }
 return copy
}
