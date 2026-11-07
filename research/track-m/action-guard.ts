// Untrusted action/parameter proposals from the machine's own flag shapes.
import {type C,type Machine,any,same,n,walkOnce,x} from '../../core/machine.ts'
import {type Path,substC,truth} from '../../kernel/kernel.ts'
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
