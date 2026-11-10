// T-12 research policies only. Production never imports this module.
import {type C,type E,type Machine,walkOnce} from '../../core/machine.ts'
import {type CountCert,type CountDecl,type Path,substC,substE,truth} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {activeWriteKey} from '../../core/count-recovery/row-cases.ts'
export const t12={cap:false,classes:false,modelFirst:false}
export const fallbackEnd=(end:number,now=clock())=>t12.cap?Math.min(end,now+600):end
export function numericPhase(model:()=>any,natural:()=>any,valid:(q:any)=>boolean){
 if(!t12.modelFirst){const n=natural();return {natural:n,q:n?{tree:n}:model()}}
 const q=model();if('tree'in q||q.why==='refuted, not unfolded'&&q.core||q.stuck==='sat'&&q.witness&&valid(q))return {natural:undefined,q}
 const n=natural();return {natural:n,q:n?{tree:n}:q}
}
const base=(s:string)=>s.endsWith('#')?s.slice(0,-1):s
export function classSelector(m:Machine,ds:CountDecl[],cert:Pick<CountCert,'reads'|'insts'>,hints:Map<string,C[]>){
 const rs=new Map(cert.reads.map(r=>[r[0],r])),counts=new Map(cert.reads.map(r=>{const c=countsForReads(ds,[[r[0],base(r[1]),r[2]]])?.[0];return [r[0],c] as const})),cache=new WeakMap<Path,Map<number,number>>()
 const flags:Record<string,C>={};for(const [n,c]of Object.entries(m.step.flags??{}))flags[n]=c.op==='all'?{op:'=',a:{op:'var',name:'?'+n},b:{op:'const',value:1}}:substC(c,{vars:{},maps:{},flags})
 const vector=(i:number)=>JSON.stringify([...cert.insts[i]!.terms].sort((a,b)=>a[1].localeCompare(b[1])||a[0]-b[0]))
 const rank=(i:number,path:Path):number=>{
  let memo=cache.get(path);if(!memo){memo=new Map();cache.set(path,memo)}const had=memo.get(i);if(had!==undefined)return had
  const q=cert.insts[i]!,reads=q.terms.map(([,id])=>rs.get(id)),frame=q.terms.length===2&&q.unit===0&&reads.every(Boolean)&&base(reads[0]![1])===base(reads[1]![1])&&reads[0]![1]!==reads[1]![1]&&(JSON.stringify(reads[0]![2])===JSON.stringify(reads[1]![2])||truth({op:'=',a:reads[0]![2],b:reads[1]![2]},path)===true)
  let result=6
  if(q.terms.length===1&&q.unit===0)result=7
  else if(frame){
   const maps=new Set<string>();for(const [,id]of q.terms){const c=counts.get(id);if(c)walkOnce(c.body,(o:any)=>{if(o.op==='get')maps.add(o.map)})}
   const unchanged=(map:string):boolean=>{const w=m.step.maps?.[map];if(!w)return true;const each='each'in w?w.each:undefined,e=substE(w.value,{vars:{},maps:{},flags})
    const same=(x:E):boolean=>{if(x.op==='if'){const t=truth(x.c,path);return t===true?same(x.then):t===false?same(x.else):same(x.then)&&same(x.else)}return x.op==='get'&&x.map===map&&!!each&&x.key.op==='var'&&x.key.name===each};return same(e)}
   const actor=activeWriteKey(m,path),away=actor&&reads.some(r=>r&&truth({op:'=',a:r[2],b:actor},path)===false)
   const decreasing=q.terms.some(([z,id])=>z>0&&rs.get(id)?.[1].endsWith('#'))
   result=[...maps].every(unchanged)?0:away&&decreasing?1:4
  }else if(hints.has(vector(i)))result=2
  else if(q.terms.length===2&&q.unit===0){
   const a=counts.get(q.terms[0]![1]),b=counts.get(q.terms[1]![1]);result=a&&b&&JSON.stringify(substE(a.body,{vars:{[a.key]:{op:'var',name:'class$key'}},maps:{},flags:{}}))===JSON.stringify(substE(b.body,{vars:{[b.key]:{op:'var',name:'class$key'}},maps:{},flags:{}}))?3:4
  }else if(q.terms.length>=3)result=5
  memo.set(i,result);return result
 }
 return (indices:number[],path:Path)=>{if(!t12.classes)return indices;const sorted=[...indices].sort((a,b)=>rank(a,path)-rank(b,path)||a-b),first=sorted[0];return first===undefined?[]:sorted.filter(i=>rank(i,path)===rank(first,path))}
}
