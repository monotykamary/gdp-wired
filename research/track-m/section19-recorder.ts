// Passive capture only: retain returned consumer proofs/cores; analyze after search.
import {type Goal,type Path,type Tree} from '../../kernel/kernel.ts'
type Ids=number[]
export function liveInputs(steps:any[]):number[]{
 const seen=new Set<number>(),inputs=new Set<number>()
 const visit=(i:number):void=>{if(seen.has(i))return;seen.add(i);const s=steps[i];if(!s)throw Error('bad proof step');if(s.kind==='input')inputs.add(s.index);else if(s.kind==='cut')visit(s.of);else if(s.kind==='combine'){if(s.ma)visit(s.a);if(s.mb)visit(s.b)}else throw Error('unknown step')}
 if(steps.length)visit(steps.length-1)
 return [...inputs]
}
class Citations {
 enabled=false;tick=0;zones:string[]=[];reader:()=>any=()=>undefined
 expressions=new WeakMap<object,Ids>();cuts=new WeakMap<object,Ids>();rowContexts=new WeakMap<object,any>()
 marks=new WeakMap<object,any[]>();emissions:any[]=[];consumers:any[]=[];decisions:any[]=[]
 reset(reader:()=>any){this.enabled=true;this.tick=0;this.zones=[];this.reader=reader;this.expressions=new WeakMap();this.cuts=new WeakMap();this.rowContexts=new WeakMap();this.marks=new WeakMap();this.emissions=[];this.consumers=[];this.decisions=[]}
 state(){const r=this.reader(),stack=r?.stack??[],frames=r?.frames??[];return {attempt:[...stack].reverse().find((f:any)=>f.kind==='attempt')?.id,helper:[...stack].reverse().find((f:any)=>f.kind==='helper')?.id,phase:r?.phase,stack:stack.map((f:any)=>f.id),frames}}
 hypOwners(g:Goal){return g.hyps.flatMap((h,i)=>{const ids=this.expressions.get(h);return ids?.length?[[i,[...ids]]]:[]})}
 pathOwners(p:Path){return [...p].flatMap(([key,a])=>{const ids=a.holds?this.cuts.get(a.lin):undefined;return ids?.length?[[key,[...ids]]]:[]})}
 context(g:Goal,p:Path){return {goal:g,path:[...p],hypOwners:this.hypOwners(g),pathOwners:this.pathOwners(p)}}
 emission(f:any,data:any){
  if(!this.enabled||!f||!data?.tree||this.emissions.some(e=>e.id===f.id))return
  const r=this.reader(),h=r.frames[f.meta.helper],good=f.meta.good,cut=data.cut??data.lemma?.cut??[...(data.targetPath??new Map()).values()].at(-1)?.lin
  if(!cut)throw Error('missing emitted cut')
  const e={id:f.id,at:++this.tick,helperId:h?.id,helper:h?.name,kind:f.name,good,cut};this.emissions.push(e)
  this.expressions.set(good,[...(this.expressions.get(good)??[]),f.id]);this.cuts.set(cut,[...(this.cuts.get(cut)??[]),f.id])
 }
 marked(tree:Tree,goal:Goal,lemmas:any[]){if(!this.enabled)return;const versions=this.marks.get(tree)??[];versions.push({at:++this.tick,goal,lemmas,hypOwners:this.hypOwners(goal),lemmaOwners:lemmas.map(l=>[...(this.cuts.get(l.cut)??[])])});this.marks.set(tree,versions)}
 transform<T extends (...args:any[])=>any>(name:string,fn:T,args:Parameters<T>):ReturnType<T>{
  const value=fn(...args);if(!this.enabled)return value
  const ids=this.expressions.get(args[0])??this.cuts.get(args[0])
  if(ids?.length&&['substC','piecesAt'].includes(name)){for(const c of Array.isArray(value)?value:[value])if(c&&typeof c==='object')this.expressions.set(c,[...new Set([...(this.expressions.get(c)??[]),...ids])])}
  if(ids?.length&&['truth','decide'].includes(name)&&typeof value==='boolean'){const {attempt,helper,phase}=this.state();this.decisions.push({at:++this.tick,name,owners:[...ids],attempt,helper,phase,value})}
  return value
 }
 bindRows<T>(g:Goal,p:Path,run:()=>T):T{const rows=run();if(this.enabled&&rows&&typeof rows==='object')this.rowContexts.set(rows,this.context(g,p));return rows}
 call<T>(name:string,g:Goal,p:Path,run:()=>T):T{
  if(!this.enabled)return run()
  const before=this.context(g,p),{attempt,helper,phase,stack}=this.state(),began=++this.tick
  this.zones.push(name);const zones=[...this.zones];let value:any;try{value=run()}finally{this.zones.pop()}
  const tree=value?.tree??(value&&('leaf'in value||'split'in value)?value:undefined),core=Array.isArray(value?.core)?value.core:undefined
  this.consumers.push({id:this.consumers.length,began,at:++this.tick,name,attempt,helper,phase,stack,zones,outcome:tree?'tree':value?.stuck??value?.kind??'none',...(tree||core?{...before,tree,core}:{offered:[...new Set([...before.hypOwners.flatMap((p:any)=>p[1]),...before.pathOwners.flatMap((p:any)=>p[1])])]} )})
  return value
 }
 rows<T>(name:string,rows:any[],run:()=>T):T{
  if(!this.enabled)return run()
  const context=this.rowContexts.get(rows),{attempt,helper,phase,stack}=this.state(),began=++this.tick,value=run() as any
  const tree=value?.kind==='refuted'?{leaf:value.steps}:undefined
  if(tree){const rowOwners=rows.map(r=>[...(this.cuts.get(r.lin)??[])]);this.consumers.push({id:this.consumers.length,began,at:++this.tick,name,attempt,helper,phase,stack,zones:[...this.zones],outcome:'tree',tree,...(context?context:{rawRows:rows,rowOwners})})}
  return value
 }
 snapshots(tree:Tree,at:number){
  const out:any[]=[],walk=(t:Tree,path:string[])=>{const mark=(this.marks.get(t)??[]).filter(m=>m.at<=at).at(-1);const owners=(this.cuts.get((t as any).split)??[]).filter(id=>this.emissions.find(e=>e.id===id)!.at<=at);if(mark||owners.length)out.push({path,...(mark?{mark}:{}),owners});if('split'in t){walk(t.yes,[...path,'yes']);walk(t.no,[...path,'no'])}};walk(tree,[]);return out
 }
 output(){return {version:1,emissions:this.emissions,consumers:this.consumers.map(c=>({...c,...(c.tree?{snapshots:this.snapshots(c.tree,c.at)}:{})})),decisions:this.decisions}}
}
export const citations=new Citations()
