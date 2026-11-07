// Untrusted Boolean-core recipe: expose witness membership before unrelated
// conditional fields. Every terminal branch is an ordinary linear refutation.
import {type C,type E,same,walkOnce} from '../../core/machine.ts'
import {type Goal,type Path,type Tree,canon,check,columnTerm,facts,linear,truth} from '../../kernel/kernel.ts'
import {refuteFast,scale,sub} from '../../core/solver.ts'
import {clock,grow,rowsAt} from '../../kernel/prove.ts'
import {walkLive} from './live-dependencies.ts'
export function booleanCandidates(g:Goal,root:Path,wits:Set<string>):{c:C,score:number}[]{
 const chosen=new Map<string,{c:C,score:number}>(),add=(c:C,score:number)=>{if(truth(c,root)!==undefined)return;const id=JSON.stringify(c),old=chosen.get(id);chosen.set(id,{c,score:score+(old?.score??0)})}
 for(const h of g.hyps){
  let c=h;while(c.op==='not')c=c.x
  if(c.op==='<'||c.op==='<='||c.op==='=')add(c,1000)
 }
 walkLive(g.hyps,root,(o:any)=>{
  if(o.op==='='&&o.a.op==='var'&&o.b.op==='var'){
   const a=wits.has(o.a.name),b=wits.has(o.b.name)
   if(!a&&!b)add(o,10)
   else if(a!==b)add(o,500)
  }
  if(!['=','<='].includes(o.op))return
  const cell=o.op==='='&&o.a.op==='get'&&o.b.op==='const'&&o.b.value===1?o.a:o.op==='<='&&o.a.op==='const'&&o.a.value===1&&o.b.op==='get'?o.b:undefined
  if(!cell)return
  let hit=false;walkOnce(cell.key,(x:any)=>{if(x.op==='var'&&wits.has(x.name))hit=true})
  if(hit)add(o,o.op==='<='?100:50)
 })
 // Equal witness keys are useful before splitting the two cells' values.
 // Their equality is only a proposal: both key-order branches still check.
 const cells=new Map<string,E[]>()
 walkLive(g.hyps,root,(o:any)=>{if(o.op==='get'&&linear(o.key,root)){const xs=cells.get(o.map)??[];if(!xs.some(k=>JSON.stringify(k)===JSON.stringify(o.key)))xs.push(o.key);cells.set(o.map,xs)}})
 const mentions=(key:E)=>{const out=new Set<string>();walkOnce(key,(o:any)=>{if(o.op==='var'&&wits.has(o.name))out.add(o.name)});return out}
 for(const keys of cells.values())for(let i=0;i<keys.length;i++)for(let j=i+1;j<keys.length;j++){
  const a=keys[i]!,b=keys[j]!,wanted=mentions(a)
  if([...mentions(b)].some(w=>wanted.has(w)))add(same(a,b),500)
 }
 return [...chosen.values()]
}
export function booleanCore(g:Goal,root:Path,wits:Set<string>,until:number,trace:object[]):Tree|undefined{
 const start=clock()
 // Lift the goal's own forced linear facts into the path, with a checked
 // opposite branch for every cut. They need not consume the Boolean pool.
 let pinned:Path=new Map(root)
 const prefix:{split:Record<string,number>,no:Tree}[]=[]
 const pin=(split:Record<string,number>):boolean=>{
  const id=canon(split);if(pinned.get(id)?.holds===true)return true
  if(clock()>=until)return false
  const other=new Map(pinned).set(id,{lin:split,holds:false}),out=refuteFast(rowsAt(g,other),256)
  const no:Tree|undefined=out?.kind==='refuted'?{leaf:out.steps}:undefined
  if(!no||!check(g,no,other))return false
  prefix.push({split,no});pinned=new Map(pinned).set(id,{lin:split,holds:true});return true
 }
 for(let round=0;round<2&&clock()<until;round++)for(const h of g.hyps)for(const split of facts(h,pinned))pin(split)
 // A row bound can be forced by the witness domain and row equality without
 // being a literal in the goal. Propose only arithmetic guards on that key.
 const guards=new Map<string,C>()
 walkLive(g.hyps,root,(o:any)=>{if(o.op==='if')walkOnce(o.c,(c:any)=>{
  if(!['<','<=','='].includes(c.op))return
  let witness=false,plain=true
  walkOnce(c,(e:any)=>{if(e.op==='var'&&wits.has(e.name))witness=true;if(['get','if','sub','min','max','prod','tup','proj'].includes(e.op))plain=false})
  if(witness&&plain)guards.set(JSON.stringify(c),c)
 })})
 for(const c of guards.values())for(const split of facts(c,pinned))if(!pin(split)){const inverse=scale(split,-1);inverse['1']=(inverse['1']??0)+1;pin(inverse)}

 const candidates=booleanCandidates(g,root,wits).filter(({c})=>truth(c,pinned)===undefined)
 const cs=candidates.sort((a,b)=>b.score-a.score).slice(0,8).flatMap(({c})=>c.op==='='?[{op:'<=' as const,a:c.a,b:c.b},{op:'<=' as const,a:c.b,b:c.a}]:[c])
 let nodes=0,leaves=0,last:unknown
 const go=(i:number,path:Path):Tree|undefined=>{
  if(clock()>=until)return undefined
  nodes++
  const out=refuteFast(rowsAt(g,path),1000)
  if(out?.kind==='refuted')return {leaf:out.steps}
  if(i===cs.length){
   leaves++;const out=grow(g,path,{nodes:0,until,units:true})
   if('tree'in out)return out.tree
   last??={path:[...path],outcome:out.stuck};return undefined
  }
  const c=cs[i]!,known=truth(c,path)
  if(known!==undefined)return go(i+1,path)
  if(c.op!=='<'&&c.op!=='<=')return undefined
  const a=linear(c.a,path),b=linear(c.b,path);if(!a||!b)return undefined
  const split=sub(a,b);if(c.op==='<')split['1']=(split['1']??0)+1
  const id=canon(split),yes=go(i+1,new Map(path).set(id,{lin:split,holds:true})),no=yes&&go(i+1,new Map(path).set(id,{lin:split,holds:false}))
  return yes&&no?{split,yes,no}:undefined
 }
 let tree=go(0,pinned)
 if(tree)for(const p of [...prefix].reverse())tree={split:p.split,yes:tree,no:p.no}
 const checked=!!tree&&check(g,tree,root)
 if(!checked&&process.env.LAB_BOOLEAN_DUMP==='1'){
  const names=new Set([...JSON.stringify([g,[...pinned]]).matchAll(/⟦\d+⟧/g)].map(m=>m[0])),terms=Object.fromEntries([...names].map(name=>[name,columnTerm(name)]))
  trace.push({stage:'boolean-fixture',goal:g,root:[...pinned],wits:[...wits],choices:cs,candidates,terms})
 }
 trace.push({stage:'boolean-core',facts:prefix.length,cuts:cs.length,nodes,leaves,ms:Math.round(clock()-start),checked,...(last?{last}:{})})
 return checked?tree:undefined
}
