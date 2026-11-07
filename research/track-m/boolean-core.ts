// Untrusted Boolean-core recipe: expose witness membership before unrelated
// conditional fields. Every terminal branch is an ordinary linear refutation.
import {type C,walkOnce} from '../../core/machine.ts'
import {type Goal,type Path,type Tree,canon,check,linear,truth} from '../../kernel/kernel.ts'
import {refuteFast,sub} from '../../core/solver.ts'
import {clock,grow,rowsAt} from '../../kernel/prove.ts'
import {walkLive} from './live-dependencies.ts'
export function booleanCore(g:Goal,root:Path,wits:Set<string>,until:number,trace:object[]):Tree|undefined{
 const chosen=new Map<string,{c:C,score:number}>(),add=(c:C,score:number)=>{if(truth(c,root)!==undefined)return;const id=JSON.stringify(c),old=chosen.get(id);chosen.set(id,{c,score:score+(old?.score??0)})}
 for(const h of g.hyps){
  let c=h;while(c.op==='not')c=c.x
  if(c.op==='<'||c.op==='<='||c.op==='=')add(c,1000)
 }
 walkLive(g.hyps,root,(o:any)=>{
  if(o.op==='='&&o.a.op==='var'&&o.b.op==='var'&&!wits.has(o.a.name)&&!wits.has(o.b.name))add(o,10)
  if(!['=','<='].includes(o.op))return
  const cell=o.op==='='&&o.a.op==='get'&&o.b.op==='const'&&o.b.value===1?o.a:o.op==='<='&&o.a.op==='const'&&o.a.value===1&&o.b.op==='get'?o.b:undefined
  if(!cell)return
  let hit=false;walkOnce(cell.key,(x:any)=>{if(x.op==='var'&&wits.has(x.name))hit=true})
  if(hit)add(o,o.op==='<='?100:50)
 })
 const cs=[...chosen.values()].sort((a,b)=>b.score-a.score).slice(0,8).flatMap(({c})=>c.op==='='?[{op:'<=' as const,a:c.a,b:c.b},{op:'<=' as const,a:c.b,b:c.a}]:[c])
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
 const start=clock(),tree=go(0,new Map(root)),checked=!!tree&&check(g,tree,root)
 trace.push({stage:'boolean-core',cuts:cs.length,nodes,leaves,ms:Math.round(clock()-start),checked,...(last?{last}:{})})
 return checked?tree:undefined
}
