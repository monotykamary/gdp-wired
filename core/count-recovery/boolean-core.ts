// Untrusted Boolean-core recipe: expose witness membership before unrelated
// conditional fields. Every terminal branch is an ordinary linear refutation.
import {type C,type E,same,walkOnce,x} from '../machine.ts'
import {type Goal,type Path,type Tree,canon,columnTerm,facts,linear,truth} from '../../kernel/kernel.ts'
import {scale,sub} from '../solver.ts'
import {clock} from '../../kernel/prove.ts'
import {walkLive} from './live-dependencies.ts'
import {foldPath} from './fold-path.ts'
import {closeKeyReads} from './key-closure.ts'
import {rebasePath} from './rebase-path.ts'
import {wallTree,check,refuteFast,grow,rowsAt} from './ops.ts'
// Unlike dependency slicing, proof-case discovery must still enter the
// operands of a comparison already forced true: its conditional columns
// can remain inconsistent until their own guards have been decided.
export function walkChoices(root:unknown,path:Path,visit:(value:any)=>void):void{
 const goals=new WeakSet<object>(),conditions=new WeakSet<object>()
 const go=(value:any,condition=false):void=>{
  const seen=condition?conditions:goals
  if(!value||typeof value!=='object'||seen.has(value))return
  seen.add(value)
  if(condition&&['not','and','or','<','<=','='].includes(value.op)&&truth(value as C,path)!==undefined)return
  if(value.op==='if'){
   const chosen=truth(value.c,path)
   if(chosen!==undefined){go(chosen?value.then:value.else);return}
   visit(value);go(value.c,true);go(value.then);go(value.else);return
  }
  visit(value)
  for(const child of Array.isArray(value)?value:Object.values(value))go(child,condition)
 }
 go(root)
}
export function booleanCandidates(g:Goal,root:Path,wits:Set<string>,extended=false):{c:C,score:number}[]{
 const walk=extended?walkChoices:walkLive
 const chosen=new Map<string,{c:C,score:number}>(),add=(c:C,score:number)=>{if(truth(c,root)!==undefined)return;const id=JSON.stringify(c),old=chosen.get(id);chosen.set(id,{c,score:score+(old?.score??0)})}
 for(const h of g.hyps){
  let c=h;while(c.op==='not')c=c.x
  if(c.op==='<'||c.op==='<='||c.op==='=')add(c,1000)
 }
 walk(g.hyps,root,(o:any)=>{
  if(o.op==='='&&o.a.op==='var'&&o.b.op==='var'){
   const a=wits.has(o.a.name),b=wits.has(o.b.name)
   if(!a&&!b)add(o,10)
   else if(a!==b)add(o,1500)
  }
  if((o.op==='<'||o.op==='<=')&&o.a.op==='var'&&o.b.op==='var'&&o.a.name!==o.b.name&&!wits.has(o.a.name)&&!wits.has(o.b.name))add(o,extended?1400:750)
  if(extended&&['<','<=','='].includes(o.op)){
   let left=false,right=false,witness=false
   walkLive(o.a,root,(e:any)=>{if(e.op==='get')left=true;if(e.op==='var'&&wits.has(e.name))witness=true})
   walkLive(o.b,root,(e:any)=>{if(e.op==='get')right=true;if(e.op==='var'&&wits.has(e.name))witness=true})
   if(left&&right&&witness)add(o,1000)
  }
  if(!['=','<='].includes(o.op))return
  // A lowered Boolean map write is still one membership predicate. Prefer
  // its shared 0/1 value over independently splitting every internal guard.
  const value=o.op==='='&&o.b.op==='const'&&o.b.value===1?o.a:o.op==='<='&&o.a.op==='const'&&o.a.value===1?o.b:undefined
  if(extended&&value?.op==='if'&&value.then.op==='const'&&value.then.value===1&&value.else.op==='const'&&value.else.value===0){
   let hit=false;walkOnce(value,(e:any)=>{if(e.op==='var'&&wits.has(e.name))hit=true})
   if(hit)add(o,1800)
  }
  const cell=o.op==='='&&o.a.op==='get'&&o.b.op==='const'&&o.b.value===1?o.a:o.op==='<='&&o.a.op==='const'&&o.a.value===1&&o.b.op==='get'?o.b:undefined
  if(!cell)return
  let hit=false;walkOnce(cell.key,(x:any)=>{if(x.op==='var'&&wits.has(x.name))hit=true})
  if(hit)add(o,extended?1200:o.op==='<='?100:50)
 })
 // Equal witness keys are useful before splitting the two cells' values.
 // Their equality is only a proposal: both key-order branches still check.
 const cells=new Map<string,E[]>()
 walk(g.hyps,root,(o:any)=>{if(o.op==='get'&&linear(o.key,root)){const xs=cells.get(o.map)??[];if(!xs.some(k=>JSON.stringify(k)===JSON.stringify(o.key)))xs.push(o.key);cells.set(o.map,xs)}})
 const mentions=(key:E)=>{const out=new Set<string>();walkOnce(key,(o:any)=>{if(o.op==='var'&&wits.has(o.name))out.add(o.name)});return out}
 for(const keys of cells.values())for(let i=0;i<keys.length;i++)for(let j=i+1;j<keys.length;j++){
  const a=keys[i]!,b=keys[j]!,wanted=mentions(a)
  if([...mentions(b)].some(w=>wanted.has(w)))add(same(a,b),500)
 }
 return [...chosen.values()]
}
export const booleanCore:typeof booleanCoreImpl=(...args)=>wallTree('tree-reconstruction',()=>booleanCoreImpl(...args))
function booleanCoreImpl(g:Goal,root:Path,wits:Set<string>,until:number,trace:object[],options:{model?:boolean,folded?:boolean,extended?:boolean,scalarGuards?:boolean,deferCheck?:boolean}={}):Tree|undefined{
 const start=clock(),scalarGuards=options.scalarGuards??false,extended=options.extended??false
 // Lift the goal's own forced linear facts into the path, with a checked
 // opposite branch for every cut. They need not consume the Boolean pool.
 let pinned:Path=new Map(root)
 const prefix:{split:Record<string,number>,no:Tree}[]=[]
 const pin=(split:Record<string,number>):boolean=>{
  const id=canon(split);if(pinned.get(id)?.holds===true)return true
  if(clock()>=until)return false
  const other=new Map(pinned).set(id,{lin:split,holds:false}),out=refuteFast(rowsAt(g,other),256)
  const no:Tree|undefined=out?.kind==='refuted'?{leaf:out.steps}:undefined
  if(!no||(!options.deferCheck&&!check(g,no,other)))return false
  prefix.push({split,no});pinned=new Map(pinned).set(id,{lin:split,holds:true});return true
 }
 for(let round=0;round<2&&clock()<until;round++)for(const h of g.hyps)for(const split of facts(h,pinned))pin(split)
 // Witness bounds and inactive scalar selectors can follow from the path
 // without appearing as literal decisions. Prove these arithmetic guards
 // before discovering candidates, so dead updates cannot crowd the pool.
 const guards=new Map<string,C>(),walk=scalarGuards?walkChoices:walkLive
 walk(g.hyps,root,(o:any)=>{if(o.op==='if')walkOnce(o.c,(c:any)=>{
  if(!['<','<=','='].includes(c.op))return
  let witness=false,plain=true
  walkOnce(c,(e:any)=>{if(e.op==='var'&&wits.has(e.name))witness=true;if(['get','if','sub','min','max','prod','tup','proj'].includes(e.op))plain=false})
  if(plain&&(scalarGuards||witness))guards.set(JSON.stringify(c),c)
 })})
 for(const c of guards.values())for(const split of facts(c,pinned)){
  if(scalarGuards&&truth(c,pinned)!==undefined)break
  if(!pin(split)){const inverse=scale(split,-1);inverse['1']=(inverse['1']??0)+1;pin(inverse)}
 }

 const candidates=booleanCandidates(g,scalarGuards?pinned:root,wits,extended).filter(({c})=>truth(c,pinned)===undefined)
 const selected=candidates.sort((a,b)=>b.score-a.score).slice(0,8),slots:number[]=[]
 const expand=(c:C):C[]=>c.op==='='?[{op:'<=' as const,a:c.a,b:c.b},{op:'<=' as const,a:c.b,b:c.a}]:[c]
 const cs=selected.flatMap(({c},slot)=>{const parts=expand(c);slots.push(...parts.map(()=>slot));return parts})
 let nodes=0,leaves=0,last:unknown
 const go=(i:number,path:Path,keysClosed=false,plan=cs):Tree|undefined=>{
  if(clock()>=until)return undefined
  nodes++
  const out=refuteFast(rowsAt(g,path),1000)
  if(out?.kind==='refuted')return {leaf:out.steps}
  if(i===plan.length){
   leaves++;const out=grow(g,path,{nodes:0,until,units:true})
   if('tree'in out)return out.tree
   last??={path:[...path],outcome:out.stuck,...(options.model&&'witness'in out?{model:out.witness,columns:Object.fromEntries(Object.keys(out.witness??{}).filter(name=>name.startsWith('⟦')).slice(0,8).map(name=>[name,columnTerm(name)]))}:{})};return undefined
  }
  if(extended&&!keysClosed){
   let field=false;walkOnce(plan[i],(o:any)=>{if(o.op==='get')field=true})
   if(field){
    const reads:{map:string,key:E}[]=[];walkChoices(g.hyps,path,(o:any)=>{if(o.op==='get')reads.push({map:o.map,key:o.key})})
    const begun=clock(),closed=closeKeyReads(g,path,reads,wits,until)
    // Refresh only the unspent choice slots. Fold expression operands, not
    // whole forced hypotheses, so their indicator structure stays visible.
    const folded=new WeakMap<object,E>(),fold=(e:E):E=>{
     const found=folded.get(e);if(found)return found
     const out=foldPath({name:'candidate operand',hyps:[same(e,x('boolean$probe'))]},closed.path).goal.hyps[0]
     const result=out?.op==='='?out.a:e;folded.set(e,result);return result
    }
    const fresh=new Map<string,{c:C,score:number}>()
    for(const candidate of booleanCandidates(g,closed.path,wits,true)){
     const c=candidate.c,normalized:C=c.op==='<'||c.op==='<='||c.op==='='?{...c,a:fold(c.a),b:fold(c.b)}:c
     if(truth(normalized,closed.path)!==undefined)continue
     const id=JSON.stringify(normalized),old=fresh.get(id)
     fresh.set(id,{c:normalized,score:Math.max(old?.score??0,candidate.score)})
    }
    const remaining=Math.max(0,8-(slots[i]??8)),refreshed=[...fresh.values()].sort((a,b)=>b.score-a.score).slice(0,remaining).flatMap(({c})=>expand(c))
    let tree=go(0,closed.path,true,refreshed)
    if(tree)for(const cut of [...closed.cuts].reverse())tree={split:cut.split,yes:tree,no:cut.no}
    trace.push({stage:'key-closure',facts:closed.cuts.length,ms:Math.round(clock()-begun),proposed:!!tree})
    return tree
   }
  }
  const c=plan[i]!,known=truth(c,path)
  if(known!==undefined)return go(i+1,path,keysClosed,plan)
  if(c.op!=='<'&&c.op!=='<=')return undefined
  const a=linear(c.a,path),b=linear(c.b,path);if(!a||!b)return undefined
  const split=sub(a,b);if(c.op==='<')split['1']=(split['1']??0)+1
  const id=canon(split),yes=go(i+1,new Map(path).set(id,{lin:split,holds:true}),keysClosed,plan),no=yes&&go(i+1,new Map(path).set(id,{lin:split,holds:false}),keysClosed,plan)
  return yes&&no?{split,yes,no}:undefined
 }
 let tree=go(0,pinned)
 if(tree){
  const paths:Path[]=[new Map(root)];for(const p of prefix)paths.push(new Map(paths.at(-1)!).set(canon(p.split),{lin:p.split,holds:true}))
  let removed=0
  for(let i=prefix.length-1;i>=0;i--){
   const p=prefix[i]!,shorter=rebasePath(g,tree,paths[i+1]!,paths[i]!,until)
   if(shorter){tree=shorter;removed++}else tree={split:p.split,yes:tree,no:p.no}
  }
  trace.push({stage:'pin-prune',removed,kept:prefix.length-removed})
 }
 const accepted=!!tree&&(options.deferCheck||check(g,tree,root)),checked=accepted&&!options.deferCheck
 trace.push({stage:'boolean-core',facts:prefix.length,cuts:cs.length,nodes,leaves,ms:Math.round(clock()-start),checked,proposed:!!tree,deferred:!!options.deferCheck,...(options.model?{choices:cs.map(c=>({op:c.op,...('a'in c?{a:JSON.stringify(c.a).slice(0,180),b:JSON.stringify(c.b).slice(0,180)}:{})}))}:{}),...(last?{last}:{})})
 return accepted?tree:undefined
}
