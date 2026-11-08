// Checked field-ceiling cuts suggested by a counted predicate and a carried
// set's per-member bound. The suggestion is untrusted; every cut is reconstructed
// and the complete result is checked against the original counted goal.
import {type C,type Machine,n,same,walkOnce,x} from '../machine.ts'
import {type CountCert,type CountDecl,type Goal,type Path,type Tree,canon,columnTerm,linear,substC,substE,truth} from '../../kernel/kernel.ts'
import {countsForReads} from '../count-facts.ts'
import {sub} from '../solver.ts'
import {liftCountProxies} from './lift-count-proxies.ts'
import {piecesAt,sourceScalarContext,sourceWitnessContext,walkLive} from './live-dependencies.ts'
import {carriedCase} from './carried-case.ts'
import {foldPath} from './fold-path.ts'
import {fieldCase} from './field-case.ts'
import {type SourceProofMemo} from './source-memo.ts'
import {booleanCore} from './boolean-core.ts'
import {selectCountBounds} from '../count-select.ts'
import {activeWriteRow,proveRowCases,rowPairs} from './row-cases.ts'
import {proveNaturalCases} from './natural-cases.ts'
import {activeCarried,copiesRows} from './action-guard.ts'
import {atPoint,clock,pastWall,withDeadline} from '../../kernel/prove.ts'

import {REFUTED} from '../../kernel/cdcl.ts'
import {wallTree,check,refuteFast,grow,rowsAt,widen,modelSequence} from './ops.ts'
type Proposal=Pick<CountCert,'reads'|'insts'>
// Bridge only cells used by the incoming path, including cells hidden inside
// natural-subtraction columns. Other count terms are already rewritten in g.
export function countBindingsAt(reads:CountCert['reads'],root:Path):C[]{
 const columns=new Set([...root.values()].flatMap(p=>Object.keys(p.lin)))
 for(const name of columns){const e=columnTerm(name);if(e)walkOnce(e,(o:any)=>{
  if(o.op==='var')columns.add(o.name)
  if(o.op==='get')for(const key of Object.keys(linear(o,root)??{}))columns.add(key)
 })}
 return reads.flatMap(([id,map,key])=>{const cell={op:'get' as const,map,key},lin=linear(cell,root);return lin&&Object.keys(lin).some(k=>columns.has(k))?[same(x(id),cell)]:[]})
}
export function fieldBounds(m:Machine,ds:CountDecl[],cert:Proposal,options:{claim?:C,path?:Path}={}):C[]{
 const key=x('$member'),bounds:{a:unknown,b:any,guard:C}[]=[]
 for(const [name,q] of Object.entries(m.step.flags??{}))if(q.op==='all')walkOnce(substC(q.c,{vars:{[q.key]:key},maps:{},flags:{}}),(c:any)=>{
  const next=c.op==='<'&&c.b?.op==='add'&&c.b.b.op==='const'&&c.b.b.value===1?c.b.a:undefined
  const pairs=c.op==='='?[[c.a,c.b],[c.b,c.a]]:c.op==='<='?[[c.a,c.b]]:next?[[c.a,next]]:[]
  for(const [left,right]of pairs)if(right&&left?.op==='get'&&JSON.stringify(left).includes('"name":"$member"')&&!JSON.stringify(right).includes('"name":"$member"'))bounds.push({a:left,b:right,guard:{op:'=',a:x(`?${name}`),b:{op:'const',value:1}}})
 })
 const out:C[]=[],seen=new Set<string>(),pre=new Set(cert.reads.filter(r=>!r[1].endsWith('#')).map(r=>r[0]))
 for(const c of countsForReads(ds,cert.reads)??[])if(pre.has(c.v))walkOnce(substE(c.body,{vars:{[c.key]:key},maps:{},flags:{}}),(p:any)=>{
  if(p.op!=='<'||p.a?.op!=='get'||JSON.stringify(p.b).includes('"name":"$member"'))return
  for(const b of bounds)if(JSON.stringify(b.a)===JSON.stringify(p.a)){
   const guard:C=p.b.op==='get'?{op:'and',xs:[b.guard,{op:'<',a:p.b.key,b:c.below}]}:b.guard
   const candidate:C={op:'<=',a:{op:'if',c:guard,then:p.b,else:{op:'const',value:0}},b:b.b},id=JSON.stringify(candidate)
   if(!seen.has(id)){seen.add(id);out.push(candidate)}
  }
 })
 const explicit=new Set<string>()
 if(options.claim)walkLive(options.claim,options.path??new Map(),(o:any)=>{if(o.op==='get')explicit.add(JSON.stringify(o))})
 const targets=new Set<string>(explicit),twins=cert.reads.filter(r=>r[1].endsWith('#')).map(([v,map,key])=>[v,map.slice(0,-1),key] as [string,string,typeof key])
 for(const c of countsForReads(ds,twins)??[])walkOnce(substE(c.body,{vars:{[c.key]:key},maps:{},flags:{}}),(p:any)=>{
  if(p.op==='<'&&bounds.some(b=>JSON.stringify(b.a)===JSON.stringify(p.a)))targets.add(JSON.stringify(p.b))
 })
 // Old input-key values used by writes also need a ceiling: otherwise a
 // post-count core can omit the actor's own pre-state version entirely.
 walkOnce(m.step.maps,(o:any)=>{if(o.op==='get'&&o.key.op==='var'&&m.inputs.includes(o.key.name))targets.add(JSON.stringify(o))})
 const focused=out.filter(c=>c.op==='<='&&c.a.op==='if'&&targets.has(JSON.stringify(c.a.then)))
 return (focused.length?focused:out).sort((a,b)=>Number(b.op==='<='&&b.a.op==='if'&&explicit.has(JSON.stringify(b.a.then)))-Number(a.op==='<='&&a.a.op==='if'&&explicit.has(JSON.stringify(a.a.then)))).slice(0,4)
}
// A candidate only: the source checker must still prove its count is empty.
export function emptyCountCandidate(m:Machine,cert:Proposal,inst:Proposal['insts'][number]):boolean{
 if(inst.unit!==0||inst.terms.length!==1||inst.terms[0]![0]!==1)return false
 const read=cert.reads.find(r=>r[0]===inst.terms[0]![1]);if(!read?.[1].endsWith('#'))return false
 const count=m.counts?.[read[1].slice(0,-1)];if(!count)return false
 let fields=false;walkOnce(count.body,(o:any)=>{if(o.op==='<'&&o.a.op==='get'&&o.b.op==='get')fields=true})
 return fields
}
export const fieldBoundLemmas:typeof fieldBoundLemmasImpl=(...args)=>wallTree('proposal-control',()=>{
 const [,,g,,until,trace,,path=new Map(),options={}]=args
 if((clock()>=until||pastWall())){trace.push({stage:'source-budget-exhausted'});return undefined}
 const cached=options.memo?.get(g,path,until)
 if(cached&&(options.deferCheck||check(g,cached,path))){trace.push({stage:'source-memo',scope:'field'});return cached}
 const tree=fieldBoundLemmasImpl(...args)
 if(tree)options.memo?.put(g,path,tree)
 return tree
})
function fieldBoundLemmasImpl(m:Machine,ds:CountDecl[],g:Goal,cert:Proposal,until:number,trace:object[],onModel?:(goal:Goal,witness:Record<string,number>)=>boolean,root:Path=new Map(),options:{splitRows?:boolean,deferCheck?:boolean,fieldClaim?:C,memo?:SourceProofMemo,onSourceModel?:(goal:Goal,witness:Record<string,number>,path:Path)=>void}={}):Tree|undefined{
 const pointOptions={deferCheck:!!options.deferCheck}
 const seq=modelSequence(root),ctx:C[]=[],path:Path=new Map(root),lemmas:{split:Record<string,number>,no:Tree}[]=[]
 const accept=(tree:Tree|undefined,path:Path)=>tree&&(options.deferCheck||check(g,tree,path))?tree:undefined
 const verdict=(tree:Tree|undefined)=>({checked:!options.deferCheck&&!!tree,...(options.deferCheck?{proposed:!!tree,deferred:true}:{})})
 const rowPlan=options.splitRows!==false?rowPairs(m,cert,root,options.fieldClaim).slice(0,2):[]
 let arithmetic:Tree|undefined
 const postMaps=new Set(cert.reads.filter(r=>r[1].endsWith('#')).map(r=>r[1])),postIds=new Set(cert.reads.filter(r=>r[1].endsWith('#')).map(r=>r[0]))
 // Split a packed field's guarded column domain once, outside the row cases.
 // Without it each row repeats the same range reconstruction for copied keys.
 if(rowPlan.length&&!postIds.size&&options.fieldClaim){
  const rows=new Set(rowPlan.flatMap(([key])=>key.op==='var'?[key.name]:[])),columns=new Set<string>()
  walkOnce(options.fieldClaim,(o:any)=>{if(o.op==='get'&&o.key.op!=='var')walkOnce(o.key,(k:any)=>{if(k.op==='var'&&!rows.has(k.name)&&!m.inputs.includes(k.name)&&!m.params.includes(k.name))columns.add(k.name)})})
  const candidates:Extract<C,{a:unknown}>[]=[]
  walkOnce(options.fieldClaim,(c:any)=>{if(!candidates.length&&c.op==='<'&&c.a.op==='var'&&columns.has(c.a.name)&&truth(c,root)===undefined)candidates.push(c)})
  let domain=candidates[0]
  if(domain&&domain.a.op==='var'){
   const column=domain.a.name,strides:number[]=[]
   walkOnce(options.fieldClaim,(o:any)=>{if(o.op!=='get')return;const key=linear(o.key,root);if(!key||key[column]!==1)return;for(const row of rows){const width=Math.abs(key[row]??0);if(Number.isInteger(width)&&width>1)strides.push(width)}})
   if(strides.length)domain={op:'<',a:domain.a,b:n(Math.min(...strides))}
  }
  if(domain&&truth(domain,root)===undefined){
   const a=linear(domain.a,root),b=linear(domain.b,root)
   if(a&&b){
    const split=sub(a,b);split['1']=(split['1']??0)+1
    const id=canon(split),negative=new Map(root).set(id,{lin:split,holds:false}),positive=new Map(root).set(id,{lin:split,holds:true})
    const no=fieldCase(m,g,cert,options.fieldClaim,negative,Math.min(until,clock()+50),e=>trace.push(e),0,options.memo)
    if(no){
     const yes=fieldBoundLemmas(m,ds,g,cert,until,trace,onModel,positive,options),tree=yes?{split,yes,no}:undefined
     trace.push({stage:'field-column-domain',domain,proposed:!!tree})
     return tree&&(options.deferCheck||check(g,tree,root))?tree:undefined
    }
   }
  }
 }
 if(rowPlan.length&&!postIds.size){
  trace.push({stage:'field-row-pairs',pairs:rowPlan})
  return proveRowCases(g,root,rowPlan,until,(branch,end)=>{
   const cached=options.memo?.get(g,branch,end);if(cached){trace.push({stage:'source-memo',scope:'field-row'});return cached}
   const tree=fieldCase(m,g,cert,options.fieldClaim,branch,end,e=>trace.push(e),0,options.memo)??fieldBoundLemmas(m,ds,g,cert,end,trace,onModel,branch,{...options,splitRows:false,deferCheck:true})
   if(tree)options.memo?.put(g,branch,tree)
   return tree
  },e=>trace.push(e),{deferToCaller:!!options.deferCheck,splitEqual:copiesRows(m,root)})
 }
 const base=g.hyps.slice(0,g.hyps.length-cert.insts.length).flatMap(c=>piecesAt(c,root)).filter(c=>{let post=false;walkLive(c,root,(o:any)=>{if(o.op==='get'&&postMaps.has(o.map)||o.op==='var'&&postIds.has(o.name))post=true});return !post})
 const cs=new Map((countsForReads(ds,cert.reads)??[]).map(c=>[c.v,{...c,body:substE(c.body,{vars:{[c.key]:x('$member')},maps:{},flags:{}})}]))
 const view=(e:any):any=>{
  if(e.op!=='if'||e.then.op!=='const'||e.then.value!==1||e.else.op!=='const'||e.else.value!==0)return e
  const c=e.c
  if(c.op==='='&&c.a.op==='get'&&c.b.op==='const'&&c.b.value===1)return c.a
  if(c.op==='='&&c.b.op==='get'&&c.a.op==='const'&&c.a.value===1)return c.b
  if(c.op==='<='&&c.a.op==='const'&&c.a.value===1&&c.b.op==='get')return c.b
  if(c.op==='<'&&c.a.op==='const'&&c.a.value===0&&c.b.op==='get')return c.b
  return e
 }
 const signature=(e:any):string|undefined=>{
  const pred=e.op==='get'?{op:'=',a:e,b:{op:'const',value:1}}:e.op==='if'&&e.then.op==='const'&&e.then.value===1&&e.else.op==='const'&&e.else.value===0?e.c:undefined
  const atoms=(c:any):string[]=>c.op==='and'?c.xs.flatMap(atoms):[JSON.stringify(c)]
  return pred?JSON.stringify([...new Set(atoms(pred))].sort()):undefined
 }
 const narrow=(good:Extract<C,{a:unknown}>)=>{
  const keep=cert.insts.flatMap((inst,i)=>{
   if(inst.unit!==0||inst.terms.length!==2||inst.terms.some(t=>postIds.has(t[1])))return []
   const positive=inst.terms.find(t=>t[0]===1),negative=inst.terms.find(t=>t[0]===-1),a=positive&&cs.get(positive[1]),b=negative&&cs.get(negative[1])
   if(!a||!b)return []
   const as=signature(a.body),bs=signature(b.body),same=as!==undefined&&as===bs,input=(view(a.body) as any).op==='get'&&(m.inputMaps??[]).includes((view(a.body) as any).map)
   let target=false;walkOnce(b.body,(o:any)=>{if(o.op==='<'&&JSON.stringify(o.b)===JSON.stringify(good.a.op==='if'?good.a.then:good.a))target=true})
   return same||input&&target?[i]:[]
  })
  const wanted=new Set(keep.map(i=>cert.insts[i]!.wit)),all=new Set(cert.insts.map(i=>i.wit))
  const weaken=(c:C):C|undefined=>{
   if(c.op==='and'){const xs=c.xs.flatMap(c=>{const n=weaken(c);return n?[n]:[]});return xs.length?{op:'and',xs}:undefined}
   let other=false,own=false;walkLive(c,root,(o:any)=>{if(o.op==='var'&&all.has(o.name)){if(wanted.has(o.name))own=true;else other=true}})
   return other&&!own?undefined:c
  }
  return [...base.flatMap(c=>{const n=weaken(c);return n?[n]:[]}),...keep.map(i=>g.hyps[g.hyps.length-cert.insts.length+i]!)]
 }
 const solve=(goal:Goal,limit:number,finish=false):Tree|undefined=>{
  const budget=limit,started=clock(),q=seq(goal,Math.min(until,clock()+budget))
  trace.push({stage:'field-query',hyps:goal.hyps.length,ms:Math.round(clock()-started),limit:budget,outcome:'tree'in q?'tree':q.stuck,core:q.core?.length,...(!('tree'in q)&&q.stuck==='sat'?{model:q.witness}:{})})
  if('tree'in q)return q.tree
  if(q.stuck==='sat'&&q.witness)options.onSourceModel?.(goal,q.witness,root)
  if(finish&&q.stuck==='sat'&&q.witness&&onModel?.(goal,q.witness))return undefined
  const reduced=q.why===REFUTED&&q.core?.length?{...goal,hyps:q.core.map(i=>goal.hyps[i]!)}:finish?goal:undefined
  if(!reduced)return undefined
  const before=atPoint.on;atPoint.on=!(root.size>0&&!finish&&q.core&&q.core.length<=8)
  try{
   const deadline=Math.min(until,clock()+(finish?Math.max(0,until-clock()):250))
   if(!finish&&root.size>0&&q.core&&q.core.length<=8){
    const start=clock(),folded=foldPath(reduced,root),out=grow(folded.goal,root,{nodes:0,until:Math.min(deadline,clock()+25),units:false})
    const lifted='tree'in out?withDeadline(deadline,()=>widen(folded.goal,reduced,out.tree,folded.opaque,root,root)):undefined
    trace.push({stage:'folded-core',aliases:Object.keys(folded.opaque).length,ms:Math.round(clock()-start),sourceChecked:'tree'in out,lifted:!!lifted})
    if(lifted)return withDeadline(deadline,()=>widen(reduced,goal,lifted,{},root,root))
    const direct=booleanCore(reduced,root,new Set(cert.insts.map(i=>i.wit)),deadline,trace,pointOptions)
    if(direct)return withDeadline(deadline,()=>widen(reduced,goal,direct,{},root,root))
    const contextual=sourceWitnessContext(goal,reduced,new Set(cert.insts.map(i=>i.wit)),root)
    if(contextual!==reduced&&clock()<deadline){
     const extra=contextual.hyps.slice(reduced.hyps.length)
     trace.push({stage:'witness-context',added:extra.length,extra:extra.flatMap(c=>piecesAt(c,root))})
     const expanded=booleanCore(contextual,root,new Set(cert.insts.map(i=>i.wit)),deadline,trace,pointOptions)
     if(expanded)return withDeadline(deadline,()=>widen(contextual,goal,expanded,{},root,root))
    }
   }
   const split=!finish&&root.size>0&&q.core&&q.core.length<=8?carriedCase(reduced,root,m.inputMaps??[],new Set(cert.insts.map(i=>i.wit)),deadline,trace):undefined
   if(split)return withDeadline(deadline,()=>widen(reduced,goal,split,{},root,root))
   const out=grow(reduced,root,{nodes:0,until:deadline,units:root.size>0&&!!q.core&&q.core.length<=8})
   return 'tree'in out?withDeadline(deadline,()=>widen(reduced,goal,out.tree,{},root,root)):undefined
  }finally{atPoint.on=before}
 }
 for(let i=0;i<cert.reads.length;i++)for(let j=i+1;j<cert.reads.length;j++){
  const a=cert.reads[i]!,b=cert.reads[j]!
  if(a[1]!==b[1]||truth({op:'=',a:a[2],b:b[2]},root)!==true)continue
  for(const [left,right]of [[a[0],b[0]],[b[0],a[0]]]){
   if((clock()>=until||pastWall()))break
   const split=sub({[left!]:1},{[right!]:1});if(path.get(canon(split))?.holds===true)continue
   const noPath=new Map(path).set(canon(split),{lin:split,holds:false}),begun=clock()
   trace.push({stage:'read-alias-start',left,right})
   const bindings=g.hyps.filter(c=>c.op==='='&&[[c.a,c.b],[c.b,c.a]].some(([v,e])=>v?.op==='var'&&[left,right].includes(v.name)&&e?.op==='get'&&e.map===a[1]))
   if(bindings.length!==2)continue
   const small:Goal={name:'equal-key count reads',hyps:bindings},out=refuteFast(rowsAt(small,noPath),256)
   const local:Tree|undefined=out?.kind==='refuted'?{leaf:out.steps}:undefined
   const no=local&&check(small,local,noPath)?liftCountProxies(small,g,local,[],noPath,noPath,undefined,options):undefined,accepted=!!no&&(options.deferCheck||check(g,no,noPath))
   trace.push({stage:'read-alias',left,right,ms:Math.round(clock()-begun),checked:!options.deferCheck&&accepted,...(options.deferCheck?{proposed:accepted,deferred:true}:{})})
   if(accepted&&no){lemmas.push({split,no});ctx.push({op:'<=',a:x(left!),b:x(right!)});path.set(canon(split),{lin:split,holds:true})}
  }
 }
 if((clock()>=until||pastWall()))return undefined
 const ceilings=fieldBounds(m,ds,cert,{claim:options.fieldClaim,path:root}),domains:C[]=[]
 for(const good of ceilings)if(good.op==='<='&&good.a.op==='if'){
  const parts=good.a.c.op==='and'?good.a.c.xs:[good.a.c]
  for(const c of parts)if(c.op==='<'&&!domains.some(d=>JSON.stringify(c)===JSON.stringify(d)))domains.push(c)
 }
 for(const domain of domains){
  if(truth(domain,path)!==undefined||(clock()>=until||pastWall()))continue
  if(domain.op!=='<')continue
  const a=linear(domain.a,root),b=linear(domain.b,root);if(!a||!b)continue
  const split=sub(a,b);split['1']=(split['1']??0)+1
  const noPath=new Map(path).set(canon(split),{lin:split,holds:false}),start=clock()
  const part={...g,hyps:[...g.hyps.slice(0,g.hyps.length-cert.insts.length),...ctx,{op:'not' as const,x:domain}]},direct=refuteFast(rowsAt(part,root),256)
  const proof:Tree|undefined=direct?.kind==='refuted'?{leaf:direct.steps}:solve(part,50)
  const lifted=proof&&widen(part,g,proof,{},root,noPath),no=accept(lifted,noPath)
  trace.push({stage:'field-domain',domain,direct:direct?.kind==='refuted',ms:Math.round(clock()-start),...verdict(no)})
  if(no){lemmas.push({split,no});ctx.push(domain);path.set(canon(split),{lin:split,holds:true})}
 }
 const finishField=():Tree|undefined=>{
  if(postIds.size||!options.fieldClaim||!lemmas.length||(clock()>=until||pastWall()))return undefined
  const offset=g.hyps.length-cert.insts.length,part={...g,hyps:[...g.hyps.slice(0,offset),...ctx,...g.hyps.slice(offset)]}
  const field=fieldCase(m,part,cert,options.fieldClaim,path,Math.min(until,clock()+150),e=>trace.push(e))
  let tree=field&&widen(part,g,field,{},path,path)
  trace.push({stage:'field-ceiling-conclusion',facts:lemmas.length,proposed:!!tree})
  if(tree){
   for(const {split,no} of [...lemmas].reverse())tree={split,yes:tree,no}
   if(options.deferCheck||check(g,tree,root))return tree
  }
  return undefined
 }
 const activeCeilings=new Set(ceilings.flatMap(good=>good.op==='<='&&good.a.op==='if'&&truth(good.a.c,path)===true?[JSON.stringify([good.a.then,good.b])]:[]))
 for(const good of ceilings){
  if(good.op==='<='&&good.a.op==='if'&&truth(good.a.c,path)!==true&&activeCeilings.has(JSON.stringify([good.a.then,good.b])))continue
  if(good.op!=='<='||(clock()>=until||pastWall()))break
  if(truth(good,path)===true)continue
  const a=linear(good.a,path),b=linear(good.b,path);if(!a||!b)continue
  const split=sub(a,b),noPath=new Map(path).set(canon(split),{lin:split,holds:false}),start=clock()
  const facts=narrow(good),part={...g,hyps:[...facts,...ctx,{op:'not' as const,x:good}]},proof=solve(part,250),lifted=proof&&widen(part,g,proof,{},root,noPath),no=accept(lifted,noPath)
  trace.push({stage:'field-bound',bound:good,ms:Math.round(clock()-start),proved:!!no,...verdict(no)})
  if(no){
   lemmas.push({split,no});ctx.push(good);path.set(canon(split),{lin:split,holds:true})
   const field=finishField();if(field)return field
  }
 }
 if((clock()>=until||pastWall()))return undefined
 const field=finishField();if(field)return field
 {
  const carriedMaps=activeCarried(m,root),countMaps=new Set(cert.reads.map(r=>r[1])),countIds=new Set(cert.reads.map(r=>r[0])),wits=new Set(cert.insts.map(i=>i.wit)),raw=g.hyps.slice(0,g.hyps.length-cert.insts.length)
  const pieces=(c:C)=>piecesAt(c,root)
  const alias=(inst:Proposal['insts'][number]):boolean=>{if(inst.unit!==0||inst.terms.length!==2||inst.terms.some(([,id])=>postIds.has(id)))return false;const a=cs.get(inst.terms[0]![1]),b=cs.get(inst.terms[1]![1]);return !!a&&!!b&&JSON.stringify(view(a.body))===JSON.stringify(view(b.body))}
  const requestFrame=(inst:Proposal['insts'][number]):boolean=>inst.terms.length===2&&inst.terms.some(([,id])=>postIds.has(id))&&inst.terms.some(([,id])=>{const c=cs.get(id),b=c&&view(c.body);return b?.op==='get'&&(m.inputMaps??[]).includes(b.map)})
  const frame=(inst:Proposal['insts'][number]):boolean=>{
   if(inst.terms.length!==2)return false
   const [a,b]=inst.terms.map(([,id])=>cert.reads.find(r=>r[0]===id))
   return !!a&&!!b&&a[1].replace(/#$/,'')===b[1].replace(/#$/,'')&&a[1].endsWith('#')!==b[1].endsWith('#')&&JSON.stringify(a[2])===JSON.stringify(b[2])
  }
  const copyFrame=(inst:Proposal['insts'][number]):boolean=>{
   if(inst.terms.length!==2)return false
   const [a,b]=inst.terms.map(([,id])=>cert.reads.find(r=>r[0]===id))
   return !!a&&!!b&&a[1].replace(/#$/,'')===b[1].replace(/#$/,'')&&a[1].endsWith('#')!==b[1].endsWith('#')&&JSON.stringify(a[2])!==JSON.stringify(b[2])
  }
  const selected=(inst:Proposal['insts'][number]):boolean=>{
   if(inst.unit!==0)return false
   if(emptyCountCandidate(m,cert,inst))return true
   if(rowPlan.length&&inst.terms.some(([,id])=>postIds.has(id)))return false
   const carried=inst.terms.some(([k,id])=>{const c=cs.get(id),b=c&&view(c.body);return k===1&&b?.op==='get'&&carriedMaps.has(b.map)})
   // Let row cases prove row-dependent carried bounds where their equalities
   // are known. The complete pool remains available in every row child.
   if(rowPlan.length&&carried&&inst.terms.length===2){
    const localRows=new Set(rowPlan.flatMap(([key])=>key.op==='var'?[key.name]:[])),positive=inst.terms.find(([k])=>k===1),negative=inst.terms.find(([k])=>k===-1)
    const source=positive&&cs.get(positive[1]),target=negative&&cs.get(negative[1]),input=source&&view(source.body)
    let local=false
    if(target)walkLive(target.body,root,(o:any)=>{if(o.op==='var'&&localRows.has(o.name)||o.op==='get'&&(m.inputMaps??[]).includes(o.map)&&input?.op==='get'&&o.map!==input.map)local=true})
    if(local)return false
   }
   if(inst.terms.length===3||inst.terms.length===5&&carried)return true
   if(inst.terms.length!==2)return false
   const [a,b]=inst.terms.map(([,id])=>cert.reads.find(r=>r[0]===id))
   return carried||alias(inst)||frame(inst)||copyFrame(inst)||!!a&&!!b&&a[1].endsWith('#')&&b[1].endsWith('#')||requestFrame(inst)||!!a&&!!b&&a[1].endsWith('#')&&!b[1].endsWith('#')
  }
  const pure=(c:C):boolean=>{let skip=false;walkLive(c,root,(o:any)=>{if(o.op==='get'||o.op==='var'&&wits.has(o.name))skip=true});return !skip}
  const maps=Object.fromEntries([...countMaps].map(map=>[map,(key:any)=>{const r=cert.reads.find(r=>r[1]===map&&JSON.stringify(r[2])===JSON.stringify(key));return r?x(r[0]):{op:'get' as const,map,key}}]))
  const flags=Object.fromEntries(Object.keys(m.step.flags??{}).map(name=>[name,{op:'flag' as const,name}]))
  const numericBase=raw.map(c=>substC(c,{vars:{},maps,flags})).flatMap(c=>pieces(c)).filter(pure)
  // The source path can mention count cells inside a guard or natural
  // subtraction. Keep their explicit bindings instead of disconnecting it
  // from the rewritten numeric hypotheses. Source transport checks every
  // required equality and its read-domain guard.
  const numericBindings=countBindingsAt(cert.reads,root)
  const finish=()=>{
   // The outer row pass adds only pre-state cuts. Defer arithmetic closure to
   // the exhaustive row children, where post-state constraints are available.
   if(rowPlan.length||arithmetic||(clock()>=until||pastWall()))return
   const numeric:Goal={...g,hyps:[...numericBase,...numericBindings,...ctx.filter(pure)]},begun=clock(),q=seq(numeric,Math.min(until,clock()+200))
   trace.push({stage:'count-arithmetic',hyps:numeric.hyps.length,ms:Math.round(clock()-begun),outcome:'tree'in q?'tree':q.stuck,core:q.core?.length,...(!('tree'in q)&&q.stuck==='sat'?{model:q.witness}:{})})
   let proof='tree'in q?q.tree:undefined
   if(!proof&&!('tree'in q)&&q.why===REFUTED&&q.core?.length){
    const reduced={...numeric,hyps:q.core.map(i=>numeric.hyps[i]!)},out=grow(reduced,root,{nodes:0,until:Math.min(until,clock()+400),units:false})
    if('tree'in out)proof=widen(reduced,numeric,out.tree,{},root,root)
   }
   if(!proof&&!('tree'in q)&&q.stuck==='unknown')proof=proveNaturalCases(numeric,root,Math.min(until,clock()+400),trace,pointOptions)
   const lifted=proof&&liftCountProxies(numeric,g,proof,cert.reads,root,path,event=>trace.push({stage:'count-transport',...event}),options)
   if(lifted)arithmetic=lifted // Checked here, or deferred to the composing caller.
  }
  const diagonalCopy=(inst:Proposal['insts'][number]):boolean=>{
   if(!copyFrame(inst))return false
   const source=inst.terms.map(([,id])=>cert.reads.find(r=>r[0]===id)).find(r=>r&&!r[1].endsWith('#')),key=source?.[2]
   if(key?.op==='tup')return JSON.stringify(key.a)===JSON.stringify(key.b)
   const decl=source&&m.counts?.[source[1]]
   return key?.op==='add'&&!!decl?.lo&&key.a.op==='mul'&&key.a.k===decl.base&&JSON.stringify(key.a.a)===JSON.stringify(key.b)
  }
  const writer=activeWriteRow(m,root)
  const afterRead=(inst:Proposal['insts'][number])=>inst.terms.map(([,id])=>cert.reads.find(r=>r[0]===id)).find(r=>r?.[1].endsWith('#'))
  const coordinates=(read:CountCert['reads'][number])=>{
   const key=read[2],d=m.counts?.[read[1].replace(/#$/,'')]
   if(key.op==='tup')return [key.a,key.b]
   if(d?.lo&&key.op==='add'&&key.a.op==='mul'&&key.a.k===d.base)return [key.a.a,key.b]
   return [key]
  }
  const rank=(inst:Proposal['insts'][number]):number=>{
   if(emptyCountCandidate(m,cert,inst))return -1
   const after=afterRead(inst),keys=after&&coordinates(after)
   if(writer&&frame(inst)&&keys?.every(key=>truth(same(key,x(writer)),root)===false))return -0.75
   if(copyFrame(inst)){
    if(writer&&keys){
     const before=inst.terms.map(([,id])=>cert.reads.find(r=>r[0]===id)).find(r=>r&&!r[1].endsWith('#')),oldKeys=before&&coordinates(before)
     let moved=false,matched=!!oldKeys&&oldKeys.length===keys.length
     for(let i=0;matched&&i<keys.length;i++){
      const changed=truth(same(keys[i]!,x(writer)),root),old=oldKeys![i]!
      if(changed===false&&truth(same(old,keys[i]!),root)!==true)return 0.5
      if(changed===true){moved=true;matched=old.op==='var'&&m.inputs.includes(old.name)&&old.name!==writer}
      if(changed===undefined)matched=false
     }
     if(matched&&moved)return -0.5
    }
    return diagonalCopy(inst)?0.5:0
   }
   return requestFrame(inst)||alias(inst)?0:inst.terms.length===2&&inst.terms.every(([,id])=>postIds.has(id))?1:frame(inst)?2:inst.terms.length===3&&inst.terms.every(([,id])=>!postIds.has(id))?3:inst.terms.length===5?4:inst.terms.length===2?5:6
  }
  finish()
  const ordered=[...cert.insts.entries()].sort((a,b)=>rank(a[1])-rank(b[1])),excluded=new Set<number>(),confirmed=new Set<number>()
  const boundOf=(index:number):C|undefined=>{const h=g.hyps[raw.length+index];return h?.op==='or'&&h.xs[0]?.op==='<='?h.xs[0]:undefined}
  let fallbackSelection=false
  const pick=():typeof ordered=>{
   const pool=ordered.filter(([index,inst])=>{const good=boundOf(index);return !excluded.has(index)&&!confirmed.has(index)&&selected(inst)&&!!good&&truth(good,path)!==true})
   // A count-sensitive guard can need shared pre-state support before its
   // row children have a closing projection. Retain that ranked fallback;
   // count-free row skeletons need no eager pre-state lemma chain.
   if(rowPlan.length){fallbackSelection=true;return numericBindings.length?pool:[]}
   const selection=selectCountBounds({...g,hyps:[...numericBase,...numericBindings,...ctx.filter(pure)]},pool.map(([index])=>({index,bound:boundOf(index)!})),until,{path:root,queryMs:200,trace:event=>trace.push({...event,stage:'needed-lemmas'})})
   if(!selection)return []
   fallbackSelection=selection.fallback
   const needed=new Set(selection.indices)
   // Selected row-independent identities are cheap prerequisites for harder
   // copy bounds. Derive them first; the selection's rank order is unchanged.
   const identity=(inst:Proposal['insts'][number])=>inst.terms.length===3&&inst.terms.every(([,id])=>!postIds.has(id))
   return pool.filter(([index])=>needed.has(index)).sort((a,b)=>Number(identity(b[1]))-Number(identity(a[1])))
  }
  let queue=pick(),cursor=0
  while(cursor<queue.length){
   const [index,inst]=queue[cursor++]!
   if(arithmetic||(clock()>=until||pastWall()))break
   if(!selected(inst))continue
   const h=g.hyps[raw.length+index];if(h?.op!=='or'||h.xs[0]?.op!=='<=')continue
   const good=h.xs[0];if(truth(good,path)===true)continue
   const split=Object.fromEntries(inst.terms.map(([n,v])=>[v,n])),noPath=new Map(path).set(canon(split),{lin:split,holds:false})
   const relevant=raw.flatMap(c=>pieces(c)).filter(c=>{let skip=false;walkLive(c,root,(o:any)=>{if(o.op==='get'&&countMaps.has(o.map)||o.op==='var'&&(countIds.has(o.name)||wits.has(o.name)&&o.name!==inst.wit))skip=true});return !skip})
   const part={...g,hyps:[...relevant,...ctx,h,{op:'not' as const,x:good}]},started=clock()
   let proof:Tree|undefined
   if(inst.terms.length===3&&inst.terms.every(([,id])=>!postIds.has(id))){
    const tiny={name:g.name,hyps:[h,{op:'not' as const,x:good}]},fast=booleanCore(tiny,root,new Set([inst.wit]),Math.min(until,clock()+30),trace,pointOptions)
    if(fast)proof=widen(tiny,part,fast,{},root,root)
    trace.push({stage:'direct-partition',index,proved:!!proof})
   }
   const directCopy=(copyFrame(inst)||frame(inst))
   if(directCopy){
    // The matching diagonal gets the existing row window; reserve time for
    // arithmetic closure instead of spending it on unrelated copy pairs.
    const copyUntil=diagonalCopy(inst)?Math.max(clock(),until-200):Math.min(until,started+230)
    const tiny=sourceScalarContext({name:g.name,hyps:raw},{name:g.name,hyps:[h,{op:'not' as const,x:good}]},new Set([...m.params,...m.inputs,...Object.keys(m.state)]),root),fast=booleanCore(tiny,root,new Set([inst.wit]),copyUntil,trace,{...pointOptions,model:false,extended:true,scalarGuards:true})
    if(fast)proof=widen(tiny,part,fast,{},root,root)
    trace.push({stage:'direct-copy',index,terms:inst.terms,reads:inst.terms.map(([,id])=>cert.reads.find(r=>r[0]===id)),proved:!!proof})
   }
   // Reallocate the existing 80 + 150 ms copy window, rather than extend it.
   proof??=solve(part,directCopy?Math.max(0,230-(clock()-started)):150)
   const lifted=proof&&withDeadline(Math.min(until,started+(directCopy?230:150)),()=>widen(part,g,proof,{},root,noPath)),no=accept(lifted,noPath)
   trace.push({stage:'count-lemma',index,arity:inst.terms.length,terms:inst.terms,ms:Math.round(clock()-started),...verdict(no)})
   if(no){confirmed.add(index);lemmas.push({split,no});ctx.push(good);path.set(canon(split),{lin:split,holds:true});finish()}
   else{
    excluded.add(index)
    // An unknown oracle already supplied the full ranked fallback. Remove
    // the failed proposal from that queue rather than repeat the same query.
    if(!fallbackSelection){queue=pick();cursor=0}
   }
  }
  finish()
 }
 if((clock()>=until||pastWall()))return undefined
 const part={...g,hyps:[...g.hyps,...ctx]},start=clock()
 let tree=arithmetic
 if(!tree&&rowPlan.length){
  trace.push({stage:'row-pairs',pairs:rowPlan})
  tree=proveRowCases(g,path,rowPlan,until,(branch,end)=>fieldBoundLemmas(m,ds,g,cert,end,trace,onModel,branch,{splitRows:false,deferCheck:true,memo:options.memo,onSourceModel:options.onSourceModel}),e=>trace.push(e),{deferToCaller:true,splitEqual:copiesRows(m,root)})
 }
 if(!tree){const proof=solve(part,Math.max(150,until-clock()-200),true);tree=proof&&widen(part,g,proof,{},root,path)}
 trace.push({stage:'field-bound-conclusion',facts:lemmas.length,ms:Math.round(clock()-start),proved:!!tree})
 if(!tree)return undefined
 for(const {split,no} of [...lemmas].reverse())tree={split,yes:tree,no}
 // The composing caller must check deferred cuts and children in its full tree.
 if(options.deferCheck)return tree
 const checked=check(g,tree,root)
 return checked?tree:undefined
}
