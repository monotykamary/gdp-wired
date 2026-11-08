// Untrusted finite-input case search for a fixed counted certificate. A small
// model/core query chooses ordinary instances; every combined tree is checked
// against the unspecialized counted obligation before it is returned.
import {type C,type Law,type Machine,walkOnce,x} from './machine.ts'
import {type CountCert,type CountDecl,type Goal,type Instances,type Path,type Tree,boundOf,canon,check,checkMC,linear,mcGoal,truth} from '../kernel/kernel.ts'
import {atPoint,clock,grow,modelInstances,usedHyps,widen,withDeadline} from '../kernel/prove.ts'
import {sub} from './solver.ts'
import {seedCountWitnessFlags} from './count-witness-flags.ts'
import {modelSequence} from '../kernel/model-sequence.ts'
import {REFUTED} from '../kernel/cdcl.ts'

type Packet={goal:Goal,decls:CountDecl[]}
export function finiteCountChoice(m:Machine):[string,Set<number>]|undefined{
 const values=new Map<string,Set<number>>()
 walkOnce([m.step,m.assume],(o:any)=>{
  if(o.op!=='=')return
  const [a,b]=o.a.op==='var'?[o.a,o.b]:[o.b,o.a]
  if(a.op!=='var'||b.op!=='const'||!m.inputs.includes(a.name))return
  const vs=values.get(a.name)??new Set<number>();vs.add(b.value);values.set(a.name,vs)
 })
 return [...values].filter(([,v])=>v.size>2&&v.size<=16).sort((a,b)=>b[1].size-a[1].size)[0]
}

export type CountBoundCandidate={index:number,bound:C}
export type CountBoundSelection={indices:number[],assumed:number,fallback:boolean}
// The arithmetic oracle chooses proposals, never facts. In rank order, add
// candidate bounds until its refutation core names the ones worth deriving.
export function selectCountBounds(base:Goal,candidates:CountBoundCandidate[],until:number,options:{path?:Path,queryMs?:number,trace?:(event:Record<string,unknown>)=>void}={}):CountBoundSelection|undefined{
 const path=options.path??new Map(),ask=modelSequence(path),started=clock()
 for(let n=candidates.length?1:0;n<=candidates.length&&clock()<until;n++){
  const goal={...base,hyps:[...base.hyps,...candidates.slice(0,n).map(c=>c.bound)]},q=ask(goal,Math.min(until,clock()+(options.queryMs??200)))
  const used='tree'in q?usedHyps(goal,q.tree,path):q.why===REFUTED&&q.core?new Set(q.core):undefined
  if(used){
   const indices=candidates.slice(0,n).filter((_,i)=>used.has(base.hyps.length+i)).map(c=>c.index)
   options.trace?.({stage:'count-core-select',pool:candidates.length,assumed:n,indices,ms:Math.round(clock()-started)})
   return {indices,assumed:n,fallback:false}
  }
  if('tree'in q||q.stuck!=='sat')break
 }
 if(clock()>=until)return undefined
 const indices=candidates.map(c=>c.index)
 options.trace?.({stage:'count-core-select',pool:candidates.length,indices,fallback:true,ms:Math.round(clock()-started)})
 return {indices,assumed:indices.length,fallback:true}
}
// Remove whole tuples mentioning count witnesses no longer in the packet.
// This only weakens the available source context; its proof is checked again.
export function withoutCountWitnesses(m:Machine,laws:Law[],at:Instances,discard:ReadonlySet<string>):Instances{
 if(!discard.size)return at
 const out:Instances={}
 for(const [name,terms]of Object.entries(at)){
  const law=laws.find(l=>l.name===name),flag=name.startsWith('?')?m.step.flags?.[name.slice(1)]:undefined
  const arity=law?1+(law.keys?.length??0):flag?.op==='all'?boundOf(flag).length:1,kept:typeof terms=[]
  for(let i=0;i<terms.length;i+=arity){
   const tuple=terms.slice(i,i+arity);let unwanted=false
   walkOnce(tuple,(o:any)=>{if(o.op==='var'&&discard.has(o.name))unwanted=true})
   if(!unwanted)kept.push(...tuple)
  }
  out[name]=kept
 }
 return out
}
function selectedCase(m:Machine,laws:Law[],at:Instances,cert:Pick<CountCert,'reads'|'insts'>,packet:Packet,path:Path,until:number,build:(at:Instances)=>Packet,options:CountCaseOptions):{goal:Goal,tree:Tree,indices:number[]}|undefined{
 const full=mcGoal(packet.goal.hyps,packet.decls,cert)
 if(!full||!cert.insts.length)return undefined
 const offset=full.hyps.length-cert.insts.length,base={...full,hyps:full.hyps.slice(0,offset)},excluded=new Set<number>()
 const candidates=cert.insts.flatMap((_,index)=>{const h=full.hyps[offset+index];return h?.op==='or'&&h.xs[0]?.op==='<='?[{index,bound:h.xs[0]}]:[]})
 while(clock()<until){
  const selected=selectCountBounds(base,candidates.filter(c=>!excluded.has(c.index)),until,{path,queryMs:options.queryMs,trace:options.trace})
  if(!selected||selected.fallback)return undefined
  const chosen=new Set(selected.indices),insts=cert.insts.filter((_,i)=>chosen.has(i)),slim={...cert,insts}
  const discard=new Set(cert.insts.filter((_,i)=>!chosen.has(i)).map(c=>c.wit)),clean=withoutCountWitnesses(m,laws,at,discard)
  const instances=seedCountWitnessFlags(m,clean,[{decls:packet.decls,cert:slim}],true),source=build(instances),goal=mcGoal(source.goal.hyps,source.decls,slim)
  if(!goal)return undefined
  let confirmed=new Map(path),failed:number|undefined
  const cuts:{split:Record<string,number>,no:Tree}[]=[]
  for(const index of selected.indices){
   const bound=candidates.find(c=>c.index===index)!.bound
   if(truth(bound,confirmed)===true)continue
   if(bound.op!=='<='){failed=index;break}
   const a=linear(bound.a,confirmed),b=linear(bound.b,confirmed)
   if(!a||!b){failed=index;break}
   const split=sub(a,b),id=canon(split),noPath=new Map(confirmed).set(id,{lin:split,holds:false})
   const proof=grow(goal,noPath,{nodes:0,until:Math.min(until,clock()+(options.queryMs??200)),units:options.units})
   if(!('tree'in proof)){failed=index;break}
   cuts.push({split,no:proof.tree});confirmed=new Map(confirmed).set(id,{lin:split,holds:true})
  }
  if(failed!==undefined){
   excluded.add(failed);options.trace?.({stage:'count-core-excluded',index:failed,excluded:[...excluded]})
   continue
  }
  const closed=grow(goal,confirmed,{nodes:0,until,units:options.units})
  if(!('tree'in closed))return undefined
  let tree=closed.tree
  for(const cut of cuts.reverse())tree={split:cut.split,yes:tree,no:cut.no}
  if(!check(goal,tree,path))return undefined
  options.trace?.({stage:'count-case-certificate',before:cert.insts.length,after:insts.length,indices:selected.indices,hyps:goal.hyps.length})
  return {goal,tree,indices:selected.indices}
 }
 return undefined
}
export type CountCaseOptions={localModels?:boolean,saturate?:boolean,queryMs?:number,coreLimit?:number,units?:boolean,corePointOnly?:boolean,trace?:(event:Record<string,unknown>)=>void}
export function proveCountCases(m:Machine,laws:Law[],at:Instances,cert:Pick<CountCert,'reads'|'insts'>,until:number,build:(at:Instances)=>Packet,options:CountCaseOptions={}):{instances:Instances,cert:CountCert}|undefined {
 return withDeadline(until,()=>{
  const choice=finiteCountChoice(m)
  if(!choice||clock()>=until)return undefined
  const [name,vs]=choice,cuts=[...vs].sort((a,b)=>a-b),path:Path=new Map(),conditions:C[]=[]
  const splitAt=(v:number):Record<string,number>=>v?{[name]:1,'1':-v}:{[name]:1}
  let activeCert=cert,packet=build(at),root=mcGoal(packet.goal.hyps,packet.decls,activeCert)
  if(!root)return undefined
  let goal:Goal={...root,name:packet.goal.name}
  const rebuild=()=>{packet=build(at);root=mcGoal(packet.goal.hyps,packet.decls,activeCert);if(root)goal={...root,name:packet.goal.name};return !!root}
  const fields=laws.filter(l=>{let counted=false;walkOnce(l.holds,(o:any)=>{if(o.op==='get'&&m.counts?.[o.map])counted=true});return !counted})
  const seq=modelSequence(),records:({goal:Goal,tree:Tree,path:Path,from?:Path,indices:number[]}|undefined)[]=[],branches:{prefix:C[],path:Path,root:Path,tails:number[]}[]=[]
  const initial=at,merged:Instances={...at},previous=atPoint.on;atPoint.on=!options.corePointOnly
  const coreGrow=(g:Goal,end:number)=>{const before=atPoint.on;atPoint.on=true;try{return grow(g,new Map(),{nodes:0,until:end,units:options.units})}finally{atPoint.on=before}}
  try {
    for(const [i,value] of [...cuts,undefined].entries()){
      if(clock()>=until)return undefined
      const split=value===undefined?undefined:splitAt(value),cut:C|undefined=value===undefined?undefined:{op:'<=',a:x(name),b:{op:'const',value}}
      if(split)path.set(canon(split),{lin:split,holds:true})
      const root=new Map(path),tails=options.saturate&&value!==undefined?cuts.filter(v=>v>value):[]
      for(const v of tails){const lin=splitAt(v);path.set(canon(lin),{lin,holds:true})}
      const prefix:C[]=[...conditions,...cut?[cut]:[],...tails.map(v=>({op:'<=' as const,a:x(name),b:{op:'const' as const,value:v}}))]
      branches.push({prefix,path:new Map(path),root,tails})
      if(options.localModels){at=initial;if(!rebuild())return undefined}
      let tree:Tree|undefined,source:Goal|undefined,from:Path|undefined,indices=cert.insts.map((_,j)=>j)
      const caseEnd=Math.min(until,clock()+Math.max(600,(until-clock())/(cuts.length+1-i)))
      const selected=selectedCase(m,laws,at,cert,packet,path,caseEnd,build,options)
      packet=build(at) // A builder may retain its most recently requested instances.
      if(selected){
       const kept=new Set(selected.indices),slim={...cert,insts:cert.insts.filter((_,j)=>kept.has(j))}
       at=seedCountWitnessFlags(m,at,[{decls:packet.decls,cert:slim}],true)
       tree=selected.tree;source=selected.goal;from=new Map(path);indices=selected.indices
      }
      for(let round=0;!tree&&round<6&&clock()<until;round++){
        const part={name:goal.name,hyps:[...prefix,...goal.hyps]},start=clock(),q=seq(part,Math.min(until,clock()+(options.queryMs??200)))
        options.trace?.({value,stage:'query',round,hyps:part.hyps.length,ms:Math.round(clock()-start),outcome:'tree'in q?'tree':q.stuck,core:q.core?.length})
        if(!('tree'in q)&&q.why===REFUTED&&q.core?.length&&q.core.length<=(options.coreLimit??Infinity)){
          const core={name:goal.name,hyps:q.core.map(j=>part.hyps[j]!)},out=coreGrow(core,Math.min(until,clock()+Math.max(600,(until-clock())/(cuts.length+1-i))))
          options.trace?.({value,stage:'core',hyps:core.hyps.length,outcome:'tree'in out?'tree':out.stuck})
          if('tree'in out){tree=out.tree;source=core}
        }
        if(tree||'tree'in q||q.stuck!=='sat'||!q.witness)break
        const next=modelInstances(m,fields,at,part,q.witness,8)
        if(!next)break
        at=next;if(!rebuild())return undefined
      }
      if(!tree){
        const part={name:goal.name,hyps:[...prefix,...goal.hyps]},out=grow(part,new Map(),{nodes:0,until:Math.min(until,clock()+Math.max(600,(until-clock())/(cuts.length+1-i))),units:options.units})
        options.trace?.({value,stage:'grow',outcome:'tree'in out?'tree':out.stuck})
        if('tree'in out){tree=out.tree;source=part}
      }
      records.push(tree&&source?{goal:source,tree,path:new Map(path),indices,...(from?{from}:{})}:undefined)
      if(options.localModels)for(const [n,terms] of Object.entries(at))merged[n]=[...merged[n]??[],...terms.slice(initial[n]?.length??0)]
      for(const v of tails)path.delete(canon(splitAt(v)))
      if(split){path.set(canon(split),{lin:split,holds:false});conditions.push({op:'not',x:cut!})}
    }
    if(options.localModels){at=merged;if(!rebuild())return undefined}
    const missing=records.flatMap((r,i)=>r?[]:[i])
    for(const [j,i] of missing.entries()){
      if(clock()>=until)break
      const {prefix,path:p}=branches[i]!,part={name:goal.name,hyps:[...prefix,...goal.hyps]}
      const out=grow(part,new Map(),{nodes:0,until:Math.min(until,clock()+(until-clock())/(missing.length-j)),units:options.units})
      if('tree'in out)records[i]={goal:part,tree:out.tree,path:p,indices:cert.insts.map((_,j)=>j)}
    }
    if(records.some(r=>!r))return undefined
    const kept=new Set(records.flatMap(r=>r?.indices??[])),discard=new Set(cert.insts.filter((_,i)=>!kept.has(i)).map(c=>c.wit))
    activeCert={...cert,insts:cert.insts.filter((_,i)=>kept.has(i))}
    at=withoutCountWitnesses(m,laws,at,discard)
    if(!rebuild())return undefined
    options.trace?.({stage:'count-cases-certificate',before:cert.insts.length,after:activeCert.insts.length})
    const trees=records.map((r,i)=>{
      let tree=r&&widen(r.goal,goal,r.tree,{},r.from??new Map(),r.path)
      if(!tree)return undefined
      const {root,tails}=branches[i]!
      for(let j=tails.length-1;j>=0;j--){
        const before=new Map(root)
        for(const v of tails.slice(0,j)){const lin=splitAt(v);before.set(canon(lin),{lin,holds:true})}
        const upper=[...before.keys()].indexOf(canon(splitAt(cuts[i]!))),bad=before.size
        if(upper<0)return undefined
        tree={split:splitAt(tails[j]!),yes:tree,no:{leaf:[{kind:'input',index:upper},{kind:'input',index:bad},{kind:'combine',a:0,b:1,ma:1,mb:1}]}}
      }
      return tree
    })
    let tree=trees.at(-1)
    for(let i=cuts.length-1;i>=0;i--)tree=tree&&trees[i]?{split:splitAt(cuts[i]!),yes:trees[i]!,no:tree}:undefined
    const result=tree&&{...activeCert,tree}
    return result&&checkMC(packet.goal.hyps,packet.decls,result)?{instances:at,cert:result}:undefined
  } finally {atPoint.on=previous}
 })
}
