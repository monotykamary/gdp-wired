// Finite-input cases: first try no count instances, then the focused certificate.
// Temporary case hypotheses are widened back to real proof-tree paths; checkMC
// checks the combined tree against the original, unspecialized goal.
import {readFileSync} from 'node:fs'
import {type C,type E,walkOnce,x} from '../../core/machine.ts'
import {type Goal,type Instances,type Path,type Tree,canon,check,checkMC,countedObligations,foldPinned,linear,mcGoal,plainOf,substC} from '../../kernel/kernel.ts'
import {atPoint,clock,counted,eprScope,fullRate,fullWork,grow,modelInstances,widen,withDeadline,withWall} from '../../kernel/prove.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {mldrHandSet} from '../protocols/ic3syn/mldr2-probe.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {sub} from '../../core/solver.ts'
import {patternsOf} from '../../kernel/epr.ts'
import {certFor} from '../../core/counts.ts'
import {appendCountCert} from '../../core/count-cert-grow.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {frameLemmas} from './frame-lemmas.ts'
import {modelCountPicks} from './model-count-picks.ts'
import {fieldBoundLemmas} from './field-bound-lemmas.ts'
import {guardCases} from './guard-cases.ts'
import {actionGuard} from './action-guard.ts'
import {countLawSeeds,countRowBridges,independentCountInstances,fieldLawBridges,focusCountCert,copyCountSubset,rowKeyNames} from '../../core/count-focused.ts'
import {seedCountWitnessFlags} from '../../core/count-witness-flags.ts'
const mark=(stage:string)=>{if(process.env.LAB_PROGRESS==='1')console.log(`${stage} ${Math.round(performance.now())}`)}
mark('entry-loaded')
const [file,input]=process.argv.slice(2),d=JSON.parse(readFileSync(file!,'utf8')),{m}=JSON.parse(readFileSync(input!,'utf8'))
mark('input-loaded')
const laws=process.env.LAB_SYMBOLIC_OVERLAP==='1'?d.laws.map((l:any)=>l.name.startsWith('Inv2973')?mldrHandSet('star','uw').laws.find(q=>q.name===l.name)!:l):d.laws,index=laws.findIndex((l:any)=>l.name===d.law),law=laws[index]
mark('laws-ready')
let at:Instances={}
for(const [name,values] of Object.entries(d.at) as [string,E[]][]){const n=1+(laws.find((l:any)=>l.name===name)?.keys?.length??0),keep:E[]=[];for(let i=0;i<values.length;i+=n){const tuple=values.slice(i,i+n);if(!/"name":"w(?:\$\d+|\?)/.test(JSON.stringify(tuple)))keep.push(...tuple)}at[name]=keep}
if(process.env.LAB_FOCUS_COLD==='1')at={}
const names=[law.forall,...law.keys??[]],own:E[]=[x(`${law.forall}#`),...(law.keys??[]).map(x)],scalar=rowKeyNames(m,law)
let countedTarget=false;walkOnce(law.holds,(o:any)=>{if(o.op==='get'&&m.counts[o.map])countedTarget=true})
const thinFields=countedTarget&&process.env.LAB_THIN_FIELD_CONTEXT==='1',wideFields=new Set<string>()
if(thinFields)for(const l of laws){
 let count=false;walkOnce(l.holds,(o:any)=>{if(o.op==='get'&&m.counts[o.map])count=true})
 if(!count&&(l.keys?.length??0)>0)wideFields.add(l.name)
}
const sourceLaws=thinFields?laws.filter((l:any)=>!wideFields.has(l.name)):laws
if(thinFields)at=Object.fromEntries(Object.entries(at).filter(([name])=>!wideFields.has(name)))
const rows=own.filter((_,i)=>scalar.has(names[i])),request:E[]=m.inputs.filter((name:string)=>Object.values(m.counts??{}).some((c:any)=>![c.j,c.lo,c.key].includes(name)&&JSON.stringify([c.below,c.body]).includes(`"name":${JSON.stringify(name)}`))).map(x)
mark('seeding-instances')
at=countLawSeeds(m,laws,at,rows.length?rows:own,request,!countedTarget,{requestDiagonals:process.env.LAB_REQUEST_DIAGONALS==='1'});at=fieldLawBridges(m,sourceLaws,at,rows.length?rows:own,request,own.length===3?own[2]:undefined);at[law.name]=[...at[law.name]??[],...own];at=countRowBridges(m,law,at,own,request)
// Diagnostic only: the design also permits Ov_uw. Its numeric keys can be
// instantiated by the actual excess-over-outside counts, not guessed halves.
if(process.env.LAB_SYMBOLIC_OVERLAP==='1'){
 const ov=laws.find((l:any)=>l.name.startsWith('Inv2973')),a=x(`${law.forall}#`),b=x('i'),j=x('j$'),pk=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:64,a},b}),read=(map:string,key:E):E=>({op:'get',map,key})
 const excess=(count:E,outside:E):E=>({op:'sub',a:count,b:outside})
 at[ov.name]=[a,b,excess(read('bq#',pk(a,j)),read('xm',pk(a,b))),excess(read('inS',{op:'const',value:0}),read('xm',pk(b,a)))]
}
mark('building-obligations')
let base=countedObligations(m,laws,{[law.name]:at},index).find(g=>g.goal.name.endsWith('@step'))!
const focusOptions={carried:process.env.LAB_ALL_CARRIED==='1'?undefined:m.inputMaps[0],targets:!countedTarget&&process.env.LAB_TARGET_COUNTS==='1'?rows:undefined,algebraic:process.env.LAB_ALGEBRAIC==='1',requestFrames:process.env.LAB_REQUEST_FRAMES==='1',copyFrames:process.env.LAB_COPY_FRAMES==='1',structural:countedTarget&&process.env.LAB_STRUCT_COUNTS==='1',frames:process.env.LAB_FRAME_COUNTS==='1'}
mark('building-certificate')
const proposed=focusCountCert(m,base.decls,certFor(base.goal,base.decls,true,1000),focusOptions)
const cert={...(process.env.LAB_COMPACT_COPY==='1'?copyCountSubset(m,proposed):proposed),picks:[] as [string,E[]][]}
mark('certificate-ready')
if(process.env.LAB_SKIP_COVERS==='1')cert.insts=cert.insts.filter(i=>i.terms.length!==3)
if(process.env.LAB_KEEP_INSTS!==undefined){
 const keep=process.env.LAB_KEEP_INSTS.split(',').map(Number)
 if(keep.some(i=>!Number.isInteger(i)||i<0||i>=cert.insts.length))throw new Error('Invalid LAB_KEEP_INSTS index')
 cert.insts=cert.insts.filter((_,i)=>keep.includes(i))
}
if(process.env.LAB_COMPACT_PROPOSALS==='1'){console.log(JSON.stringify({reads:cert.reads,insts:cert.insts}));process.exit(0)}
if(process.env.LAB_DESCRIBE_ONLY==='1'){
 const pool=certFor(base.goal,base.decls,true,1000)
 const ids=process.env.LAB_BODY_IDS?.split(',')
 console.log(JSON.stringify({reads:cert.reads,selected:cert.insts,pool:pool.insts.filter(i=>i.terms.length>=3),...(ids?{bodies:countsForReads(base.decls,cert.reads)?.filter(c=>ids.includes(c.v))}:{})}))
 process.exit(0)
}
mark('seeding-witness-flags')
at=seedCountWitnessFlags(m,at,[{decls:base.decls,cert}],true)
base=countedObligations(m,laws,{[law.name]:at},index).find(g=>g.goal.name.endsWith('@step'))!
mark('building-counted-goal')
let goal:Goal={...mcGoal(base.goal.hyps,base.decls,cert)!,name:base.goal.name},plain=goal.hyps.slice(0,goal.hyps.length-cert.insts.length)
mark('counted-goal-ready')
const order=(hyps:C[]):C[]=>{if(process.env.LAB_CONCLUSION_LAST!=='1')return hyps;const i=hyps.indexOf(base.goal.hyps.at(-1)!);return i<0?hyps:[...hyps.slice(0,i),...hyps.slice(i+1),hyps[i]!] }
const fieldLaws=sourceLaws.filter((l:any)=>{let count=false;walkOnce(l.holds,(o:any)=>{if(o.op==='get'&&m.counts[o.map])count=true});return !count})
const initialAt=at,allAt:Instances={...at},packetCache=new Map<string,{base:typeof base,goal:Goal,plain:C[]}>()
packetCache.set(JSON.stringify(at),{base,goal,plain})
const rebuild=()=>{
 const key=JSON.stringify(at),had=packetCache.get(key)
 if(had){base=had.base;goal=had.goal;plain=had.plain;return}
 base=countedObligations(m,laws,{[law.name]:at},index).find(g=>g.goal.name.endsWith('@step'))!
 if(process.env.LAB_GROW_CERT==='1'){
  const known=new Set(cert.reads.map(r=>JSON.stringify(r.slice(1))));let missing=false
  walkOnce(base.goal.hyps,(o:any)=>{if(o.op==='get'&&base.decls.some(d=>d.map===o.map)&&!known.has(JSON.stringify([o.map,o.key])))missing=true})
  if(missing){
   const next=focusCountCert(m,base.decls,certFor(base.goal,base.decls,true,1000),{...focusOptions,algebraic:focusOptions.algebraic||process.env.LAB_GROW_ALGEBRAIC==='1'})
   const added=next.reads.filter(r=>!known.has(JSON.stringify(r.slice(1))))
   if(!focusOptions.algebraic&&process.env.LAB_GROW_ALGEBRAIC==='1'){const ids=new Set(added.map(r=>r[0]));next.insts=next.insts.filter(i=>i.terms.length<3||i.terms.some(t=>ids.has(t[1])))}
   for(const c of countsForReads(base.decls,added)??[])next.insts.push({wit:'newCount$'+next.insts.length,below:c.below,terms:[[1,c.v]],unit:0})
   if(appendCountCert(cert,next,base.goal.hyps)){
    packetCache.clear();at=seedCountWitnessFlags(m,at,[{decls:base.decls,cert}],true)
    base=countedObligations(m,laws,{[law.name]:at},index).find(g=>g.goal.name.endsWith('@step'))!
   }
  }
 }
 goal={...mcGoal(base.goal.hyps,base.decls,cert)!,name:base.goal.name};plain=goal.hyps.slice(0,goal.hyps.length-cert.insts.length)
 packetCache.set(key,{base,goal,plain})
}
const refinePicks=(w:Record<string,number>):boolean=>{
 if(process.env.LAB_MODEL_PICKS!=='1')return false
 const seen=new Set(cert.picks.map(p=>JSON.stringify(p))),next=modelCountPicks(m,base.decls,cert,w).filter(p=>!seen.has(JSON.stringify(p)))
 if(!next.length)return false
 cert.picks.push(...next);packetCache.clear();trace.push({stage:'model-picks',picks:next});return true
}
const values=new Map<string,Set<number>>()
walkOnce([m.step,m.assume],(o:any)=>{if(o.op!=='=')return;const [a,b]=o.a.op==='var'?[o.a,o.b]:[o.b,o.a];if(a.op==='var'&&b.op==='const'&&m.inputs.includes(a.name)){const v=values.get(a.name)??new Set<number>();v.add(b.value);values.set(a.name,v)}})
const choice=[...values].filter(([,v])=>v.size>2).sort((a,b)=>b[1].size-a[1].size)[0]
if(!choice)throw new Error('No finite-choice scalar')
const [name,vs]=choice,cuts=[...vs].sort((a,b)=>a-b).filter(v=>v>=Number(process.env.LAB_FIRST_CUT??-Infinity)),path:Path=new Map(),conditions:C[]=[],records:({goal:Goal,tree:Tree,path:Path,from?:Path}|undefined)[]=[],trace:object[]=[],cores:object[]=[]
if(process.env.LAB_PROGRESS==='1'){console.log('replay-ready');const push=trace.push.bind(trace);trace.push=(...events:object[])=>{for(const event of events){const e=event as any;console.log(JSON.stringify({stage:e.stage,index:e.index,left:e.left,right:e.right,key:e.key,cached:e.cached,pairs:e.pairs,nodes:e.nodes,leaves:e.leaves,steps:e.steps,depth:e.depth,unique:e.unique,hyps:e.hyps,facts:e.facts,cuts:e.cuts,ms:e.ms,checked:e.checked,proposed:e.proposed,proved:e.proved,wall:Math.round(performance.now())}))}return push(...events)}}
const splitAt=(value:number):Record<string,number>=>value?{[name]:1,'1':-value}:{[name]:1}
const branches:{prefix:C[],path:Path}[]=[],branchRoots:Path[]=[],tailCuts:number[][]=[]
const seq=modelSequence(), refine=process.env.LAB_CASE_REFINE==='1'
const proofPath=():Path=>process.env.LAB_SEARCH_PATH==='1'?new Map(path):new Map()
atPoint.on=process.env.LAB_AT_POINT==='1'
if(process.env.LAB_EPR==='1')eprScope.patterns=patternsOf(plainOf(m),laws)
const aliasCore=(g:Goal,splits:Record<string,number>[],path:Path,until:number):Tree|undefined=>{
 if(clock()>=until)return undefined
 const [split,...rest]=splits
 if(!split){const out=grow(g,path,{nodes:0,until,units:process.env.LAB_NO_UNITS==='1'?false:undefined});return 'tree'in out?out.tree:undefined}
 const id=canon(split),yes=aliasCore(g,rest,new Map(path).set(id,{lin:split,holds:true}),until)
 if(!yes)return undefined
 const no=aliasCore(g,rest,new Map(path).set(id,{lin:split,holds:false}),until)
 return no?{split,yes,no}:undefined
}

const fieldCore=(c:C):C=>{
 if(c.op!=='and')return c
 return {...c,xs:c.xs.flatMap(child=>{
  if(child.op==='and')return [fieldCore(child)]
  let counted=false;walkOnce(child,(o:any)=>{if(o.op==='get'&&m.counts[o.map.replace(/#$/,'')])counted=true})
  return counted?[]:[child]
 })}
}

const growCore=(original:Goal,until:number):{tree:Tree}|{stuck:string,why?:string}=>{
  const g=process.env.LAB_FIELD_CORE==='1'?{...original,hyps:original.hyps.map((c,i)=>i===original.hyps.length-1?c:fieldCore(c))}:original
  const before=atPoint.on
  if(process.env.LAB_CORE_POINT==='1')atPoint.on=true
  try{
    if(process.env.LAB_ALIAS==='1'&&!countedTarget&&own.length===3&&request[0]?.op==='var'){
      const req=request[0].name,splits=rows.slice(0,2).flatMap(r=>r.op==='var'?[{[r.name]:1,[req]:-1},{[r.name]:-1,[req]:1}]:[])
      const tree=aliasCore(g,splits,new Map(),until)
      return tree?{tree}:{stuck:'unknown',why:'alias cases'}
    }
    const out=grow(g,proofPath(),{nodes:0,until,units:process.env.LAB_NO_UNITS==='1'?false:undefined})
    if('tree'in out&&g!==original){const tree=widen(g,original,out.tree,{},proofPath(),proofPath());return tree?{...out,tree}:{stuck:'unknown',why:'field-core rebase'}}
    return out
  }finally{atPoint.on=before}
}
const activation=process.env.LAB_ASSUMED_ACTIVE==='1'?substC(m.step.flags.leads,{vars:{},maps:{},flags:{canVote:{op:'=',a:x('?canVote'),b:{op:'const',value:1}}}}):undefined
const start=performance.now(),w=fullWork()
const result=withWall(start+Math.min(60000,Number(process.env.LAB_WALL_MS??10000)),()=>counted(fullRate,()=>{
 const end=clock()+5000
 return withDeadline(end,()=>{
 for(const [i,value] of [...cuts,undefined].entries()){
  const split=value===undefined?undefined:splitAt(value),cut:C|undefined=value===undefined?undefined:{op:'<=',a:x(name),b:{op:'const',value}}
  if(split)path.set(canon(split),{lin:split,holds:true})
  const basePath=new Map(path),tails=process.env.LAB_SATURATE==='1'&&value!==undefined?cuts.filter(v=>v>value):[]
  branchRoots.push(basePath);tailCuts.push(tails)
  for(const v of tails){const lin=splitAt(v);path.set(canon(lin),{lin,holds:true})}
  const restore=()=>{for(const v of tails)path.delete(canon(splitAt(v)))}
  const t=clock(),prefix=[...conditions,...activation?[activation]:[],...cut?[cut]:[],...tails.map(v=>({op:'<=' as const,a:x(name),b:{op:'const' as const,value:v}}))];let tree:Tree|undefined,proofGoal:Goal|undefined,proofFrom:Path|undefined
  branches.push({prefix,path:new Map(path)})
  if(process.env.LAB_LOCAL_MODELS==='1'){at=initialAt;rebuild()}
  if(process.env.LAB_CASE!==undefined&&String(value)!==process.env.LAB_CASE){records.push(undefined);restore();if(split){path.set(canon(split),{lin:split,holds:false});conditions.push({op:'not',x:cut!})}continue}
  if(process.env.LAB_PIN_CASE==='1'&&value!==undefined&&(i===0?value===0:cuts[i-1]===value-1)){
   const part={name:goal.name,hyps:order([...prefix,...goal.hyps])}
   try{
    const pinned={...part,hyps:part.hyps.map(c=>foldPinned(c,[[name,value]]))},started=clock()
    const pinEnd=process.env.LAB_CASE===undefined?Math.min(end,clock()+Math.max(600,(end-clock())/(cuts.length+1-i))):end
    const factored=process.env.LAB_PIN_FRAMES==='1'?frameLemmas(pinned,cert,pinEnd,trace):undefined
    const out=factored?{tree:factored}:grow(pinned,new Map(),{nodes:0,until:pinEnd,units:false})
    if('tree'in out)tree=widen(pinned,goal,out.tree,{},new Map(),path)
    trace.push({value,stage:'pinned',outcome:'tree'in out?'tree':out.stuck,rebased:!!tree,ms:Math.round(clock()-started)})
   }catch(error){trace.push({value,stage:'pinned',error:String(error)})}
  }
  if(!tree&&process.env.LAB_GUARD_CASES==='1'){
   const part={name:goal.name,hyps:order([...prefix,...goal.hyps])},pins:[string,number][]=value===undefined?[]:[[name,value]]
   const rooted=process.env.LAB_GUARD_PATH==='1',pinned={...part,hyps:part.hyps.map(c=>foldPinned(c,pins))},guard=foldPinned(actionGuard(m,name,value)??{op:'=',a:{op:'const',value:1},b:{op:'const',value:0}},rooted?[]:pins),begun=clock()
   const root=rooted?new Map(path):new Map(),row=process.env.LAB_ROW_CASE
   if(row){
    const a=`${law.forall}#`,b=law.keys?.[0],actor='i',eq=(key:string)=>{const l={[key]:1,[actor]:-1},r={[actor]:1,[key]:-1};root.set(canon(l),{lin:l,holds:true});root.set(canon(r),{lin:r,holds:true})},gt=(key:string)=>{const l={'1':1,[actor]:1,[key]:-1};root.set(canon(l),{lin:l,holds:true})}
    if(row==='equal')eq(a)
    else{gt(a);if(b){if(row==='new-term')eq(b);else gt(b)}}
    if(process.env.LAB_ACTIVE_ROW==='1'){
     const hold=(c:C):void=>{
      if(c.op==='and'){c.xs.forEach(hold);return}
      if(c.op==='='){hold({op:'<=',a:c.a,b:c.b});hold({op:'<=',a:c.b,b:c.a});return}
      if(c.op!=='<'&&c.op!=='<=')throw new Error('nonlinear diagnostic guard')
      const a=linear(c.a,root),b=linear(c.b,root);if(!a||!b)throw new Error('guard is not linearizable')
      const lin=sub(a,b);if(c.op==='<')lin['1']=(lin['1']??0)+1
      root.set(canon(lin),{lin,holds:true})
     }
     hold(guard)
    }
   }
   const deferred=!process.env.LAB_ROW_CASE,found=guardCases(m,base.decls,rooted?goal:pinned,cert,guard,end,trace,rooted?0:conditions.length,root,{deferCheck:deferred})
   if(found){tree=rooted?found:widen(pinned,goal,found,{},new Map(),path);proofGoal=goal}
   trace.push({value,stage:'guard-result',ms:Math.round(clock()-begun),sourceChecked:!deferred&&!!found,proposed:!!found,proved:!!tree})
   if(process.env.LAB_ROW_CASE)return {complete:false,branches:[],groundChecked:false,checked:false,diagnosticRow:process.env.LAB_ROW_CASE,diagnosticChecked:!!found}
  }
  if(!tree&&process.env.LAB_FIELD_BOUNDS==='1'){
   const part={name:goal.name,hyps:order([...prefix,...goal.hyps])},pinned=process.env.LAB_BOUND_PIN==='1'&&value!==undefined?{...part,hyps:part.hyps.map(c=>foldPinned(c,[[name,value]]))}:part,start=clock(),found=fieldBoundLemmas(m,base.decls,pinned,cert,end,trace,process.env.LAB_BOUND_MODELS==='1'?(part,witness)=>{
    const support=laws.filter((l:any)=>!fieldLaws.includes(l)&&l.name!==law.name),preferred=modelInstances(m,support,at,part,witness,8)
    if(preferred)for(const l of support){
     const had=at[l.name]??[],xs=preferred[l.name]??had,n=1+(l.keys?.length??0),tuples:E[][]=[]
     for(let start=had.length;start<xs.length;start+=n)tuples.push(xs.slice(start,start+n))
     const names=[l.forall,...l.keys??[]],rows=rowKeyNames(m,l),positions=names.flatMap((name:any,i:number)=>rows.has(name)?[i]:[])
     const chosen=tuples.find(t=>positions.length>1&&positions.some(i=>JSON.stringify(t[i])!==JSON.stringify(t[positions[0]!])))??tuples[0]
     if(chosen)preferred[l.name]=[...had,...chosen]
    }
    const proposed=preferred??modelInstances(m,laws,at,part,witness,8),next=proposed&&independentCountInstances(m,laws,at,proposed,cert.insts.map(i=>i.wit))
    trace.push({stage:'field-bound-model',added:next?Object.fromEntries(Object.entries(next).flatMap(([name,terms])=>terms.length>(at[name]?.length??0)?[[name,terms.slice(at[name]?.length??0)]]:[])):null,model:witness})
    if(next){at=next;rebuild()}return true
   }:undefined)
   trace.push({value,stage:'field-bound-source',conditional:!!activation,checked:!!found,ms:Math.round(clock()-start)})
   if(found&&activation)return {complete:false,branches:[],groundChecked:false,checked:false,conditionalChecked:true,conditionalMs:Math.round(clock()-t)}
   if(found){tree=widen(pinned,goal,found,{},new Map(),path);proofGoal=goal}
   trace.push({value,stage:'field-bound-result',ms:Math.round(clock()-start),proved:!!tree})
  }
  if(!tree&&process.env.LAB_FRAME_LEMMAS==='1'){
   const part={name:goal.name,hyps:order([...prefix,...goal.hyps])},out=frameLemmas(part,cert,process.env.LAB_CASE===undefined?Math.min(end,clock()+Math.max(600,(end-clock())/(cuts.length+1-i))):end,trace)
   if(out){tree=out;proofGoal=part;proofFrom=new Map()}
  }
  if(!tree&&process.env.LAB_PLAIN_FIRST==='1'){
   const part={name:goal.name,hyps:order([...prefix,...plain])},started=clock(),q=seq(part,Math.min(end,clock()+Number(process.env.LAB_DECIDE_MS??200)))
   trace.push({value:value??'rest',stage:'plain-decision',outcome:'tree'in q?'tree':q.stuck,why:'tree'in q?undefined:q.why,core:q.core?.length,ms:Math.round(clock()-started)})
   if(!('tree'in q)&&q.why===REFUTED&&q.core?.length&&q.core.length<=Number(process.env.LAB_CORE_LIMIT??Infinity)){
    const reduced={name:goal.name,hyps:order(q.core.map(i=>part.hyps[i]!))},out=growCore(reduced,Math.min(end,clock()+600))
    if('tree'in out){if(process.env.LAB_DEFER_REBASE==='1'){tree=out.tree;proofGoal=reduced;proofFrom=proofPath()}else tree=widen(reduced,goal,out.tree,{},proofPath(),path)}
   }
  }
  if(!tree&&refine)for(let round=0;round<6&&clock()<end;round++){
   const part={name:goal.name,hyps:order([...prefix,...goal.hyps])},pinnedQuery=process.env.LAB_PIN_QUERY==='1'&&value!==undefined&&(i===0?value===0:cuts[i-1]===value-1),query=pinnedQuery?{...part,hyps:part.hyps.map(c=>foldPinned(c,[[name,value!]]))}:part,started=clock(),q=seq(query,Math.min(end,clock()+Number(process.env.LAB_DECIDE_MS??200)))
   trace.push({value:value??'rest',stage:'decision',outcome:'tree'in q?'tree':q.stuck,why:'tree'in q?undefined:q.why,core:q.core?.length,ms:Math.round(clock()-started)})
   if(!('tree'in q)&&q.why===REFUTED&&q.core?.length&&q.core.length<=Number(process.env.LAB_CORE_LIMIT??Infinity)){
    const reduced={name:goal.name,hyps:order(q.core.map(i=>query.hyps[i]!))},t=clock()
    if(process.env.LAB_DUMP_CORE==='1')cores.push({value,goal:reduced})
    const out=growCore(reduced,Math.min(end,clock()+Math.max(600,(end-clock())/(cuts.length+1-i))))
    trace.push({value:value??'rest',stage:'core',hyps:reduced.hyps.length,outcome:'tree'in out?'tree':out.stuck,ms:Math.round(clock()-t)})
    if('tree'in out){if(process.env.LAB_DEFER_REBASE==='1'){tree=out.tree;proofGoal=reduced;proofFrom=proofPath()}else tree=widen(reduced,goal,out.tree,{},proofPath(),path)}
   }
   if(tree||'tree'in q||q.stuck!=='sat'||!q.witness)break
   if(refinePicks(q.witness)){rebuild();continue}
   const modelLaws=(process.env.LAB_ALL_MODELS==='1'?laws:fieldLaws).filter((l:any)=>process.env.LAB_NO_ROW_MODELS!=='1'||!fieldLaws.includes(l)||(l.keys?.length??0)<2)
   const proposed=modelInstances(m,modelLaws,at,query,pinnedQuery?{...q.witness,[name]:value!}:q.witness,8)
   const added=proposed&&independentCountInstances(m,laws,at,proposed,cert.insts.map(i=>i.wit))
   trace.push({value:value??'rest',stage:'model',round,query:q.stuck,added:added?Object.fromEntries(Object.entries(added).flatMap(([n,terms])=>terms.length>(at[n]?.length??0)?[[n,terms.slice(at[n]?.length??0)]]:[])):null})
   if(!added){if(process.env.LAB_DUMP_MODEL==='1')trace.push({value,stage:'missing-model',model:q.witness,instances:at,cert});break}
   at=added;rebuild()
  }
  if(!tree)for(const [stage,hyps] of (refine?[['counts',goal.hyps]]:[['plain',plain],['counts',goal.hyps]]) as [string,C[]][]){
   if(clock()>=end)break
   const part:Goal={name:goal.name,hyps:order([...prefix,...hyps])},until=stage==='plain'?Math.min(end,clock()+Number(process.env.LAB_DECIDE_MS??200)):Math.min(end,clock()+Math.max(600,(end-clock())/(cuts.length+1-i)))
   const out=grow(part,proofPath(),{nodes:0,until,units:process.env.LAB_NO_UNITS==='1'?false:undefined})
   trace.push({value:value??'rest',stage,hyps:hyps.length,ms:Math.round(clock()-t),outcome:'tree'in out?'tree':out.stuck})
   if('tree'in out){if(process.env.LAB_DEFER_REBASE==='1'){tree=out.tree;proofGoal=part;proofFrom=proofPath()}else tree=widen(part,goal,out.tree,{},proofPath(),path);if(tree)break}
   if(!('tree'in out)&&out.stuck==='sat'&&out.witness&&process.env.LAB_ALL_MODELS==='1'){
    if(refinePicks(out.witness)){rebuild();continue}
    const proposed=modelInstances(m,laws,at,part,out.witness,8)
    const next=proposed&&independentCountInstances(m,laws,at,proposed,cert.insts.map(i=>i.wit))
    trace.push({value:value??'rest',stage:'grow-model',added:next?Object.fromEntries(Object.entries(next).flatMap(([n,terms])=>terms.length>(at[n]?.length??0)?[[n,terms.slice(at[n]?.length??0)]]:[])):null})
    if(next){
     at=next;rebuild()
     const retry={name:goal.name,hyps:order([...prefix,...goal.hyps])},again=grow(retry,proofPath(),{nodes:0,until:Math.min(end,clock()+Math.max(300,(end-clock())/(cuts.length+1-i))),units:process.env.LAB_NO_UNITS==='1'?false:undefined})
     trace.push({value:value??'rest',stage:'grow-refined',outcome:'tree'in again?'tree':again.stuck})
     if('tree'in again){if(process.env.LAB_DEFER_REBASE==='1'){tree=again.tree;proofGoal=retry;proofFrom=proofPath()}else tree=widen(retry,goal,again.tree,{},proofPath(),path)}
    }
   }
  }
  records.push(tree?{goal:proofGoal??goal,tree,path:new Map(path),...(proofFrom?{from:proofFrom}:{})}:undefined)
  if(process.env.LAB_LOCAL_MODELS==='1')for(const [name,terms] of Object.entries(at))allAt[name]=[...allAt[name]??[],...terms.slice(initialAt[name]?.length??0)]
  restore()
  if(split){path.set(canon(split),{lin:split,holds:false});conditions.push({op:'not',x:cut!})}
 }
 if(process.env.LAB_LOCAL_MODELS==='1'){at=allAt;rebuild()}
 // Spend the remaining shared budget on unresolved cases, not on solved ones.
 const missing=records.flatMap((r,i)=>r||process.env.LAB_CASE!==undefined&&String(cuts[i])!==process.env.LAB_CASE?[]:[i])
 for(const [j,i] of missing.entries()){
  if(clock()>=end)break
  if(process.env.LAB_CASE!==undefined&&String(cuts[i])!==process.env.LAB_CASE)continue
  const {prefix,path:casePath}=branches[i]!,sourcePath=process.env.LAB_SEARCH_PATH==='1'?casePath:new Map(),caseEnd=Math.min(end,clock()+(end-clock())/(missing.length-j))
  for(let round=0;round<6&&clock()<caseEnd;round++){
   const part={name:goal.name,hyps:order([...prefix,...goal.hyps])},t=clock(),out=grow(part,sourcePath,{nodes:0,until:caseEnd,units:process.env.LAB_NO_UNITS==='1'?false:undefined})
   const tree='tree'in out?widen(part,goal,out.tree,{},sourcePath,casePath):undefined
   trace.push({value:cuts[i]??'rest',stage:'retry',round,ms:Math.round(clock()-t),outcome:'tree'in out?'tree':out.stuck})
   if(tree){records[i]={goal,tree,path:casePath};break}
   if('tree'in out||out.stuck!=='sat'||!out.witness)break
   if(refinePicks(out.witness)){rebuild();continue}
   const modelLaws=(process.env.LAB_ALL_MODELS==='1'?laws:fieldLaws).filter((l:any)=>process.env.LAB_NO_ROW_MODELS!=='1'||!fieldLaws.includes(l)||(l.keys?.length??0)<2)
   const proposed=modelInstances(m,modelLaws,at,part,out.witness,8),next=proposed&&independentCountInstances(m,laws,at,proposed,cert.insts.map(i=>i.wit))
   trace.push({value:cuts[i]??'rest',stage:'retry-model',round,added:next?Object.fromEntries(Object.entries(next).flatMap(([n,terms])=>terms.length>(at[n]?.length??0)?[[n,terms.slice(at[n]?.length??0)]]:[])):null})
   if(process.env.LAB_DUMP_MODEL==='1')trace.push({value:cuts[i],stage:'missing-model',model:out.witness,instances:at,cert})
   if(!next)break
   at=next;rebuild()
  }
 }
 const trees=records.map((r,i)=>{
  let t=r&&(r.goal===goal&&!r.from?r.tree:widen(r.goal,goal,r.tree,{},r.from??r.path,r.path))
  if(!t)return undefined
  const root=branchRoots[i]!,tails=tailCuts[i]!
  for(let j=tails.length-1;j>=0;j--){
   const before=new Map(root)
   for(const v of tails.slice(0,j)){const lin=splitAt(v);before.set(canon(lin),{lin,holds:true})}
   const upper=[...before.keys()].indexOf(canon(splitAt(cuts[i]!))),bad=before.size
   if(upper<0)return undefined
   t={split:splitAt(tails[j]!),yes:t,no:{leaf:[{kind:'input',index:upper},{kind:'input',index:bad},{kind:'combine',a:0,b:1,ma:1,mb:1}]}}
  }
  return t
 })
 let tree=trees.at(-1)
 for(let i=cuts.length-1;i>=0;i--)tree=tree&&trees[i]?{split:splitAt(cuts[i]!),yes:trees[i]!,no:tree}:undefined
 const checked=!!tree&&checkMC(base.goal.hyps,base.decls,{...cert,tree})
 // A complete MC check includes the same ground-tree check. Partial diagnostic
 // runs instead check each available branch against its exact original scope.
 return {complete:!!tree,branches:tree?trees.map(()=>checked):trees.map((t,i)=>!!t&&check(goal,t,branchRoots[i]!)),groundChecked:checked,checked}
 })
},true))
console.log(JSON.stringify({file,law:law.name,context:thinFields?'thin-field':'full',diagnosticAssumptions:[...activation?['existing leader activation; no unrestricted proof unless rebase checks']:[],...process.env.LAB_ROW_CASE?['row-case assumptions; not an unrestricted proof']:[],...process.env.LAB_ACTIVE_ROW?['active action guard assumed for row diagnostic']:[]],...result,counted:Math.round((fullWork()-w)/fullRate),wall:Math.round(performance.now()-start),insts:cert.insts.length,trace,...(cores.length?{cores}:{})}))
