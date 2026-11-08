// Partial active-source diagnostic, not a complete-law or protocol proof.
import {readFileSync} from 'node:fs'
import {type C,type Law,type Machine,n,plus,same,walkOnce,x} from '../../core/machine.ts'
import {type Instances,type Path,canon,countedObligations,linear,mcGoal,truth} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,modelInstances,usedHyps,withWall} from '../../kernel/prove.ts'
import {certFor} from '../../core/counts.ts'
import {countLawSeeds,countRowBridges,fieldLawBridges,focusCountCert,independentCountInstances,rowKeyNames} from '../../core/count-focused.ts'
import {seedCountWitnessFlags} from '../../core/count-witness-flags.ts'
import {finiteCountChoice,withoutCountWitnesses} from '../../core/count-cases.ts'
import {actionGuard,activeCarried} from '../../core/count-recovery/action-guard.ts'
import {activeWriteKey,activeWriteRow} from '../../core/count-recovery/row-cases.ts'
import {fieldBoundLemmas,fieldBounds} from '../../core/count-recovery/field-bound-lemmas.ts'
import {sourceProofMemo} from '../../core/count-recovery/source-memo.ts'
import {checkConditionalProof as check,hasConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {sourceWitnessInstances} from '../../core/count-recovery/source-witness-instances.ts'
import {sub} from '../../core/solver.ts'
const [file,prefix='Inv2973',valueText='0',carriedArg='first']=process.argv.slice(2),value=Number(valueText)
const {m,laws}=JSON.parse(readFileSync(file!,'utf8')) as {m:Machine,laws:Law[]}
const index=laws.findIndex(l=>l.name.startsWith(prefix)),law=laws[index]!
if(!law)throw new Error('missing law')
const names=[law.forall,...law.keys??[]],own=names.map((name,i)=>x(i?name!:`${name}#`)),scalar=rowKeyNames(m,law)
let targetCounts=false
walkOnce(law.holds,(o:any)=>{if(o.op==='get'){if(o.key.op==='var')scalar.add(o.key.name);if(m.counts?.[o.map])targetCounts=true}})
const rows=own.filter((_,i)=>scalar.has(names[i]!)),request=m.inputs.filter(name=>Object.values(m.counts??{}).some(d=>![d.j,d.lo,d.key].includes(name)&&JSON.stringify([d.below,d.body]).includes(`"name":${JSON.stringify(name)}`))).map(x)
let at:Instances=countLawSeeds(m,laws,{},rows.length?rows:own,request,!targetCounts,{requestDiagonals:true})
at=fieldLawBridges(m,targetCounts?laws.filter(l=>(l.keys?.length??0)===0):laws,at,rows.length?rows:own,request,own.length===3?own[2]:undefined)
if(law.forall)at[law.name]=[...at[law.name]??[],...own]
at=countRowBridges(m,law,at,own,request)
const carried=carriedArg==='all'?undefined:carriedArg==='first'?m.inputMaps?.[0]:carriedArg
const build=()=>{const p=countedObligations(m,laws,{[law.name]:at},index).find(p=>p.goal.name.endsWith('@step'))!;return {...p,cert:focusCountCert(m,p.decls,certFor(p.goal,p.decls,true,1000),{carried,structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,targets:!targetCounts?rows:undefined,...(process.env.LAB_DEMAND_PROPOSALS==='1'?{claim:p.goal.hyps.at(-1)}:{})})}}
let packet=build();at=seedCountWitnessFlags(m,at,[packet],true);packet=build()
if(process.env.LAB_SOURCE_CERT==='1'){console.log(JSON.stringify({reads:packet.cert.reads,insts:packet.cert.insts}));process.exit(0)}
const choice=finiteCountChoice(m);if(!choice)throw new Error('no choice')
const [selector,values]=choice,guard=actionGuard(m,selector,value);if(!guard)throw new Error('no guard')
const root:Path=new Map([...values].sort((a,b)=>a-b).map(v=>{const lin=v?{[selector]:1,'1':-v}:{[selector]:1};return [canon(lin),{lin,holds:v>=value}]}))
const conditions:C[]=[]
const collect=(c:C):void=>{if(c.op==='and'||c.op==='or')c.xs.forEach(collect);else if(c.op==='not')collect(c.x);else if(c.op==='='){conditions.push({op:'<=',a:c.a,b:c.b},{op:'<=',a:c.b,b:c.a})}else if(c.op==='<')conditions.push({op:'<=',a:plus(c.a,n(1)),b:c.b});else if(c.op==='<=')conditions.push(c);else throw new Error('unsupported guard')}
collect(guard)
const paths:Path[]=[]
const visit=(i:number,path:Path):void=>{
 const active=truth(guard,path);if(active!==undefined){if(active)paths.push(path);return}
 if(i>=conditions.length||paths.length>=8)return
 const c=conditions[i]!;if(c.op!=='<=')return
 const known=truth(c,path);if(known!==undefined){visit(i+1,path);return}
 const a=linear(c.a,path),b=linear(c.b,path);if(!a||!b)return
 const lin=sub(a,b),id=canon(lin)
 visit(i+1,new Map(path).set(id,{lin,holds:false}));visit(i+1,new Map(path).set(id,{lin,holds:true}))
}
visit(0,root)
const ceilings=fieldBounds(m,packet.decls,packet.cert,{claim:packet.goal.hyps.at(-1),path:root}),ceilingIndex=process.env.LAB_CEILING_INDEX
if(ceilingIndex!==undefined){
 const ceiling=ceilings[Number(ceilingIndex)];if(!ceiling)throw new Error('missing ceiling candidate')
 const reads=packet.cert.reads.filter(r=>!r[1].endsWith('#')),ids=new Set(reads.map(r=>r[0])),insts=packet.cert.insts.filter(q=>q.terms.every(([,id])=>ids.has(id)))
 const kept=new Set(insts.map(q=>q.wit)),discard=new Set(packet.cert.insts.filter(q=>!kept.has(q.wit)).map(q=>q.wit))
 at=withoutCountWitnesses(m,laws,at,discard)
 const original=countedObligations(m,laws,{[law.name]:at},index).find(p=>p.goal.name.endsWith('@step'))!
 packet={...packet,goal:{...original.goal,hyps:[...original.goal.hyps.slice(0,-1),{op:'not',x:ceiling}]},cert:{reads,insts}}
}
if(process.env.LAB_SOURCE_CORE){
 const prior=JSON.parse(readFileSync(process.env.LAB_SOURCE_CORE,'utf8'))
 if(prior.conditionalChecked!==true||prior.law!==law.name)throw new Error('source core is not a checked conditional result for this law')
 const signature=(q:any)=>JSON.stringify({wit:q.wit,below:q.below,terms:q.terms,unit:q.unit})
 const keep=new Set(prior.usedCounts.map(signature)),selected=packet.cert.insts.filter(q=>keep.has(signature(q)))
 if(selected.length!==keep.size)throw new Error('source core does not match this certificate')
 const pre=new Set(packet.cert.reads.filter(r=>!r[1].endsWith('#')).map(r=>r[0]))
 const insts=process.env.LAB_SOURCE_KEEP_PRE==='1'?packet.cert.insts.filter(q=>keep.has(signature(q))||q.terms.every(([,id])=>pre.has(id))):selected
 packet.cert={...packet.cert,insts}
}
const makeGoal=()=>{const original=mcGoal(packet.goal.hyps,packet.decls,packet.cert)!;return {...original,hyps:[guard,...original.hyps]}}
let goal=makeGoal();const memo=sourceProofMemo(m,law.name)
for(const [branch,path]of paths.entries()){
 if(process.env.LAB_ROW_MODE==='equal'){
  const writer=activeWriteRow(m,path);if(!writer)throw new Error('no written row')
  for(const row of rows){const a=linear(row,path)!,b=linear(x(writer),path)!,lin=sub(a,b),back=sub(b,a);path.set(canon(lin),{lin,holds:true});path.set(canon(back),{lin:back,holds:true})}
 }
 const section7=process.env.LAB_SECTION7_T0==='1'?(await import('./section7-observer.ts')).section7:undefined
 section7?.begin(`${law.name}:${process.env.LAB_ROW_MODE??'active'}`,packet.cert)
 const events:any[]=[],suggestions:object[]=[],captured=new Set<string>(),start=performance.now()
 let tree:ReturnType<typeof fieldBoundLemmas>
 const retries=process.env.LAB_SOURCE_MODEL_RETRY==='1'?Number(process.env.LAB_SOURCE_MODEL_ROUNDS??2):0,sourceAdditions:object[]=[]
 for(let attempt=0;attempt<=retries&&!tree;attempt++){
 const restart={},known=at;let pending:Instances|undefined
 try{tree=withWall(start+60000,()=>counted(fullRate,()=>fieldBoundLemmas(m,packet.decls,goal,packet.cert,clock()+Number(process.env.LAB_SOURCE_MS??3000),events,(source,witness)=>{
  const next=modelInstances(m,laws,at,source,witness,8),valid=next&&independentCountInstances(m,laws,at,next,packet.cert.insts.map(i=>i.wit))
  suggestions.push({hyps:source.hyps.length,added:valid?Object.fromEntries(Object.entries(valid).flatMap(([name,ts])=>ts.length>(at[name]?.length??0)?[[name,ts.slice(at[name]?.length??0)]]:[])):null})
  return true
 },path,{deferCheck:true,conditional:process.env.LAB_CONDITIONAL_PROOF==='1',...(process.env.LAB_ROW_MODE==='equal'?{splitRows:false}:{}),fieldClaim:packet.goal.hyps.at(-1),memo,...(attempt<retries||process.env.LAB_SOURCE_DUMP==='1'?{onSourceModel:(source:any,model:Record<string,number>,sourcePath:Path)=>{
  if(process.env.LAB_SOURCE_DUMP==='1'&&captured.size<8){
   const used=new Set<string>();walkOnce(source.hyps,(o:any)=>{if(o.op==='var')used.add(o.name)})
   const instances=packet.cert.insts.filter(q=>used.has(q.wit)&&(process.env.LAB_SOURCE_DUMP_POST==='1'?q.terms.some(([,id])=>packet.cert.reads.some(r=>r[0]===id&&r[1].endsWith('#'))):q.terms.length>=3)),key=JSON.stringify(source.hyps)
   if(instances.length&&!captured.has(key)){
    captured.add(key);const writer=activeWriteRow(m,sourcePath)
    console.log(JSON.stringify({sourceQuery:true,source,path:[...sourcePath],model,instances,reads:packet.cert.reads,writer,writeKey:activeWriteKey(m,sourcePath),carried:[...activeCarried(m,sourcePath)],rowAliases:own.map(k=>({key:k,equal:writer?truth(same(k,x(writer)),sourcePath):undefined}))}))
   }
  }
  if(attempt>=retries)return
  pending=sourceWitnessInstances(m,laws,at,source,model,new Set(packet.cert.insts.map(i=>i.wit)))
  if(pending)throw restart
 }}:{})}),true))}catch(error){if(error!==restart)throw error}
 if(!pending)break
 sourceAdditions.push({attempt,added:Object.fromEntries(Object.entries(pending).flatMap(([name,ts])=>ts.length>(known[name]?.length??0)?[[name,ts.slice(known[name]?.length??0)]]:[]))})
 const retained=packet.cert;at=pending;packet=build();packet.cert=retained;goal=makeGoal()
 }
 const failed:any[]=[];let query:any
 for(const event of events){
  if(event.stage==='field-query')query=event
  if(event.stage==='count-lemma'&&!event.proposed&&failed.length<4){
   const next:Instances|undefined=query?.model?modelInstances(m,laws,at,goal,query.model,32):undefined,valid=next&&independentCountInstances(m,laws,at,next,packet.cert.insts.map(i=>i.wit))
   failed.push({index:event.index,terms:packet.cert.insts[event.index]?.terms,query:query&&{hyps:query.hyps,outcome:query.outcome,model:query.model},suggestedFromFullGoal:valid?Object.fromEntries(Object.entries(valid).flatMap(([name,ts])=>ts.length>(at[name]?.length??0)?[[name,ts.slice(at[name]?.length??0)]]:[])):null})
  }
 }
 if(events.some(e=>e.stage==='closure-source'&&e.scope<0))throw new Error('noncanonical closure scope')
 console.log(JSON.stringify({diagnostic:true,law:law.name,value,branch,carried,rowMode:process.env.LAB_ROW_MODE,ceilingIndex,ceilings,fieldAttempts:events.filter(e=>e.stage==='field-bound'),failed,sourceAdditions,...(process.env.LAB_SOURCE_TRACE==='1'?{countSteps:events.filter(e=>['count-lemma','needed-lemmas','field-bound-pending-core'].includes(e.stage)),closureSteps:events.filter(e=>e.stage.startsWith('closure-')),usedCounts:tree&&!hasConditionalProof(tree)?[...usedHyps(goal,tree,path)].filter(i=>i>=goal.hyps.length-packet.cert.insts.length).map(i=>({index:i-goal.hyps.length+packet.cert.insts.length,...packet.cert.insts[i-goal.hyps.length+packet.cert.insts.length]})):[]}:{}),wallMs:performance.now()-start,conditionalTree:!!tree,conditionalChecked:!!tree&&check(goal,tree,path),hyps:goal.hyps.length,instances:packet.cert.insts.length,suggestions,path:[...path],tail:events.slice(-14)}))
 section7?.finish()
}
