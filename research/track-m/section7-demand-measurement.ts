// Research-only T2/T3 measurements of the captured v7 incomplete arithmetic leaves.
// No assumed pool fact is exported as a proof or admitted to a production goal.
import {readFileSync} from 'node:fs'
import {type C,type Machine,x} from '../../core/machine.ts'
import {type CountCert,type Goal,type Path,canon,substC} from '../../kernel/kernel.ts'
import {brokenOf,clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {countBindingsAt} from '../../core/count-recovery/field-bound-lemmas.ts'
import {piecesAt,walkLive} from '../../core/count-recovery/live-dependencies.ts'

type Captured={law:string,closureSteps:any[]}
type Inputs={law:string,final:any,active:number[],requested:number[],violated:number[],pool:number[],originalInstances:number}
export function inputs(law:string,cert:Pick<CountCert,'reads'|'insts'>,goal:Goal):Inputs{
 const file=process.env.LAB_SECTION7_CAPTURE;if(!file)throw new Error('LAB_SECTION7_CAPTURE required')
 const rows=readFileSync(file,'utf8').split('\n').filter(s=>s.startsWith('{')).map(s=>JSON.parse(s) as Captured)
 const final=rows.filter(r=>r.law===law).flatMap(r=>r.closureSteps??[]).findLast(r=>r.stage==='closure-final'&&r.outcome==='sat'&&r.model&&r.path)
 if(!final)throw new Error('missing captured incomplete leaf: '+law)
 const active=[...new Set<number>(final.closedIndices)],requested=law.startsWith('Inv*')?[84,18,23,32,33,29,30,27,28]:[126,275,276,271,272,141,142,143,144]
 const offset=goal.hyps.length-cert.insts.length,pool:number[]=[],violated:number[]=[]
 for(const [i,q]of cert.insts.entries()){
  const h=goal.hyps[offset+i]
  if(q.terms.length>5||h?.op!=='or'||h.xs[0]?.op!=='<=')continue
  pool.push(i);if(brokenOf({name:'captured-pool-good',hyps:[h.xs[0]]})(final.model).length)violated.push(i)
 }
 if([...active,...requested].some(i=>!pool.includes(i)))throw new Error('requested index is outside current pool')
 return {law,final,active,requested,violated,pool,originalInstances:cert.insts.length}
}
export function targetPath(fresh:Path,data:Inputs):Path{
 const path=new Map(fresh)
 // Opaque column IDs are process-local. Retain the fresh guard's columns and
 // copy only the captured leaf's explicit scalar/row comparisons, never ⟦n⟧.
 for(const [,atom]of data.final.path as [string,{lin:Record<string,number>,holds:boolean}][]){
  if(Object.keys(atom.lin).some(k=>k.includes('⟦')))continue
  const id=canon(atom.lin),old=path.get(id)
  if(old&&old.holds!==atom.holds)throw new Error('captured leaf conflicts with fresh guard')
  path.set(id,{lin:{...atom.lin},holds:atom.holds})
 }
 return path
}
export function restrictPool(cert:Pick<CountCert,'reads'|'insts'>,data:Inputs){
 const wanted=new Set([...data.active,...data.requested]),indices=cert.insts.flatMap((_,i)=>wanted.has(i)?[i]:[])
 cert.insts=indices.map(i=>cert.insts[i]!)
 return {policy:'section-7.5-explicit-indices-plus-v7-active',originalInstances:data.originalInstances,instances:indices.length,originalIndices:indices,activeUnique:data.active.length,activeReported:data.final.cuts,requested:data.requested,violatedByCapturedModel:data.violated,violatedNotSelected:data.violated.filter(i=>!wanted.has(i))}
}
export function measureAllAssumed(m:Machine,g:Goal,cert:Pick<CountCert,'reads'|'insts'>,path:Path,data:Inputs){
 const raw=g.hyps.slice(0,-cert.insts.length),maps=new Set(cert.reads.map(r=>r[1])),wits=new Set(cert.insts.map(q=>q.wit))
 const replacements=Object.fromEntries([...maps].map(map=>[map,(key:any)=>{const r=cert.reads.find(r=>r[1]===map&&JSON.stringify(r[2])===JSON.stringify(key));return r?x(r[0]):{op:'get' as const,map,key}}]))
 const flags=Object.fromEntries(Object.keys(m.step.flags??{}).map(name=>[name,{op:'flag' as const,name}]))
 const pure=(c:C)=>{let other=false;walkLive(c,path,(o:any)=>{if(o.op==='get'||o.op==='var'&&wits.has(o.name))other=true});return !other}
 const abstracted=raw.map(c=>substC(c,{vars:{},maps:replacements,flags})),base=[...abstracted.flatMap(c=>piecesAt(c,path)).filter(pure),...countBindingsAt(cert.reads,path)]
 const offset=g.hyps.length-cert.insts.length,goods=data.pool.map(i=>{const h=g.hyps[offset+i];if(h?.op!=='or'||h.xs[0]?.op!=='<=')throw new Error('bad pool clause');return h.xs[0]})
 const numeric:Goal={name:g.name,hyps:[...base,...goods]},before=fullWork(),start=performance.now()
 const result=withWall(start+1000,()=>counted(fullRate,()=>modelSequence(path)(numeric,clock()+350),true)),wallMs=performance.now()-start,countedUnits=(fullWork()-before)/fullRate
 const core='tree'in result?[]:result.core??[],poolCore=core.filter(i=>i>=base.length).map(i=>data.pool[i-base.length]!)
 const witness='tree'in result?undefined:result.witness
 const classification='tree'in result||result.why===REFUTED?'refuted':result.stuck==='sat'?'generator-gap':'unknown'
 console.log(JSON.stringify({measurement:'T3',law:data.law,classification,assumptionsOnly:true,completeLawProof:false,wallMs,countedUnits,queryUnitLimit:350,wallLimitMs:1000,baseHyps:base.length,poolHyps:goods.length,hyps:numeric.hyps.length,poolOriginalIndices:data.pool,core,poolCore,coreWits:poolCore.map(i=>cert.insts[i]!.wit),path:[...path],result,validatedSat:witness&&classification==='generator-gap'?brokenOf(numeric)(witness).length===0:undefined,violatedAssumedGoods:witness&&classification==='generator-gap'?brokenOf({name:'goods',hyps:goods})(witness).map(i=>data.pool[i]):undefined,numeric}))
}
