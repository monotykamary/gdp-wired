// Offline citation analysis. No new proof search and no removal of a lemma.
import {readFileSync,writeFileSync,mkdtempSync} from 'node:fs'
import {join} from 'node:path'
import {homedir} from 'node:os'
import {createHash} from 'node:crypto'
import {strict as assert} from 'node:assert'
import {termColumn,columnTerm,check,canon,leafConstraints,lemmaPath,facts,linear,type Goal,type Path,type Tree} from '../../kernel/kernel.ts'
import {markConditionalProof,checkConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {normalize,inequalityKey} from './section18-data.ts'
import {unpack} from './section18-codec.ts'
import {liveInputs} from './section19-recorder.ts'
import {sub} from '../../core/solver.ts'
import {citationStage} from './section19-stage.ts'
const linC=(lin:any)=>({op:'<=',a:Object.entries(lin).reduce<any>((a,[name,k])=>({op:'add',a,b:name==='1'?{op:'const',value:k}:{op:'mul',k,a:{op:'var',name}}}),{op:'const',value:0}),b:{op:'const',value:0}})
const sha=(b:Buffer)=>createHash('sha256').update(b).digest('hex')
const near=(a:number,b:number)=>Math.abs(a-b)<1e-6*Math.max(1,Math.abs(a),Math.abs(b))
if(process.argv[3]==='--one'){
 const x=unpack(readFileSync(process.argv[2]!,'utf8')),trace=x.citationTrace;assert(trace&&trace.version===1);assert(!x.error);assert.equal(x.allowance,5000);assert.equal(x.wallAllowance,4800)
 for(const [i,t]of x.columns.entries())assert.equal(termColumn(t),`⟦${i}⟧`)
 const results=new Map<number,any>(x.results.map((r:any)=>[r.id,r])),frames=new Map<number,any>(x.frames.map((f:any)=>[f.id,f]))
 const emissions=trace.emissions.map((e:any)=>{const r=results.get(e.id);assert(r?.emitted);assert.equal(JSON.stringify(normalize(e.good,r.reads,columnTerm)),r.key);const p=new Map(r.targetPath??[]) as Path,a=linear(e.good.a,p),b=linear(e.good.b,p);assert(a&&b);const expected=sub(a,b);if(e.good.op==='<')expected['1']=(expected['1']??0)+1;assert.equal(canon(e.cut),canon(expected));return {...e,result:r,key:inequalityKey(normalize(linC(e.cut),r.reads,columnTerm)),uses:[] as any[],requestedBefore:[] as any[]}})
 assert.equal(emissions.length,x.results.filter((r:any)=>r.emitted).length)
 const byId=new Map<number,any>(emissions.map((e:any)=>[e.id,e])),consumerAudit:any[]=[]
 const readsFor=(id:number|undefined)=>x.results.find((r:any)=>r.id===id)?.reads??x.results.find((r:any)=>r.helper&&frames.get(r.id)?.meta?.helper===id)?.reads??[]
 const cite=(ids:number[],c:any,kind:string,detail:any)=>{for(const id of new Set(ids)){const e=byId.get(id);assert(e);if(id===c.attempt)continue;assert(e.at<=c.at);e.uses.push({consumer:c.id,consumerName:c.name,consumerAttempt:c.attempt,stage:citationStage(c),kind,...detail})}}
 for(const c of trace.consumers){
  if(!c.tree&&!c.core)continue
  let goal=c.goal as Goal,path=new Map(c.path??[]) as Path,hypOwners=new Map<number,number[]>(c.hypOwners??[]),pathOwners=new Map<string,number[]>(c.pathOwners??[])
  const marks=new WeakMap<object,any>(),splitOwners=new WeakMap<object,number[]>()
  for(const s of c.snapshots??[]){let t=c.tree;for(const p of s.path)t=t[p];if(s.mark){marks.set(t,s.mark);markConditionalProof(s.mark.goal,t,s.mark.lemmas)}if(s.owners.length)splitOwners.set(t,s.owners)}
  let checked=false
  if(c.rawRows){goal={name:'captured solver rows',hyps:c.rawRows.map((r:any)=>linC(r.lin))};path=new Map();hypOwners=new Map(c.rowOwners.map((ids:number[],i:number)=>[i,ids]));checked=check(goal,c.tree,path)}
  else if(c.tree)checked=checkConditionalProof(goal,c.tree,path)
  if(!goal)throw Error('missing consumer goal')
  const reads=readsFor(c.attempt??c.helper),rowSeen=new Set<string>();let direct=0,shadows=0,contextReads=0
  const apply=(rows:any[],i:number,owners:number[][],active:Path,context:any,kind:string)=>{
   const row=rows[i];if(!row)return
   const key=kind+':'+i+':'+JSON.stringify([...active])+':'+JSON.stringify([...context.hypOwners]);if(rowSeen.has(key))return;rowSeen.add(key)
   const src=row.src,ids=src&&'fact'in src?(context.hypOwners.get(src.fact)??[]):src&&'atom'in src?(owners[src.atom]??[]):[]
   if(ids.length){cite(ids,c,ids.length===1?kind:'ambiguous-origin',{row:i});direct++}
   // A semantic match without a provenance tag is an upper-bound use, not an exact citation.
   const normalized=inequalityKey(normalize(linC(row.lin),reads,columnTerm)),possible=emissions.filter((e:any)=>e.at<c.at&&e.id!==c.attempt&&e.key===normalized&&!ids.includes(e.id)).map((e:any)=>e.id)
   if(possible.length){cite(possible,c,'possible-formula-match',{row:i,observedKind:kind});shadows++}
   for(const e of emissions.filter((e:any)=>e.at>c.at&&e.key===normalized))e.requestedBefore.push({consumer:c.id,kind,row:i})
   const touched=new Set<string>()
   class Observed extends Map<string,any>{override get(k:string){touched.add(k);return super.get(k)}override has(k:string){touched.add(k);return super.has(k)}}
   if(src&&'fact'in src)facts(context.goal.hyps[src.fact],new Observed(active))
   else if(src&&'term'in src){const term=columnTerm(src.term);if(term)linear(term,new Observed(active))}
   else if(src&&'pair'in src)for(const k of active.keys())touched.add(k)
   let j=0;for(const k of active.keys()){if(touched.has(k)&&owners[j]?.length){cite(owners[j]!,c,'context-read',{row:i,observedKind:kind});contextReads++}j++}
  }
  const walk=(t:Tree,p:Path,po:Map<string,number[]>,context:any):void=>{
   const own=marks.get(t);if(own)context={goal:own.goal,hypOwners:new Map(own.hypOwners),lemmas:own.lemmas,lemmaOwners:own.lemmaOwners}
   if('split'in t){const k=canon(t.split),ids=splitOwners.get(t)??[];walk(t.yes,new Map(p).set(k,{lin:t.split,holds:true}),new Map(po).set(k,ids),context);walk(t.no,new Map(p).set(k,{lin:t.split,holds:false}),new Map(po).set(k,[]),context);return}
   const active=lemmaPath(context.lemmas,p),indices=context.lemmas.flatMap((l:any,i:number)=>lemmaPath([l],p)!==p?[i]:[]),owners:number[][]=[...indices.map((i:number)=>context.lemmaOwners[i]??[]),...[...p.keys()].map(k=>po.get(k)??[])],rows=leafConstraints(context.goal,active),seen=new Set<number>()
   const input=(i:number):void=>{if(seen.has(i))return;seen.add(i);if(i<rows.length)apply(rows,i,owners,active,context,checked?'checked-proof':'proposed-proof');else if(i>=rows.length+(t.squares?.length??0)){const pair=t.products?.[i-rows.length-(t.squares?.length??0)];if(pair){input(pair[0]);input(pair[1])}}}
   for(const i of liveInputs(t.leaf))input(i)
  }
  if(c.tree)walk(c.tree,path,pathOwners,{goal,hypOwners,lemmas:[],lemmaOwners:[]})
  if(c.core){for(const i of c.core){assert(Number.isInteger(i)&&i>=0&&i<goal.hyps.length);const ids=hypOwners.get(i)??[];if(ids.length)cite(ids,c,ids.length===1?'core':'ambiguous-origin',{hyp:i});for(const lin of facts(goal.hyps[i]!,path)){const key=inequalityKey(normalize(linC(lin),reads,columnTerm)),possible=emissions.filter((e:any)=>e.at<c.at&&e.id!==c.attempt&&e.key===key&&!ids.includes(e.id)).map((e:any)=>e.id);if(possible.length)cite(possible,c,'possible-formula-match',{hyp:i,observedKind:'core'});for(const e of emissions.filter((e:any)=>e.at>c.at&&e.key===key))e.requestedBefore.push({consumer:c.id,kind:'core',hyp:i})}}}
  consumerAudit.push({id:c.id,name:c.name,attempt:c.attempt,helper:c.helper,zones:c.zones,tree:!!c.tree,core:!!c.core,checked,direct,shadows,contextReads,rawRows:!!c.rawRows})
 }
 for(const d of trace.decisions)cite(d.owners,{...d,id:'decision@'+d.at,name:d.name,zones:[]},'decision',{value:d.value})
 const records=emissions.map((e:any)=>{const r=e.result;assert(near(Object.values(r.units).reduce((a:any,b:any)=>a+b,0) as number,r.totalExclusive));return {id:e.id,helper:e.helper,kind:e.kind,at:e.at,key:e.key,statement:r.statement,targetChecked:r.targetChecked,sourceChecked:r.sourceChecked,units:r.units,totalUnits:r.totalExclusive,uses:e.uses,requestedBefore:e.requestedBefore,proofCited:e.uses.some((u:any)=>u.kind==='checked-proof'),coreCited:e.uses.some((u:any)=>u.kind==='core'),anyObservedUse:!!e.uses.length}})
 const summarize=(rs:any[])=>({emitted:rs.length,checked:rs.filter(r=>r.targetChecked).length,proofCited:rs.filter(r=>r.proofCited).length,coreCited:rs.filter(r=>r.coreCited).length,requestedBefore:rs.filter(r=>r.requestedBefore.length).length,decisionRead:rs.filter(r=>r.uses.some((u:any)=>u.kind==='decision')).length,possibleOnly:rs.filter(r=>r.uses.length&&!r.uses.some((u:any)=>['checked-proof','core','decision'].includes(u.kind))).length,noObservedUse:rs.filter(r=>!r.uses.length).length,emittedUnits:rs.reduce((s,r)=>s+r.totalUnits,0),notProofCitedUnits:rs.filter(r=>!r.proofCited).reduce((s,r)=>s+r.totalUnits,0),noObservedUseUnits:rs.filter(r=>!r.uses.length).reduce((s,r)=>s+r.totalUnits,0),noObservedUseSourceUnits:rs.filter(r=>!r.uses.length).reduce((s,r)=>s+r.units.source,0)})
 const summary={law:x.law,op:x.op,allowance:x.allowance,wallAllowance:x.wallAllowance,searchUnits:x.searchUnits,searchWallMs:x.searchWallMs,closed:x.closed,helperUnits:x.helperRootUnits,otherHelperUnits:x.nonAttemptHelperUnits,attempts:x.results.length,nonEmittedAttemptUnits:x.results.filter((r:any)=>!r.emitted).reduce((n:number,r:any)=>n+r.totalExclusive,0),consumerCalls:trace.consumers.length,consumerAudit,summaries:{all:summarize(records),field:summarize(records.filter((r:any)=>r.helper==='field')),frame:summarize(records.filter((r:any)=>r.helper==='frame'))},records}
 writeFileSync(process.argv[4]!,JSON.stringify(summary)+'\n')
}else{
 const input=process.argv[2]!,manifest=JSON.parse(readFileSync(join(input,'archive-manifest.json'),'utf8')),bytes=readFileSync(join(input,'receipts.tar.gz'));assert.equal(sha(bytes),manifest.sha256)
 const tmp=mkdtempSync('/tmp/section19-audit-'),out=mkdtempSync(join(homedir(),'track-m-section19-audit-'));let p=Bun.spawn(['tar','xzf',join(input,'receipts.tar.gz'),'-C',tmp],{stdout:'inherit',stderr:'inherit'});assert.equal(await p.exited,0)
 const rows=[];for(const name of ['overlap-op0','overlap-op4','star-op3','star-op5']){const raw=join(tmp,name+'-observe/result.json'),summary=raw+'.audit';p=Bun.spawn([process.execPath,import.meta.path,raw,'--one',summary],{stdout:'inherit',stderr:'inherit'});assert.equal(await p.exited,0,name);rows.push(JSON.parse(readFileSync(summary,'utf8')))}
 writeFileSync(join(out,'summary.json'),JSON.stringify({researchOnly:true,noNewSearch:true,inputSha256:manifest.sha256,rows},null,2)+'\n');const csv=['law,op,id,helper,kind,checked,proof_cited,core_cited,any_observed_use,units,source_units,uses'];for(const r of rows)for(const e of r.records)csv.push([r.law,r.op,e.id,e.helper,e.kind,e.targetChecked,e.proofCited,e.coreCited,e.anyObservedUse,e.totalUnits,e.units.source,JSON.stringify(e.uses)].map(v=>'"'+String(v).replaceAll('"','""')+'"').join(','));writeFileSync(join(out,'citations.csv'),csv.join('\n')+'\n')
 console.log(JSON.stringify({output:out,rows:rows.map(({records:_records,consumerAudit,...r})=>({...r,checkedConsumerProofs:consumerAudit.filter((c:any)=>c.checked).length}))}));p=Bun.spawn([process.execPath,'research/track-m/pack-section10-archive.ts',join(out,'summary.json'),join(out,'citations.csv')],{stdout:'inherit',stderr:'inherit'});assert.equal(await p.exited,0);p=Bun.spawn(['rm','-rf','--',tmp],{stdout:'inherit',stderr:'inherit'});assert.equal(await p.exited,0)
}
