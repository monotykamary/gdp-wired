import {writeFileSync} from 'node:fs'
import {diagnostic as d} from './section10-diagnostic.ts'
import {clock,counted,fullRate,fullWork,brokenOf,withWall,withDeadline} from '../../kernel/prove.ts'
import {columnTerm,check} from '../../kernel/kernel.ts'
import {modelSequence,grow,widen} from '../../core/count-recovery/ops.ts'
import {booleanCore} from '../../core/count-recovery/boolean-core.ts'
import {foldPath} from '../../core/count-recovery/fold-path.ts'
import {walkLive} from '../../core/count-recovery/live-dependencies.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {atPoint} from '../../kernel/prove.ts'
export function analyzeSection10(output:string,record:Pick<typeof d,'frames'|'events'|'captures'|'label'>=d){
// All following work is a separate diagnostic allowance, never the row share.
const main=new Set(record.frames.filter(f=>f.kind==='closure'&&f.meta.main).map(f=>f.id)),finalCase=record.events.findLast((e:any)=>e.kind==='case-final-results'),target=finalCase?.unresolved[0],stop=record.events.find((e:any)=>e.kind==='stop'&&main.has(e.closure)&&(target===undefined||target==='else'||e.path.filter(([,a]:any)=>Object.keys(a.lin).every(k=>k==='1'||k===finalCase.selector)).every(([,a]:any)=>{const n=(a.lin['1']??0)+(a.lin[finalCase.selector]??0)*target;return a.holds?n<=0:n>0})))
if(!stop)throw new Error('no first unfinished main subbranch captured')
const key=(p:any)=>JSON.stringify(p),capture=record.captures.findLast(c=>c.closure===stop.closure&&key(c.path)===key(stop.path))
if(!capture)throw new Error('no numeric query for unfinished subbranch')
const path=new Map(capture.path) as any
const valid=(g:any,p:any,point:any)=>{const model={...point};walkLive(g.hyps,p,(o:any)=>{if(o.op==='var'&&!Object.hasOwn(model,o.name))model[o.name]=0});for(const a of p.values() as any)for(const k of Object.keys(a.lin))if(k!=='1'&&!Object.hasOwn(model,k))model[k]=0;return Object.values(model).every(Number.isSafeInteger)&&!brokenOf(g)(model).length&&[...p.values()].every((a:any)=>{const n=Object.entries(a.lin).reduce((s:number,[k,v])=>s+(v as number)*(k==='1'?1:model[k]),0);return a.holds?n<=0:n>0})?model:undefined}
const measure=<T>(fn:()=>T)=>{const before=fullWork();const value=withWall(performance.now()+60000,()=>counted(fullRate,fn,true));return {value,units:(fullWork()-before)/fullRate}}
const probe=measure(()=>modelSequence(path)(capture.numeric,clock()+5000)),q:any=probe.value
const point=!(q&&'tree'in q)&&q.stuck==='sat'&&q.witness?{...q.witness}:undefined
if(point)for(const index of capture.pool){const {inst}=capture.source(index);for(const [,id]of inst.terms)if(!Object.hasOwn(point,id))point[id]=0}
const model=point&&valid(capture.numeric,path,point),numericChecked=!!q&&'tree'in q&&check(capture.numeric,q.tree,path)
const lastObserved=record.captures.findLast(c=>c.closure===stop.closure&&c.model),sourceCapture=model?capture:lastObserved,sourceModel=model??lastObserved?.model,sourcePath=sourceCapture?new Map(sourceCapture.path) as any:path
const violated=sourceModel&&sourceCapture?sourceCapture.pool.filter((index:number)=>{const {part}=sourceCapture.source(index),h=part.hyps.at(-2);return brokenOf({name:'candidate',hyps:[h.xs[0]]})(sourceModel).length>0}):[]
const sources=[]
for(const index of violated){
 const {inst,part}=sourceCapture.source(index)
 let tree:any,proofSource=part,initial:any,validatedModel:any
 const measured=measure(()=>{const queryLimit=clock()+(inst.terms.length===5?150:50);initial=modelSequence(sourcePath)(part,queryLimit);tree='tree'in initial?initial.tree:undefined
  if(!tree&&initial.stuck==='sat'&&initial.witness)validatedModel=valid(part,sourcePath,initial.witness)
  else if(!tree&&initial.why===REFUTED&&initial.core?.length&&initial.core.length<=8){const end=Math.max(queryLimit,clock()+100),small={...part,hyps:initial.core.map((i:number)=>part.hyps[i])},old=atPoint.on;atPoint.on=false;try{let local=booleanCore(small,sourcePath,new Set([inst.wit]),end,[],{deferCheck:true,extended:true,scalarGuards:true,model:true});if(!local&&clock()<end){const folded=foldPath(small,sourcePath),out=grow(folded.goal,sourcePath,{nodes:0,until:Math.min(end,clock()+25),units:false});local='tree'in out?withDeadline(end,()=>widen(folded.goal,small,out.tree,folded.opaque,sourcePath,sourcePath)):undefined}if(local){tree=local;proofSource=small}}finally{atPoint.on=old}}
 })
 const checked=!!tree&&check(proofSource,tree,sourcePath)
 const reused=record.events.filter(e=>e.kind==='source-result'&&e.outcome==='reused-model'&&e.index===index&&key(e.path)===key(sourceCapture.path))
 sources.push({index,inst,part,query:initial,outcome:checked?'refuted-checked':validatedModel?'sat-validated':'unknown',units:measured.units,checked,model:validatedModel,reusedDuringProduction:reused.length})
}
const columns=[];for(let i=0;;i++){const e=columnTerm(`⟦${i}⟧`);if(e===undefined)break;columns.push(e)}
const result={revision:'192ebbe2',diagnosticOnly:true,production:{label:record.label,frames:record.frames,events:record.events,captures:record.captures.map(({source:_source,...rest}:any)=>rest)},firstUnfinished:stop,captureId:capture.id,originalNumericQuery:capture.query,originalNumericModel:capture.model,freshDiagnosticNumeric:{allowance:5000,units:probe.units,query:q,model,valid:!!model,checked:numericChecked,violated:model?violated:[]},sourceContext:sourceCapture&&{captureId:sourceCapture.id,path:sourceCapture.path,model:sourceModel,violated,kind:model?'fresh-terminal-model':'last-observed-model'},sources,columns}
writeFileSync(output,JSON.stringify(result,(key,value)=>key==='tree'&&value&&typeof value==='object'?{proofOmitted:true}:value)+'\n')
console.log(JSON.stringify({diagnosticResult:output,mainClosures:[...main],firstUnfinished:stop,capture:capture.id,numericUnits:probe.units,numericValid:!!model,violated,sources:sources.map(s=>({index:s.index,outcome:s.outcome,units:s.units}))}))

}
