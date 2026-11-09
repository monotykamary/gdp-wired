// A checked op branch, not a complete-law proof. No production imports this.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {columnTerm,countedObligations,termColumn} from '../../kernel/kernel.ts'
import {fullRate,fullWork} from '../../kernel/prove.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {proveCountCases} from '../../core/count-cases.ts'
import {checkConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {shardControl as s} from './section13-control.ts'
import {boundedResearch,ResearchStop} from './bounded-research.ts'
import {section12Recorder} from './section12-recorder.ts'
import {diagnostic as d} from './section10-diagnostic.ts'
import {realNow} from './without-deadlines.ts'
const [file,opText,out]=process.argv.slice(2),op=Number(opText);if(!file||!out||!Number.isInteger(op)||op<0||op>6)throw new Error('PACKET OP OUT required')
mkdirSync(out,{recursive:true})
const p=JSON.parse(readFileSync(file,'utf8')),{m,laws,at,cert,packet,context,options}=p,law=laws.find((l:any)=>packet.goal.name.startsWith(l.name)),index=laws.indexOf(law)
for(let i=0;i<p.columns.length;i++)if(termColumn(p.columns[i])!==`⟦${i}⟧`)throw new Error('column restoration failed')
const name=law.name.startsWith('Inv2973')?'Inv2973':'Invstar',record=section12Recorder(join(out,'actions.jsonl'));record.reset(law.name)
const columns=()=>{const xs=[];for(let i=0;;i++){const t=columnTerm(`⟦${i}⟧`);if(t===undefined)return xs;xs.push(t)}}
let current:any={kind:'action-entry',goal:packet.goal,path:[]},latest:any,result:any,finalContext:any,limit:string|undefined
const done={},start=realNow(),before=fullWork(),stats={cuts:0,sat:0,refuted:0,unknown:0,reused:0,cached:0,rawSat:0,rawRefuted:0,rawUnknown:0},baseEvent=d.event.bind(d)
d.event=(kind,data)=>{baseEvent(kind,data);if(kind==='cut')stats.cuts++;if(kind==='source-result'){const k=data.outcome==='checked'?'refuted':data.outcome==='sat'?'sat':data.outcome==='reused-model'?'reused':'unknown';stats[k]++}if(kind==='source-cached')stats.cached++;if(kind==='source-query-result')stats[data.query?.tree||data.query?.why==='refuted, not unfolded'?'rawRefuted':data.query?.stuck==='sat'?'rawSat':'rawUnknown']++;if(['source-result','source-cached'].includes(kind)){const e=d.events.at(-1),f=e&&d.frames[e.frame];if(f)writeFileSync(join(out,'outcomes.jsonl'),JSON.stringify({index:data.index,outcome:data.outcome,path:f.meta.path,units:fullWork()/fullRate-f.start})+'\n',{flag:'a'})}if(kind==='stop'&&!d.events.slice(0,-1).some(e=>e.kind==='stop'))writeFileSync(join(out,'first-failure.json'),JSON.stringify(record.result(0).firstFailure)+'\n')}
s.mode='run';s.op=op
s.capture=()=>{}
s.finish=(r,c)=>{result=r;finalContext=c;throw done}
s.query=(q,run)=>{current=q;latest=record.latest();writeFileSync(join(out,'inflight.json'),JSON.stringify({law:law.name,op,packet:q,lastNumeric:latest,columns:columns()})+'\n');return run()}
try{
 boundedResearch(50000,600000,()=>proveCountCases(m,laws,at,cert,50000,next=>{
  const part=countedObligations(m,laws,{[law.name]:next},index).find(x=>x.goal.name.endsWith('@step'));if(!part)throw new Error('missing step packet');return part
 },{...options,trace:()=>{},propose:(g,ds)=>focusCountCert(m,ds,certFor(g,ds,true,1000),{carried:context.carried??undefined,structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,targets:context.targets,claim:g.hyps.at(-1)})}),progress=>writeFileSync(join(out,'heartbeat.json'),JSON.stringify({...progress,stats,law:law.name,op,kind:current.kind})+'\n'))
}catch(e){if(e instanceof ResearchStop)limit=e.reason;else if(e!==done)throw e}
const searchUnits=(fullWork()-before)/fullRate,searchWallMs=realNow()-start,checked=!!result&&checkConditionalProof(result.goal,result.tree,result.from??result.path),totalUnits=(fullWork()-before)/fullRate,wallMs=realNow()-start,detail=record.result(totalUnits)
const capture=detail.firstFailure?.capture??latest,failure=checked?null:detail.firstFailure??{kind:'budget',reason:limit??'no-branch-tree',path:capture?.path??current.path,capture,activeQuery:current}
const ancestor=(id:number|undefined,leaf:number)=>{while(id!==undefined){if(id===leaf)return true;id=d.frames[id]?.parent}return false}
const violated=(failure?.capture?.violated??[]) as number[]
const sources=violated.map(i=>{
 const leaf=failure.capture.frame,attempts=d.frames.filter(f=>f.kind==='source-attempt'&&f.meta.index===i&&ancestor(f.id,leaf)).map(f=>({path:f.meta.path,units:f.units??0,outcomes:d.events.filter(e=>e.frame===f.id&&['source-result','source-cached','source-query-result'].includes(e.kind))})),observed=attempts.flatMap(a=>a.outcomes.filter(e=>e.kind==='source-result'||e.kind==='source-cached').map(e=>e.outcome))
 const source=failure.capture.source?.(i)
 return {index:i,inst:failure.capture.cert.insts[i],result:observed.at(-1)??'unattempted',units:attempts.reduce((n,a)=>n+a.units,0),attempts,...(source?{packet:{goal:source.part,path:failure.capture.path}}:{})}
})
const output={researchOnly:true,law:law.name,name,op,verdict:checked?'closed':'unknown',closed:checked,limit:limit??null,allowance:50000,wallLimitMs:600000,searchUnits,units:totalUnits,searchWallMs,wallMs,stats,ledger:detail.ledger,outsideActions:detail.outsideActions,firstFailure:failure,sources:sources.map(({packet:_packet,...rest})=>rest),columns:columns(),packetScope:'captured first production action-entry packet; other ops skipped, no complete-law claim'}
writeFileSync(join(out,'result.json'),JSON.stringify({...output,trace:detail.trace})+'\n')
writeFileSync(join(out,'sources.json'),JSON.stringify({law:law.name,op,sources,columns:columns()})+'\n')
if(result)writeFileSync(join(out,'branch-proof.json'),JSON.stringify({result,context:finalContext,columns:columns()})+'\n')
// Compact immediate-publication record; full columns remain only in archives.
const {columns:_columns,...published}=output
console.log(JSON.stringify({shardResult:{...published,firstFailure:failure?{kind:failure.kind,reason:failure.reason,path:failure.path,guards:failure.path,numericModel:failure.capture?.model??null,violatedSet:failure.capture?.violated??[],capture:failure.capture?{path:failure.capture.path,model:failure.capture.model,violated:failure.capture.violated,cert:failure.capture.cert}:null,activeQuery:failure.activeQuery?{kind:failure.activeQuery.kind,path:failure.activeQuery.path}:undefined}:null}}))
