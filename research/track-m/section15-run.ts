// T-12: one captured op at the unchanged 5,000-unit law allowance.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {countedObligations,termColumn} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {proveCountCases} from '../../core/count-cases.ts'
import {checkConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {shardControl as s} from './section13-control.ts'
import {section12Recorder} from './section12-recorder.ts'
import {diagnostic as d} from './section10-diagnostic.ts'
import {t12} from './section15-control.ts'
const [file,opText,out,flags='all']=process.argv.slice(2),op=Number(opText);if(!file||!out||!Number.isInteger(op))throw new Error('PACKET OP OUT [all|none]')
const p=JSON.parse(readFileSync(file,'utf8')),{m,laws,at,cert,packet,context,options}=p,law=laws.find((l:any)=>packet.goal.name.startsWith(l.name)),index=laws.indexOf(law)
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw new Error('column restoration failed')
Object.assign(t12,{cap:flags==='all',classes:flags==='all',modelFirst:flags==='all'});mkdirSync(out,{recursive:true})
const record=section12Recorder(join(out,'actions.jsonl'));record.reset(law.name)
let result:any,current:any;const done={};s.mode='run';s.op=op;s.capture=()=>{};s.finish=r=>{result=r;throw done};s.query=(q,run)=>{current=q;return run()}
const start=performance.now(),work=fullWork(),allowance=5000;let error:string|undefined
try{withWall(start+600000,()=>counted(fullRate,()=>proveCountCases(m,laws,at,cert,clock()+allowance,next=>{const x=countedObligations(m,laws,{[law.name]:next},index).find(x=>x.goal.name.endsWith('@step'));if(!x)throw new Error('step missing');return x},{...options,trace:()=>{},propose:(g,ds)=>focusCountCert(m,ds,certFor(g,ds,true,1000),{carried:context.carried??undefined,structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,targets:context.targets,claim:g.hyps.at(-1)})}),true))}catch(e){if(e!==done)error=String(e)}
const checked=!!result&&checkConditionalProof(result.goal,result.tree,result.from??result.path),units=(fullWork()-work)/fullRate,wallMs=performance.now()-start,detail=record.result(units)
const nearest=(id:number|undefined,kind:string):number|undefined=>{while(id!==undefined){const f=d.frames[id];if(!f)return undefined;if(f.kind===kind)return id;id=f.parent}return undefined}
const sourceOutcomes=new Map(d.events.filter(e=>e.kind==='source-result').map(e=>[e.frame,e.outcome])),sourceQueries=d.frames.filter(f=>f.kind==='source-query')
const checkedSourceQueryUnits=sourceQueries.filter(f=>sourceOutcomes.get(nearest(f.id,'source-attempt'))==='checked').reduce((s,f)=>s+(f.exclusive??0),0)
const checkedSourceAttemptUnits=d.frames.filter(f=>f.kind==='source-attempt'&&sourceOutcomes.get(f.id)==='checked').reduce((s,f)=>s+(f.units??0),0)
const groups=new Map<string,any>();for(const f of d.frames.filter(f=>f.kind==='action-site')){const k=f.meta.site;let g=groups.get(k);if(!g){g={site:k,fn:f.meta.fn,calls:0,units:0,exclusive:0,maxUnits:0};groups.set(k,g)}g.calls++;g.units+=f.units??0;g.exclusive+=f.exclusive??0;g.maxUnits=Math.max(g.maxUnits,f.units??0)}
const output={researchOnly:true,engine:p.revision,law:law.name,op,flags:{...t12},allowance,productionLocalDraws:true,inflightDump:false,seedCount:0,closed:checked,verdict:checked?'closed':'unknown',error,units,wallMs,checkedSourceQueryUnits,checkedSourceAttemptUnits,stopRuleTriggered:units>2500&&op===4||checkedSourceQueryUnits>1500&&op===4,ledger:detail.ledger,firstFailure:detail.firstFailure??(checked?null:{kind:'no-branch-proof',activeQuery:current}),sites:[...groups.values()],rounds:d.frames.filter(f=>f.kind==='action-query-round').map(f=>({id:f.id,parent:f.parent,round:f.meta.round,units:f.units,exclusive:f.exclusive})),unprofiledActionUnits:d.frames.filter(f=>f.kind==='action').reduce((s,f)=>s+(f.exclusive??0),0),trace:detail.trace}
writeFileSync(join(out,'result.json'),JSON.stringify(output)+'\n');console.log(JSON.stringify({...output,trace:undefined,firstFailure:undefined}))
if(error)process.exitCode=1
