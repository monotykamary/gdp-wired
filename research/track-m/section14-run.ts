// T-11.5 op replay: every production local deadline remains intact.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {countedObligations,termColumn,canon,check,type Goal,type Path} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {proveCountCases} from '../../core/count-cases.ts'
import {checkConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {admitConditionalCut} from '../../core/count-recovery/conditional-cuts.ts'
import {shardControl as s} from './section13-control.ts'
import {tierControl} from './section14-control.ts'
import {section12Recorder} from './section12-recorder.ts'
import {diagnostic as d} from './section10-diagnostic.ts'
const [file,opText,out,budgetText='50000',seedFile]=process.argv.slice(2),op=Number(opText),allowance=Number(budgetText);if(!file||!out||!Number.isInteger(op)||!(allowance>0))throw new Error('PACKET OP OUT [TOTAL_UNITS] [SEEDS] required')
mkdirSync(out,{recursive:true});const p=JSON.parse(readFileSync(file,'utf8')),{m,laws,at,cert,packet,context,options}=p,law=laws.find((l:any)=>packet.goal.name.startsWith(l.name)),index=laws.indexOf(law)
const seed=seedFile?JSON.parse(readFileSync(seedFile,'utf8')):undefined
for(const [i,term]of (seed?.columns??p.columns).entries())if(termColumn(term)!==`⟦${i}⟧`)throw new Error('column restoration failed')
const record=section12Recorder(join(out,'actions.jsonl'));record.reset(law.name)
let result:any,current:any,last:any;const done={},imports:any[]=[]
if(seed){
 for(const x of seed.accepted){const goal:Goal={name:seed.root.name,hyps:x.lemma.slice.map((i:number)=>seed.root.hyps[i])},path:Path=new Map([[canon(x.lemma.cut),{lin:x.lemma.cut,holds:false}]]);if(x.lemma.when.length||!check(goal,x.lemma.tree,path))throw new Error('unverified root seed '+x.index)}
 tierControl.initial=goal=>seed.accepted.flatMap((x:any)=>{
  const local={name:seed.root.name,hyps:x.lemma.slice.map((i:number)=>seed.root.hyps[i])},path:Path=new Map([[canon(x.lemma.cut),{lin:x.lemma.cut,holds:false}]]),lemma=admitConditionalCut(goal,local,x.lemma.tree,path,new Map(),x.lemma.cut,[],performance.now()+10000)
  imports.push({index:x.index,accepted:!!lemma,name:goal.name});return lemma?[{lemma,good:x.good,index:x.index}]:[]
 })
}
s.mode='run';s.op=op;s.capture=()=>{};s.finish=r=>{result=r;throw done};s.query=(q,run)=>{current=q;last=record.latest();return run()}
const stats={cuts:0,sat:0,checkedSources:0,unknown:0,reused:0,rawSat:0,rawRefuted:0,rawUnknown:0},event=d.event.bind(d)
d.event=(kind,data)=>{event(kind,data);if(kind==='cut')stats.cuts++;if(kind==='source-result')stats[data.outcome==='checked'?'checkedSources':data.outcome==='sat'?'sat':data.outcome==='reused-model'?'reused':'unknown']++;if(kind==='source-query-result')stats[data.query?.tree||data.query?.why==='refuted, not unfolded'?'rawRefuted':data.query?.stuck==='sat'?'rawSat':'rawUnknown']++}
const begin=performance.now(),work=fullWork();let endClock=0
try{withWall(begin+600000,()=>counted(fullRate,()=>{endClock=clock()+allowance;return proveCountCases(m,laws,at,cert,endClock,next=>{const part=countedObligations(m,laws,{[law.name]:next},index).find(x=>x.goal.name.endsWith('@step'));if(!part)throw new Error('step missing');return part},{...options,trace:()=>{},propose:(g,ds)=>focusCountCert(m,ds,certFor(g,ds,true,1000),{carried:context.carried??undefined,structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,targets:context.targets,claim:g.hyps.at(-1)})})},true))}catch(e){if(e!==done)throw e}
const searchUnits=(fullWork()-work)/fullRate,searchWallMs=performance.now()-begin,checked=!!result&&checkConditionalProof(result.goal,result.tree,result.from??result.path),units=(fullWork()-work)/fullRate,wallMs=performance.now()-begin,detail=record.result(units)
const output={researchOnly:true,engine:p.revision,op,law:law.name,allowance,productionLocalDeadlines:true,inflightDump:false,seeded:!!seed,seedCount:seed?.accepted.length??0,imported:imports,closed:checked,verdict:checked?'closed':'unknown',units,wallMs,searchUnits,searchWallMs,endClock,stats,ledger:detail.ledger,firstFailure:detail.firstFailure??(checked?null:{kind:'no-branch-proof',activeQuery:current,lastNumeric:last}),stages:d.frames.filter(f=>['natural-query','numeric-query','batch-query','source-query','closure'].includes(f.kind)).map(f=>({id:f.id,parent:f.parent,kind:f.kind,units:f.units,exclusive:f.exclusive,meta:f.meta})),trace:detail.trace}
writeFileSync(join(out,'result.json'),JSON.stringify(output)+'\n');console.log(JSON.stringify({result:{...output,trace:undefined,firstFailure:undefined,stages:undefined}}))
