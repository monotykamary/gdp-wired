// Supervisor fallback: a killed atomic query is unknown, never a refutation.
import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
const [out,file,op,exit]=process.argv.slice(2);if(!out||!file)throw new Error('OUT PACKET OP EXIT required')
const read=(name:string)=>existsSync(join(out,name))?JSON.parse(readFileSync(join(out,name),'utf8')):null,p=JSON.parse(readFileSync(file,'utf8')),heartbeat=read('heartbeat.json'),inflight=read('inflight.json'),first=read('first-failure.json'),name=p.packet.goal.name.startsWith('Inv2973')?'Inv2973':'Invstar'
const cap=first?.capture??inflight?.lastNumeric,observed=existsSync(join(out,'outcomes.jsonl'))?readFileSync(join(out,'outcomes.jsonl'),'utf8').trim().split('\n').filter(Boolean).map(l=>JSON.parse(l)):[]
const sources=(cap?.violated??[]).map((i:number)=>{const attempts=observed.filter(a=>a.index===i);return {index:i,inst:cap.cert.insts[i],result:attempts.at(-1)?.outcome??'unattempted',units:attempts.reduce((s,a)=>s+a.units,0),attempts}})
const result={researchOnly:true,name,law:p.packet.goal.name,op:Number(op),verdict:'unknown',closed:false,limit:'external-watchdog',exit:Number(exit),allowance:50000,wallLimitMs:600000,units:heartbeat?.units??null,unitsAreLowerBound:true,wallMs:600000,stats:heartbeat?.stats??null,firstFailure:first??{kind:'censored',reason:'external-watchdog',path:cap?.path??inflight?.packet?.path,guards:cap?.path??inflight?.packet?.path,capture:cap??null,activeQuery:inflight?.packet??null},sources,columns:inflight?.columns??p.columns}
writeFileSync(join(out,'result.json'),JSON.stringify(result)+'\n')
