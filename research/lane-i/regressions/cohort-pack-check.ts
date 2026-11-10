// Transport-only load fixture from already collected measurements; not new proof evidence.
import {readFileSync,readdirSync} from 'node:fs'
import {gzipSync,gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
import {decodeReceipt} from './merge-bisect-audit.ts'
import {packCohort,cohortReceipt,unpackCohort} from './cohort-envelope.ts'
const dir=process.argv[2]!,samples:any[]=[]
for(const file of readdirSync(dir).filter(name=>name.endsWith('.log.gz'))){const text=gunzipSync(readFileSync(join(dir,file))).toString('utf8');if(!text.includes('BISECT_SUMMARY_GZIP'))continue;try{samples.push(decodeReceipt(text))}catch{}}
if(!samples.length)throw new Error('no archived fixtures')
const results:any[]=[]
for(let i=0;results.length<10;i++){const sample=samples[i%samples.length],record=sample.summary.records[Math.floor(i/samples.length)%sample.summary.records.length],traces=sample.traces.filter((trace:any)=>trace.repeat===record.repeat),summary={...sample.summary,records:[record],repeats:1,traceSha256:createHash('sha256').update(JSON.stringify(traces)).digest('hex')},stdout='BISECT_TRACES_GZIP '+gzipSync(JSON.stringify(traces)).toString('base64')+'\nBISECT_SUMMARY_GZIP '+gzipSync(JSON.stringify(summary)).toString('base64');results.push({revision:summary.revision,exit:0,stdout,stderr:''})}
const group={id:999,cpu:'transport-only fixture',revisions:results.map(result=>result.revision),results},old=gzipSync(JSON.stringify(group)).toString('base64'),bytes=packCohort(group),packed=bytes.toString('base64'),decoded=unpackCohort(bytes)
for(let i=0;i<results.length;i++)if(JSON.stringify(cohortReceipt(decoded,decoded.results[i]))!==JSON.stringify(decodeReceipt(results[i].stdout)))throw new Error('lossy receipt transport')
console.log(JSON.stringify({scope:'transport-only; not new benchmark runs',fixtures:samples.length,pairedRecords:results.length,oldBase64Bytes:old.length,newBase64Bytes:packed.length,lossless:true}))
if(packed.length>350000)throw new Error('real-trace transport load still exceeds collector allowance')
