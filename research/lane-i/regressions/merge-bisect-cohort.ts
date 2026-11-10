// A matching worker runs one paired trial at every missing point. Five matching
// workers give five repeats per commit without occupying a Ryzen for one point.
import {readFileSync,writeFileSync,mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {spawnSync} from 'node:child_process'
import {gzipSync} from 'node:zlib'
import {decodeReceipt} from './merge-bisect-audit.ts'
import {packCohort} from './cohort-envelope.ts'
const id=Number(process.argv[2]),revisions:string[]=JSON.parse(readFileSync(process.argv[3]!,'utf8'))
if(!Number.isInteger(id)||id<100||revisions.some(rev=>!/^[a-f0-9]{40}$/.test(rev)))throw new Error('invalid cohort')
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim()
if(cpu!=='AMD Ryzen 9 9950X 16-Core Processor'){console.log('COHORT_CPU_SKIP '+JSON.stringify({id,cpu,revisions}));process.exit(0)}
const archive=mkdtempSync(join(tmpdir(),`lane-i-cohort-${id}-`))
console.log('COHORT_ARCHIVE '+JSON.stringify({id,path:archive}))
const order=revisions.map((_,i)=>revisions[(i+id)%revisions.length]!),results=[]
for(const revision of order){
 const run=spawnSync(process.execPath,['regression-driver/merge-bisect.ts',revision,String(id),'1','--cohort'],{encoding:'utf8',timeout:180000,maxBuffer:64*1024*1024,env:process.env})
 const record={revision,exit:run.status,signal:run.signal,error:run.error?.message,stdout:run.stdout??'',stderr:run.stderr??''};results.push(record)
 writeFileSync(join(archive,revision+'.json.gz'),gzipSync(JSON.stringify(record)))
 console.log('COHORT_PROGRESS '+JSON.stringify({id,revision,exit:run.status,signal:run.signal}))
 if(run.status===0){const {summary}=decodeReceipt(record.stdout);if(summary.revision!==revision||summary.replica!==id||summary.repeats!==1||summary.cohort!==true)throw new Error('child identity mismatch')}
}
const bytes=packCohort({id,cpu,revisions,results}),output=bytes.toString('base64')
writeFileSync(join(archive,'cohort.json.br'),bytes)
if(output.length>350000)throw new Error('cohort output exceeds safe collector tail; durable archive: '+archive)
console.log('COHORT_RESULT_BR '+output)
if(results.some(row=>row.exit!==0))process.exitCode=1
