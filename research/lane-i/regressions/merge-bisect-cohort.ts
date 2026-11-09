// A matching worker runs one paired trial at every missing point. Five matching
// workers give five repeats per commit without occupying a Ryzen for one point.
import {readFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {gzipSync} from 'node:zlib'
import {decodeReceipt} from './merge-bisect-audit.ts'
const id=Number(process.argv[2]),revisions:string[]=JSON.parse(readFileSync(process.argv[3]!,'utf8'))
if(!Number.isInteger(id)||id<100||revisions.some(rev=>!/^[a-f0-9]{40}$/.test(rev)))throw new Error('invalid cohort')
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim()
if(cpu!=='AMD Ryzen 9 9950X 16-Core Processor'){console.log('COHORT_CPU_SKIP '+JSON.stringify({id,cpu,revisions}));process.exit(0)}
const order=revisions.map((_,i)=>revisions[(i+id)%revisions.length]!),results=[]
for(const revision of order){
 const run=spawnSync(process.execPath,['regression-driver/merge-bisect.ts',revision,String(id),'1','--cohort'],{encoding:'utf8',timeout:180000,maxBuffer:64*1024*1024,env:process.env})
 const record={revision,exit:run.status,signal:run.signal,error:run.error?.message,stdout:run.stdout??'',stderr:run.stderr??''};results.push(record)
 console.log('COHORT_PROGRESS '+JSON.stringify({id,revision,exit:run.status,signal:run.signal}))
 if(run.status===0){const {summary}=decodeReceipt(record.stdout);if(summary.revision!==revision||summary.replica!==id||summary.repeats!==1||summary.cohort!==true)throw new Error('child identity mismatch')}
}
const output=gzipSync(JSON.stringify({id,cpu,revisions,results})).toString('base64')
if(output.length>350000)throw new Error('cohort output exceeds safe collector tail; recover worker stdout')
console.log('COHORT_RESULT_GZIP '+output)
if(results.some(row=>row.exit!==0))process.exitCode=1
