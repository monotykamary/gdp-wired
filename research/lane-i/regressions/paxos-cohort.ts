import {paxosCpu} from './paxos-cpu.ts'
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
const repeats=Number(process.argv[4]??1)
if(!Number.isInteger(repeats)||repeats<1||repeats>5)throw new Error('invalid repeats')
if(!Number.isInteger(id)||id<100||revisions.some(rev=>!/^[a-f0-9]{40}$/.test(rev)))throw new Error('invalid cohort')
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim()
if(cpu!==paxosCpu){console.log('PAXOS_COHORT_CPU_SKIP '+JSON.stringify({id,cpu,revisions}));process.exit(0)}
const archive=mkdtempSync(join(tmpdir(),`lane-i-cohort-${id}-`))
console.log('PAXOS_COHORT_ARCHIVE '+JSON.stringify({id,path:archive}))
const order=revisions.map((_,i)=>revisions[(i+id)%revisions.length]!),results=[]
for(const revision of order){
 const run=spawnSync(process.execPath,['regression-driver/paxos-bisect.ts',revision,String(id),String(repeats),'--cohort'],{encoding:'utf8',timeout:(repeats*130+50)*1000,maxBuffer:64*1024*1024,env:process.env})
 const record={revision,exit:run.status,signal:run.signal,error:run.error?.message,stdout:run.stdout??'',stderr:run.stderr??''};results.push(record)
 writeFileSync(join(archive,revision+'.json.gz'),gzipSync(JSON.stringify(record)))
 console.log('PAXOS_COHORT_PROGRESS '+JSON.stringify({id,revision,exit:run.status,signal:run.signal}))
 if(run.status===0){const {summary}=decodeReceipt(record.stdout);if(summary.revision!==revision||summary.replica!==id||summary.repeats!==repeats||summary.cohort!==true)throw new Error('child identity mismatch')}
}
const bytes=packCohort({id,cpu,revisions,results}),output=bytes.toString('base64')
writeFileSync(join(archive,'cohort.json.br'),bytes)
if(output.length>350000)throw new Error('cohort output exceeds safe collector tail; durable archive: '+archive)
console.log('PAXOS_COHORT_RESULT_BR '+output)
if(results.some(row=>row.exit!==0))process.exitCode=1
