import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
import {cpSync,mkdtempSync,readFileSync,readdirSync,rmSync,writeFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {gunzipSync,gzipSync} from 'node:zlib'
const [current,before,source,kernelHash,checkerHash]=process.argv.slice(2),auditor=resolve('research/lane-i/merge-0480/audit.ts')
const run=(dir:string)=>spawnSync('bun',[auditor,dir,before!,source!,kernelHash!,checkerHash!,'release-compatible'],{encoding:'utf8',timeout:30000,maxBuffer:4*1024*1024})
const positive=run(current!);a.equal(positive.status,0,positive.stdout+positive.stderr)
const file=readdirSync(current!).filter(f=>f.startsWith('off-candidate-')&&f.endsWith('.log')).sort()[0]!,full=file.replace('off-candidate-','strict-')
const mutations:[string,string,(r:any)=>void][]=[['source',file,r=>{r.source='0'.repeat(40)}],['custody',full,r=>{r.custody['kernel/kernel.ts']='0'.repeat(64)}],['ledger',full,r=>{r.raw.ticks++}],['clock',full,r=>{r.clockReads=1}],['off-trace',file,r=>{r.events.push({phase:'synthetic-audit-drift'})}]]
for(const[name,target,mutate]of mutations){const dir=mkdtempSync(join(tmpdir(),'merge-audit-control-'));try{cpSync(current!,dir,{recursive:true});const path=join(dir,target),line=readFileSync(path,'utf8').split('\n').find(s=>s.startsWith('CANDIDATE_RECEIPT '))!,envelope=JSON.parse(line.slice(18)),data=JSON.parse(gunzipSync(Buffer.from(envelope.gzipBase64,'base64')).toString());mutate(data);const bytes=gzipSync(JSON.stringify(data));envelope.source=data.source;envelope.sha256=createHash('sha256').update(bytes).digest('hex');envelope.gzipBase64=bytes.toString('base64');writeFileSync(path,'CANDIDATE_RECEIPT '+JSON.stringify(envelope)+'\n');const result=run(dir);a.notEqual(result.status,0,name);console.log('MERGE_AUDIT_CONTROL '+JSON.stringify({name,exit:result.status}))}finally{rmSync(dir,{recursive:true,force:true})}}
console.log('MERGE_AUDIT_CONTROLS '+JSON.stringify({source,positive:true,rejected:mutations.length}))
