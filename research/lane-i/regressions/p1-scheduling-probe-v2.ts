// Exact frozen-family comparison. Experimental policies modify only disposable counts.ts.
import {readFileSync,writeFileSync,mkdirSync,mkdtempSync,rmSync,copyFileSync} from 'node:fs'
import {resolve,join} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gunzipSync,gzipSync,brotliCompressSync,constants} from 'node:zlib'
const sha=(bytes:string|Uint8Array)=>createHash('sha256').update(bytes).digest('hex')
const expected:Record<string,string>=JSON.parse(readFileSync('frozen-paxos/checksums.json','utf8'))
for(const [path,hash]of Object.entries(expected))if(sha(readFileSync(path))!==hash)throw Error('input hash mismatch: '+path)
const {restore,command}=await import(resolve('research/verify-all/final-gate-common.ts'))
const input=resolve('paxos-input'),data=resolve('p1-input'),config=JSON.parse(readFileSync(join(data,'config.json'),'utf8')),temp=mkdtempSync('/tmp/lane-i-p1-scheduling-')
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim(),records:any[]=[],sources:any[]=[],whole:any[]=[]
let archived=false
const familyHashes={p1:sha(readFileSync(join(data,'family.json'))),paxos:sha(readFileSync(join(data,'paxos-family.json')))}
if(familyHashes.p1!==config.p1Sha256||familyHashes.paxos!==config.paxosSha256)throw Error('frozen family mismatch')
const run=(cwd:string,args:string[],timeout=30000,env:Record<string,string>={})=>{const r=spawnSync('bun',args,{cwd,encoding:'utf8',timeout,maxBuffer:32*1024*1024,env:{...process.env,...env}});return{exit:r.status,signal:r.signal,error:r.error?.message,stdout:r.stdout??'',stderr:r.stderr??''}}
const tools=['lane-b-cost.ts','audit-lane-b-cost.ts','check-cost-profile.ts','paxos-frozen-attempt.ts','paxos-proof-replay.ts']
try{
 for(const name of ['control','current','guarded']as const){
  const revision=name==='control'?config.control:config.candidate,dir=join(temp,name),meta=restore(input,dir,revision)
  mkdirSync(join(dir,'research/lane-i-fastloop'),{recursive:true})
  for(const file of tools)copyFileSync(resolve('regression-driver/p1-tools',file),join(dir,'research/lane-i-fastloop',file))
  command('bun',['install','--frozen-lockfile'],dir)
  const file=join(dir,'core/counts.ts'),before=readFileSync(file,'utf8')
  if(sha(before)!==(name==='control'?config.controlCounts:config.candidateCounts))throw Error('core source mismatch: '+name)
  let after=before
  if(name==='guarded'){
   const anchor='    // Try the sparse obligations first: eager completion can crowd out an easy proof.\n    // Stuck-model paths below retain bounded completion for requested count maps.'
   if(before.split(anchor).length!==2)throw Error('non-unique experimental anchor')
   after=before.replace(anchor,anchor+'\n    // Experimental: unary, single-key priority requires a separate relevant count premise.\n    if (pass && completionMaps.size && !law.keys?.length && [...completionMaps].every(map => !m.counts![map]!.lo) && modelLaws.some(other => other.name !== law.name && reads(other.holds, map => completionMaps.has(map)).size)) completeCounts()')
   writeFileSync(file,after)
  }
  const kernelHashes=Object.fromEntries(['kernel/prove.ts','kernel/kernel.ts','core/solver.ts'].map(file=>[file,sha(readFileSync(join(dir,file)))]))
  sources.push({name,revision,meta,dir,countsBefore:sha(before),countsAfter:sha(after),kernelHashes,experimental:name==='guarded'})
 }
 if(sources.some(source=>JSON.stringify(source.kernelHashes)!==JSON.stringify(sources[0].kernelHashes)))throw Error('checker/solver implementations differ')
 for(let repeat=1;repeat<=3;repeat++)for(const index of [0,1,2]){
  const source=sources[(index+repeat-1)%3],dir=source.dir,out=join(temp,`r${repeat}-${source.name}`);mkdirSync(out)
  const p1=run(dir,['research/lane-i-fastloop/lane-b-cost.ts',join(data,'family.json'),'p1',out,'6000','7000'],25000,{LANE_B_PASS_ORDER:'count-first',LANE_B_EARLY_FOCUS:'off'})
  if(p1.exit!==0)throw Error('p1 driver failed: '+source.name+' '+p1.stderr)
  const summary=JSON.parse(readFileSync(join(out,'summary.json'),'utf8')),capture=JSON.parse(gunzipSync(readFileSync(join(out,'capture.json.gz'))).toString())
  const audit=run(dir,['research/lane-i-fastloop/audit-lane-b-cost.ts',join(out,'capture.json.gz'),join(data,'family.json')])
  if(audit.exit!==0)throw Error('independent p1 replay failed: '+audit.stderr)
  const paxos=run(dir,['research/lane-i-fastloop/paxos-frozen-attempt.ts',join(data,'paxos-family.json'),source.name])
  if(paxos.exit!==0)throw Error('Paxos driver failed: '+paxos.stderr)
  const lines=paxos.stdout.split('\n'),traceLine=lines.find(line=>line.startsWith('PAXOS_ATTEMPT '))
  if(!traceLine)throw Error('missing frozen Paxos trace')
  const trace=JSON.parse(traceLine.slice(14)),proofLine=lines.find(line=>line.startsWith('PAXOS_PROOF_GZIP_BASE64 '));let paxosAudit:any=null
  if(proofLine){const file=join(out,'paxos-proof.json.gz');writeFileSync(file,Buffer.from(proofLine.slice(24),'base64'));paxosAudit=run(dir,['research/lane-i-fastloop/paxos-proof-replay.ts',join(data,'paxos-family.json'),file]);if(paxosAudit.exit!==0)throw Error('fresh Paxos replay failed: '+paxosAudit.stderr)}
  const {captures:_captures,...compactCapture}=capture
  records.push({repeat,source:source.name,revision:source.revision,p1:{summary,audit,compactCaptureGzip:gzipSync(JSON.stringify(compactCapture)).toString('base64')},paxos:{trace,audit:paxosAudit,proofGzip:proofLine?.slice(24)}})
  console.log('P1_SCHEDULING_PROGRESS '+JSON.stringify({repeat,source:source.name,p1:{checked:summary.checked,units:summary.units},paxos:{outcome:trace.outcome,solver:trace.solver}}))
 }
 for(const name of ['current','guarded']){
  const source=sources.find(row=>row.name===name),file=join(source.dir,'core/counts.ts'),plain=readFileSync(file,'utf8'),anchor='return {traced, get counted()'
  const wrapper=`const observed = (...args: Parameters<typeof traced>): ReturnType<typeof traced> => {
 const w=phaseWork.n,f=phaseFull(); let result:ReturnType<typeof traced>|undefined
 try { return result=traced(...args) } finally { console.error('P1_PHASE '+JSON.stringify({law:args[0].name,pass:args[2],family:args[1].length,work:phaseWork.n-w,full:phaseFull()-f,outcome:result?('proof'in result?'proof':result.stuck):'throw'})) }
}
return {traced:observed, get counted()`
  if(plain.split(anchor).length!==2)throw Error('phase wrapper anchor')
  const changed="import {work as phaseWork} from './solver.ts'\nimport {fullWork as phaseFull} from '../kernel/prove.ts'\n"+plain.replace(anchor,wrapper)
  writeFileSync(file,changed)
  const phasePatch={before:sha(plain),after:sha(changed),kind:'observation-only traced wrapper'}
  const child=spawnSync('timeout',['-s','KILL','60','bun','research/protocols/ic3syn/run.ts','--ms','60000','--only','paxos_epr','--skip','broken'],{cwd:source.dir,encoding:'utf8',timeout:65000,maxBuffer:32*1024*1024,env:{...process.env,GDP_INFER_TRACE:'2',GDP_COUNTS_TRACE:'3'}}),r={exit:child.status,signal:child.signal,error:child.error?.message,stdout:child.stdout??'',stderr:child.stderr??''}
  const results=r.stdout.split('\n').flatMap(line=>{try{return[JSON.parse(line)]}catch{return[]}}).filter(row=>row.id==='paxos_epr')
  whole.push({source:name,phasePatch,...r,results})
  console.log('P1_SCHEDULING_WHOLE '+JSON.stringify({source:name,exit:r.exit,results}))
 }
 const result={config,cpu,familyHashes,inputManifestSha256:sha(readFileSync('frozen-paxos/checksums.json')),driverSha256:sha(readFileSync('regression-driver/p1-scheduling-probe-v2.ts')),sources:sources.map(({dir:_dir,...source})=>source),records,whole,scope:'Conditional frozen-family costs plus one whole-Paxos screening run; not a final gate.'},packed=brotliCompressSync(Buffer.from(JSON.stringify(result)),{params:{[constants.BROTLI_PARAM_QUALITY]:8}}),encoded=packed.toString('base64')
 writeFileSync(join(temp,'result.json.br'),packed)
 console.log('P1_SCHEDULING_ARCHIVE '+JSON.stringify({path:join(temp,'result.json.br'),sha256:sha(packed),encodedBytes:encoded.length}))
 if(encoded.length>350000)throw Error('receipt exceeds collector-safe tail')
 console.log('P1_SCHEDULING_RESULT_BR '+encoded)
 archived=true
}finally{if(archived)rmSync(temp,{recursive:true,force:true});else console.error('P1_SCHEDULING_RECOVERY '+temp)}
