// Five fresh-process, same-worker pairs of exact committed sources. Not a final gate.
import {readFileSync,writeFileSync,mkdtempSync,mkdirSync,copyFileSync,rmSync} from 'node:fs'
import {resolve,join} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gunzipSync,gzipSync,brotliCompressSync,constants} from 'node:zlib'
const sha=(v:string|Uint8Array)=>createHash('sha256').update(v).digest('hex'),manifest=readFileSync('frozen-paxos/checksums.json','utf8'),hashes:Record<string,string>=JSON.parse(manifest)
for(const [path,hash]of Object.entries(hashes))if(sha(readFileSync(path))!==hash)throw Error('input changed: '+path)
const config=JSON.parse(readFileSync('p1-input/config.json','utf8')),data=resolve('p1-input'),input=resolve('paxos-input'),temp=mkdtempSync('/tmp/p1-confirm-'),records:any[]=[],sources:any[]=[]
const {restore,command}=await import(resolve('research/verify-all/final-gate-common.ts'))
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim()
const run=(cwd:string,args:string[],timeout:number,env:Record<string,string>={})=>{const r=spawnSync('bun',args,{cwd,encoding:'utf8',timeout,maxBuffer:16*1024*1024,env:{...process.env,...env}});return{exit:r.status,signal:r.signal,error:r.error?.message,stdout:r.stdout??'',stderr:r.stderr??''}}
let archived=false
try{
 for(const side of ['current','fixed']as const){const revision=side==='current'?config.candidate:config.fixed,dir=join(temp,side),meta=restore(input,dir,revision)
  mkdirSync(join(dir,'research/lane-i-fastloop'),{recursive:true})
  for(const f of ['lane-b-cost.ts','audit-lane-b-cost.ts','check-cost-profile.ts'])copyFileSync(resolve('regression-driver/p1-tools',f),join(dir,'research/lane-i-fastloop',f))
  command('bun',['install','--frozen-lockfile'],dir)
  const counts=sha(readFileSync(join(dir,'core/counts.ts'))),expected=side==='current'?config.candidateCounts:config.fixedCounts
  if(counts!==expected)throw Error('count source mismatch')
  const kernel=Object.fromEntries(['kernel/prove.ts','kernel/kernel.ts','core/solver.ts','core/laws.ts'].map(p=>[p,sha(readFileSync(join(dir,p)))]))
  sources.push({side,revision,meta,dir,counts,kernel})
 }
 if(JSON.stringify(sources[0].kernel)!==JSON.stringify(sources[1].kernel))throw Error('checker or source-law change')
 for(let repeat=1;repeat<=5;repeat++)for(const side of repeat%2?['current','fixed']:['fixed','current']){
  const s=sources.find(s=>s.side===side),out=join(temp,`${repeat}-${side}`);mkdirSync(out)
  const p=run(s.dir,['research/lane-i-fastloop/lane-b-cost.ts',join(data,'family.json'),'p1',out,'6000','7000'],25000,{LANE_B_PASS_ORDER:'count-first',LANE_B_EARLY_FOCUS:'off'})
  if(p.exit!==0)throw Error('p1 process failed: '+p.stderr)
  const summary=JSON.parse(readFileSync(join(out,'summary.json'),'utf8')),capture=JSON.parse(gunzipSync(readFileSync(join(out,'capture.json.gz'))).toString());delete capture.captures
  const audit=run(s.dir,['research/lane-i-fastloop/audit-lane-b-cost.ts',join(out,'capture.json.gz'),join(data,'family.json')],30000)
  const r=spawnSync('timeout',['-s','KILL','60','bun','research/protocols/ic3syn/run.ts','--ms','60000','--only','paxos_epr','--skip','broken'],{cwd:s.dir,encoding:'utf8',timeout:65000,maxBuffer:32*1024*1024,env:{...process.env,GDP_INFER_TRACE:'2',GDP_COUNTS_TRACE:'3'}})
  const stdout=r.stdout??'',stderr=r.stderr??'',results=stdout.split('\n').flatMap(line=>{try{return[JSON.parse(line)]}catch{return[]}}).filter(row=>row.id==='paxos_epr')
  const expected=side==='current'?2046.9378360:1152.3382236,replay=JSON.parse(audit.stdout||'{}'),whole={exit:r.status,signal:r.signal,error:r.error?.message,stdout,stderr,results}
  const passed=summary.withinDiagnosticLine&&summary.checked&&audit.exit===0&&replay.checked&&Math.abs(summary.units-expected)<1e-6&&whole.exit===0&&results.length===1&&results[0].search?.verdict==='proven'&&results[0].search.work===6915544&&results[0].search.full===1037946
  records.push({repeat,side,revision:s.revision,summary,audit,proofGzip:gzipSync(JSON.stringify(capture)).toString('base64'),whole,passed})
  console.log('P1_CONFIRM_PROGRESS '+JSON.stringify({repeat,side,passed,units:summary.units,whole:results.map(row=>({verdict:row.search?.verdict,work:row.search?.work,full:row.search?.full}))}))
 }
 for(const s of sources)if(sha(readFileSync(join(s.dir,'core/counts.ts')))!==s.counts)throw Error('source mutated during measurement')
 const passed=records.length===10&&records.every(r=>r.passed),result={config,cpu,inputManifestSha256:sha(manifest),sources:sources.map(({dir:_dir,...s})=>s),records,passed,scope:'five paired exact-commit cost confirmations; not final gate'},bytes=brotliCompressSync(Buffer.from(JSON.stringify(result)),{params:{[constants.BROTLI_PARAM_QUALITY]:8}}),encoded=bytes.toString('base64')
 writeFileSync(join(temp,'result.json.br'),bytes)
 if(encoded.length>350000)throw Error('receipt too large; retained at '+temp)
 console.log('P1_CONFIRM_ARCHIVE '+JSON.stringify({sha256:sha(bytes),encodedBytes:encoded.length}))
 console.log('P1_CONFIRM_RESULT_BR '+encoded);archived=true;if(!passed)process.exitCode=1
}finally{if(archived)rmSync(temp,{recursive:true,force:true});else console.error('P1_CONFIRM_RECOVERY '+temp)}
