// Disposable single-condition hypothesis test; not the ordinary strict cohort.
import {mkdtempSync,readFileSync,writeFileSync,rmSync} from 'node:fs'
import {resolve,join} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {gzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const {restore,command,harnessHashes}=await import(resolve('research/verify-all/final-gate-common.ts'))
const group=Number(process.argv[2]),mode=process.argv[3],input=resolve('bisect-input'),config={...JSON.parse(readFileSync(join(input,'gate.json'),'utf8')),candidate:'1fc01c10f4fe5ee71101639cca55c5da39c3e10c'},temp=mkdtempSync(join(tmpdir(),'lane-i-guard-probe-'))
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim(),digest=(s:string)=>createHash('sha256').update(s).digest('hex')
try{
 const dirs={base:join(temp,'base'),candidate:join(temp,'candidate')},meta={base:restore(input,dirs.base,config.baseline),candidate:restore(input,dirs.candidate,config.candidate)},hashes={base:harnessHashes(dirs.base),candidate:harnessHashes(dirs.candidate)}
 const preload=['phase-preload.ts','cache-preload.ts','law-preload.ts'].map(file=>readFileSync(resolve('regression-driver',file),'utf8')).join('\n')
 for(const side of ['base','candidate'] as const){command('bun',['install','--frozen-lockfile'],dirs[side]);writeFileSync(join(dirs[side],'.lane-i-guard.ts'),preload)}
 const relative=mode==='completion-off'?'core/counts.ts':mode==='inclusions-off'?'core/count-recovery/member-inclusions.ts':undefined
 if(!relative)throw new Error('unknown ablation mode')
 const file=join(dirs.candidate,relative),original=readFileSync(file,'utf8')
 const anchor=mode==='completion-off'?"if (!pass || countCompleted) return false":original.match(/^export function memberInclusions\([^\n]+\)\s*:\s*MemberInclusion\[\]\s*\{/m)?.[0]
 if(!anchor||original.split(anchor).length!==2)throw new Error('ablation anchor must match once')
 const guarded=original.replace(anchor,mode==='completion-off'?"if (true || !pass || countCompleted) return false":anchor+'\n if (true) return []'),patch={file:relative,before:digest(original),after:digest(guarded),anchor,mode}
 const variants=[{name:'base',side:'base',guard:false},{name:'candidate',side:'candidate',guard:false},{name:'candidate-ablation',side:'candidate',guard:true}] as const
 for(let repeat=1;repeat<=2;repeat++){
  const shift=(group+repeat)%variants.length,order=[...variants.slice(shift),...variants.slice(0,shift)],outcomes:Record<string,unknown>={}
  for(const variant of order){
   writeFileSync(file,variant.guard?guarded:original)
   const start=performance.now(),run=spawnSync('timeout',['-s','KILL','60','bun','--preload','./.lane-i-guard.ts','research/protocols/ic3syn/run.ts','--ms','60000','--only','consensus_forall','--skip','broken'],{cwd:dirs[variant.side],encoding:'utf8',timeout:65000,maxBuffer:64*1024*1024,env:{...process.env,CI:'1',GIT_TERMINAL_PROMPT:'0',GDP_INFER_TRACE:'2',GDP_COUNTS_TRACE:'3'}}),wallMs=performance.now()-start,stdout=run.stdout??'',stderr=run.stderr??''
   const results=stdout.split('\n').flatMap(line=>{try{const row=JSON.parse(line);return row.id==='consensus_forall'?[row]:[]}catch{return[]}}),records=(prefix:string)=>stderr.split('\n').filter(line=>line.startsWith(prefix)).map(line=>JSON.parse(line.slice(prefix.length)))
   outcomes[variant.name]={side:variant.side,guard:variant.guard,exit:run.status,signal:run.signal,error:run.error?.message,wallMs,results,profile:records('LANE_I_PROFILE '),lawEvents:records('LANE_I_LAW '),cache:records('LANE_I_CACHE '),stdoutSha256:digest(stdout),stderrSha256:digest(stderr),traceGzipBase64:gzipSync(Buffer.from(stdout+'\n---stderr---\n'+stderr)).toString('base64')}
  }
  writeFileSync(file,original)
  console.log('FIRST_B_ABLATION '+JSON.stringify({group,repeat,mode,cpu,order:order.map(row=>row.name),strictMs:60000,meta,hashes,patch,outcomes}))
 }
}finally{rmSync(temp,{recursive:true,force:true})}
