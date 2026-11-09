// Screening ablation, not part of the ordinary ten-pair strict cohort.
// Compare both fixed sources, then b09 with its existing row-sharing switch off.
import {mkdtempSync,readFileSync,writeFileSync,rmSync} from 'node:fs'
import {resolve,join} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {gzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const {restore,command,harnessHashes}=await import(resolve('research/verify-all/final-gate-common.ts'))
const group=Number(process.argv[2]),input=resolve('gate-inputs'),config=JSON.parse(readFileSync(join(input,'gate.json'),'utf8')),temp=mkdtempSync(join(tmpdir(),'lane-i-cache-probe-'))
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim(),digest=(s:string)=>createHash('sha256').update(s).digest('hex')
try{
 const dirs={base:join(temp,'base'),candidate:join(temp,'candidate')},meta={base:restore(input,dirs.base,config.baseline),candidate:restore(input,dirs.candidate,config.candidate)},hashes={base:harnessHashes(dirs.base),candidate:harnessHashes(dirs.candidate)}
 const preload=readFileSync(resolve('regression-driver/phase-preload.ts'),'utf8')+'\n'+readFileSync(resolve('regression-driver/cache-preload.ts'),'utf8')
 for(const side of ['base','candidate'] as const){command('bun',['install','--frozen-lockfile'],dirs[side]);writeFileSync(join(dirs[side],'.lane-i-cache.ts'),preload)}
 const variants=[{name:'base',side:'base',rows:'1'},{name:'candidate',side:'candidate',rows:'1'},{name:'candidate-no-shared-rows',side:'candidate',rows:'0'}] as const
 for(let repeat=1;repeat<=2;repeat++){
  const shift=(group+repeat)%variants.length,order=[...variants.slice(shift),...variants.slice(0,shift)],outcomes:Record<string,unknown>={}
  for(const variant of order){
   const start=performance.now(),run=spawnSync('timeout',['-s','KILL','60','bun','--preload','./.lane-i-cache.ts','research/protocols/ic3syn/run.ts','--ms','60000','--only','consensus_forall','--skip','broken'],{cwd:dirs[variant.side],encoding:'utf8',timeout:65000,maxBuffer:64*1024*1024,env:{...process.env,CI:'1',GIT_TERMINAL_PROMPT:'0',GDP_INFER_TRACE:'2',GDP_COUNTS_TRACE:'3',GDP_ROWS_SHARED:variant.rows}}),wallMs=performance.now()-start,stdout=run.stdout??'',stderr=run.stderr??''
   const results=stdout.split('\n').flatMap(line=>{try{const row=JSON.parse(line);return row.id==='consensus_forall'?[row]:[]}catch{return[]}})
   const records=(prefix:string)=>stderr.split('\n').filter(line=>line.startsWith(prefix)).map(line=>JSON.parse(line.slice(prefix.length)))
   outcomes[variant.name]={side:variant.side,rowsShared:variant.rows,exit:run.status,signal:run.signal,error:run.error?.message,wallMs,results,profile:records('LANE_I_PROFILE '),cache:records('LANE_I_CACHE '),stdoutSha256:digest(stdout),stderrSha256:digest(stderr),traceGzipBase64:gzipSync(Buffer.from(stdout+'\n---stderr---\n'+stderr)).toString('base64')}
  }
  console.log('CACHE_PROBE '+JSON.stringify({group,repeat,cpu,order:order.map(row=>row.name),strictMs:60000,meta,hashes,outcomes}))
 }
}finally{rmSync(temp,{recursive:true,force:true})}
