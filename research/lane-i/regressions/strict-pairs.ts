// Exact b09/main paired strict replay. Nonmatching CPUs do no experiment.
import {mkdtempSync,readFileSync,writeFileSync,rmSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {gzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const group=Number(process.argv[2]),repeats=Number(process.argv[3]??3)
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim()
if(cpu!=='AMD Ryzen 9 9950X 16-Core Processor') { console.log('STRICT_CPU_SKIP '+JSON.stringify({group,cpu}));process.exit(0) }
const {restore,command,harnessHashes}=await import(resolve('research/verify-all/final-gate-common.ts'))
const input=resolve('gate-inputs'),config=JSON.parse(readFileSync(join(input,'gate.json'),'utf8'))
const temp=mkdtempSync(join(tmpdir(),'lane-i-strict-'))
const digest=(s:string)=>createHash('sha256').update(s).digest('hex')
try {
  const dirs={base:join(temp,'base'),candidate:join(temp,'candidate')}
  const meta={base:restore(input,dirs.base,config.baseline),candidate:restore(input,dirs.candidate,config.candidate)}
  const hashes={base:harnessHashes(dirs.base),candidate:harnessHashes(dirs.candidate)}
  for(const side of ['base','candidate'] as const){command('bun',['install','--frozen-lockfile'],dirs[side]);writeFileSync(join(dirs[side],'.lane-i-phase.ts'),readFileSync(resolve('regression-driver/phase-preload.ts')))}
  for(let repeat=1;repeat<=repeats;repeat++){
    const order=(group+repeat)%2?['candidate','base'] as const:['base','candidate'] as const
    const outcomes:Record<string,unknown>={}
    for(const side of order){
      const args=['-s','KILL','60','bun','--preload','./.lane-i-phase.ts','research/protocols/ic3syn/run.ts','--ms','60000','--only','consensus_forall','--skip','broken']
      const start=performance.now(),run=spawnSync('timeout',args,{cwd:dirs[side],encoding:'utf8',timeout:65000,maxBuffer:64*1024*1024,env:{...process.env,CI:'1',GIT_TERMINAL_PROMPT:'0',GDP_INFER_TRACE:'2',GDP_COUNTS_TRACE:'3'}}),wallMs=performance.now()-start
      const stdout=run.stdout??'',stderr=run.stderr??'',json=stdout.split('\n').flatMap(line=>{try{const row=JSON.parse(line);return row.id==='consensus_forall'?[row]:[]}catch{return[]}})
      const profile=stderr.split('\n').filter(line=>line.startsWith('LANE_I_PROFILE ')).map(line=>JSON.parse(line.slice(15)))
      const finish=profile.find(row=>row.event==='result'),candidates=profile.find(row=>row.event==='candidates'),first=profile.find(row=>row.event==='first-attempt-return')
      const zero=finish?.at-finish?.searchMs
      const attempts=[...stderr.matchAll(/counts: try (.*?) \| ls (\d+) pass ([01]) ms (\d+) took (\d+) wall (\d+) \[(.*?)\] -> (.*)/g)].map(m=>({law:m[1],family:Number(m[2]),pass:Number(m[3]),allowance:Number(m[4]),units:Number(m[5]),wallMs:Number(m[6]),outcome:m[8]}))
      const phases=stderr.split('\n').filter(line=>line.startsWith('[infer] ')||line.startsWith('counts: finite result '))
      outcomes[side]={exit:run.status,signal:run.signal,error:run.error?.message,wallMs,results:json,generationWallMs:candidates&&Number.isFinite(zero)?candidates.at-zero:null,preAttemptWallMs:first&&Number.isFinite(zero)?first.at-first.attemptWallMs-zero:null,profile,attempts,phases,stdoutSha256:digest(stdout),stderrSha256:digest(stderr),traceGzipBase64:gzipSync(Buffer.from(stdout+'\n---stderr---\n'+stderr)).toString('base64')}
    }
    console.log('STRICT_PAIR '+JSON.stringify({group,repeat,cpu,strictMs:60000,order,meta,hashes,outcomes}))
  }
} finally {rmSync(temp,{recursive:true,force:true})}
