// Exact historical-source, same-CPU paired bisection. Trace patches only observe public attempts.
import {mkdtempSync,readFileSync,writeFileSync,rmSync} from 'node:fs'
import {resolve,join} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {gzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const revision=process.argv[2]!,replica=Number(process.argv[3]),repeats=Number(process.argv[4]??5)
const cohort=process.argv.includes('--cohort')
if(!/^[a-f0-9]{40}$/.test(revision)||!Number.isInteger(repeats)||repeats<1||(!cohort&&repeats<5))throw new Error('exact revision and five repeats, or one explicit cohort repeat, required')
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim()
if(cpu!=='AMD EPYC 9455 48-Core Processor'){console.log('BISECT_CPU_SKIP '+JSON.stringify({revision,replica,cpu}));process.exit(0)}
const {restore,command,harnessHashes}=await import(resolve('research/verify-all/final-gate-common.ts'))
const input=resolve('paxos-input'),baseline=JSON.parse(readFileSync(join(input,'gate.json'),'utf8')).baseline,temp=mkdtempSync(join(tmpdir(),'lane-i-bisect-')),digest=(s:string)=>createHash('sha256').update(s).digest('hex')
const anchor='return {traced, get counted()'
const observe=`const __laneTrace = (...args: Parameters<typeof traced>): ReturnType<typeof traced> => {
 const w=__laneWork.n,f=__laneFull(),t=clock(),s=performance.now(),p={...cprof}
 let r: ReturnType<typeof traced> | undefined
 try { return r=traced(...args) } finally {
  console.error('BISECT_LAW '+JSON.stringify({law:args[0].name,family:args[1].length,pass:args[2],allowance:args[3],at:s,wallMs:performance.now()-s,units:clock()-t,work:__laneWork.n-w,full:__laneFull()-f,outcome:r?('proof' in r?'kept':r.stuck):'throw',profile:Object.fromEntries(Object.entries(cprof).map(([k,v])=>[k,v-(p[k]??0)]).filter(([,v])=>v))}))
 }
}
return {traced:__laneTrace, get counted()`
const records:unknown[]=[],traces:unknown[]=[]
try{
 const dirs={base:join(temp,'base'),candidate:join(temp,'candidate')},meta={base:restore(input,dirs.base,baseline),candidate:restore(input,dirs.candidate,revision)},hashes={base:harnessHashes(dirs.base),candidate:harnessHashes(dirs.candidate)},patches:Record<string,unknown>={}
 for(const side of ['base','candidate'] as const){
  command('bun',['install','--frozen-lockfile'],dirs[side])
  const path=join(dirs[side],'core/counts.ts'),source=readFileSync(path,'utf8')
  if(source.split(anchor).length!==2)throw new Error('public attempt trace anchor must match once: '+side)
  const changed="import {work as __laneWork} from './solver.ts'\nimport {fullWork as __laneFull} from '../kernel/prove.ts'\n"+source.replace(anchor,observe)
  writeFileSync(path,changed);writeFileSync(join(dirs[side],'.lane-i-phase.ts'),readFileSync(resolve('regression-driver/phase-preload.ts')))
  patches[side]={file:'core/counts.ts',before:digest(source),after:digest(changed),kind:'observation-only public traced wrapper',kernelUnchanged:true}
 }
 for(let repeat=1;repeat<=repeats;repeat++){
  const order=(replica+repeat)%2?['candidate','base'] as const:['base','candidate'] as const,outcomes:Record<string,unknown>={}
  for(const side of order){
   const start=performance.now(),run=spawnSync('timeout',['-s','KILL','60','bun','--preload','./.lane-i-phase.ts','research/protocols/ic3syn/run.ts','--ms','60000','--only','paxos_epr','--skip','broken'],{cwd:dirs[side],encoding:'utf8',timeout:65000,maxBuffer:64*1024*1024,env:{...process.env,CI:'1',GIT_TERMINAL_PROMPT:'0',GDP_INFER_TRACE:'2',GDP_COUNTS_TRACE:'3'}}),wallMs=performance.now()-start,stdout=run.stdout??'',stderr=run.stderr??''
   const json=(text:string,prefix='')=>text.split('\n').flatMap(line=>{if(prefix&&!line.startsWith(prefix))return[];try{return[JSON.parse(line.slice(prefix.length))]}catch{return[]}})
   const results=json(stdout).filter(row=>row.id==='paxos_epr'),profile=json(stderr,'LANE_I_PROFILE '),attempts=json(stderr,'BISECT_LAW '),finish=profile.find(row=>row.event==='result'),generation=profile.find(row=>row.event==='candidates'),zero=finish?finish.at-finish.searchMs:undefined
   outcomes[side]={exit:run.status,signal:run.signal,error:run.error?.message,wallMs,results,profile,attempts,generationWallMs:generation&&zero!==undefined?generation.at-zero:null,finitePassMs:generation?.profile?.finiteHoudini??0,finitePassPresent:generation?.profile?.finiteHoudini!==undefined,preProverWallMs:attempts.length&&zero!==undefined?attempts[0].at-zero:null,stdoutSha256:digest(stdout),stderrSha256:digest(stderr)}
   traces.push({repeat,side,stdout,stderr})
  }
  records.push({repeat,order,outcomes});console.log('BISECT_PROGRESS '+JSON.stringify({revision,replica,repeat,cpu}))
 }
 const trace=JSON.stringify(traces),summary=JSON.stringify({revision,baseline,replica,repeats,cohort,cpu,bun:command('bun',['--version']).trim(),strictMs:60000,meta,hashes,patches,records,traceSha256:digest(trace)})
 console.log('BISECT_TRACES_GZIP '+gzipSync(trace).toString('base64'))
 const encoded=gzipSync(summary).toString('base64');if(encoded.length>350000)throw new Error('summary exceeds safe collector tail')
 console.log('BISECT_SUMMARY_GZIP '+encoded)
}finally{rmSync(temp,{recursive:true,force:true})}
