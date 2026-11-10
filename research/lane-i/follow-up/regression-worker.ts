import{readFileSync,copyFileSync,mkdtempSync,rmSync}from'node:fs'
import{join,resolve}from'node:path'
import{createHash}from'node:crypto'
import{gzipSync}from'node:zlib'
import{runResourceMeasured}from'./resource-run.ts'
const sha=(v:string|Uint8Array)=>createHash('sha256').update(v).digest('hex'),mode=process.argv[2],name=process.argv[3],cpu=readFileSync('/proc/cpuinfo','utf8').match(/^model name\s*:\s*(.+)$/m)?.[1]?.trim(),epyc='AMD EPYC 4585PX 16-Core Processor',allowed=['two-phase-epyc','two-phase-other','two-phase-any','infer','sums']
if(!mode||!name||!allowed.includes(mode)||!cpu)throw Error('mode, name and CPU required')
const eligible=mode==='two-phase-epyc'?cpu===epyc:mode==='two-phase-other'?cpu!==epyc:true
console.log('REGRESSION_ADMISSION '+JSON.stringify({name,mode,cpu,eligible,bun:Bun.version,affinity:readFileSync('/proc/self/status','utf8').match(/^Cpus_allowed_list:\s*(.+)$/m)?.[1]}))
if(!eligible){console.log('REGRESSION_CPU_SKIP '+JSON.stringify({name,mode,cpu,reason:'not requested CPU cohort; no test or proof attempted'}));process.exit(0)}
const hashes=JSON.parse(readFileSync('checksums.json','utf8')),extra=JSON.parse(readFileSync('regression.json','utf8')),cfg=JSON.parse(readFileSync('config.json','utf8'))
for(const[p,h]of Object.entries({...hashes,...extra.hashes}))if(sha(readFileSync(p))!==h)throw Error('input hash mismatch '+p)
const{restore,command}=await import(resolve('research/verify-all/final-gate-common.ts')),temp=mkdtempSync('/tmp/a8-regression-'),dirs:Record<string,string>={},pairs:any[]=[]
const output=console.log;console.log=(...args:unknown[])=>{if(typeof args[0]==='string'&&args[0].startsWith('BAR_RESOURCE_'))return;output(...args)}
try{
 for(const side of ['base','candidate']){const dir=join(temp,side),meta=restore(resolve('gate-inputs'),dir,cfg.revisions[side]);dirs[side]=dir
  const sources=Object.fromEntries(Object.keys(extra.sources[side]).map(p=>[p,sha(readFileSync(join(dir,p)))]));if(JSON.stringify(sources)!==JSON.stringify(extra.sources[side]))throw Error('source mismatch '+side)
  console.log('REGRESSION_SOURCE '+JSON.stringify({name,mode,side,revision:cfg.revisions[side],meta,sources,cpu,bun:Bun.version}))
  command('bun',['install','--frozen-lockfile'],dir)
  if(mode.startsWith('two-phase'))copyFileSync('phase-preload.ts',join(dir,'regression-phase-preload.ts'))
 }
 for(let repeat=1;repeat<=5;repeat++){
  const order=repeat%2?['candidate','base']:['base','candidate'],outcomes:Record<string,any>={}
  for(const side of order){const currentCpu=readFileSync('/proc/cpuinfo','utf8').match(/^model name\s*:\s*(.+)$/m)?.[1]?.trim();if(currentCpu!==cpu)throw Error('CPU changed')
   const args=mode.startsWith('two-phase')?['--preload','./regression-phase-preload.ts','research/protocols/ic3syn/run.ts','--ms','60000','--only','two_phase_commit','--skip','broken']:mode==='infer'?['test','./core/infer.test.ts','--test-name-pattern','an invariant over four values']:['test','./core/sums.test.ts']
   const r=await runResourceMeasured('bun',args,dirs[side]!,`${name}-${repeat}-${side}`,mode.startsWith('two-phase')?90:120),lines=r.stdout.split('\n'),json=lines.flatMap(l=>{try{return[JSON.parse(l)]}catch{return[]}}),protocol=json.find(x=>x.id==='two_phase_commit'),phaseLine=lines.find(l=>l.startsWith('REGRESSION_PHASE ')),phases=phaseLine?JSON.parse(phaseLine.slice('REGRESSION_PHASE '.length)):null,passed=r.status===0&&(mode.startsWith('two-phase')?protocol?.search?.verdict==='proven':true)
   const record={name,mode,repeat,side,revision:cfg.revisions[side],cpu,args,exit:r.status,signal:r.signal,wallMs:r.wallMs,passed,protocol,phases,stdoutSha256:sha(r.stdout),stderrSha256:sha(r.stderr),traceGzipBase64:gzipSync(r.stdout+'\n---stderr---\n'+r.stderr).toString('base64'),resourcesGzipBase64:gzipSync(JSON.stringify(r.resources)).toString('base64')}
   console.log('REGRESSION_RUN '+JSON.stringify(record));outcomes[side]={exit:r.status,passed,wallMs:r.wallMs,root:protocol?.search,phases}
  }
  const pair={name,mode,repeat,order,cpu,outcomes,candidateOnlyLoss:outcomes.base.passed&&!outcomes.candidate.passed};pairs.push(pair);console.log('REGRESSION_PAIR '+JSON.stringify(pair))
 }
 for(const side of ['base','candidate']){const dirty=command('git',['status','--porcelain','--untracked-files=no'],dirs[side]);if(dirty)throw Error('source changed '+side);console.log('REGRESSION_CLEAN '+JSON.stringify({side,dirty}))}
 const losses=pairs.filter(p=>p.candidateOnlyLoss).map(p=>p.repeat);console.log('REGRESSION_SUMMARY '+JSON.stringify({name,mode,cpu,pairs:5,basePass:pairs.filter(p=>p.outcomes.base.passed).length,candidatePass:pairs.filter(p=>p.outcomes.candidate.passed).length,candidateOnlyLosses:losses,majorityLoss:losses.length>=3,selection:'For multiple eligible cohorts, designate lowest job-name as primary before looking at outcomes; retain every other cohort.'}))
}finally{console.log=output;rmSync(temp,{recursive:true,force:true})}
