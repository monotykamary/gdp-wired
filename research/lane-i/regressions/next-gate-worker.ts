// Exact-source preflight. Each invocation owns its restored trees and bounded children.
import {readFileSync,mkdirSync,mkdtempSync,copyFileSync,rmSync,existsSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {createHash} from 'node:crypto'
import {gzipSync,gunzipSync} from 'node:zlib'
import {runResourceMeasured} from './resource-run.ts'
const sha=(v:string|Uint8Array)=>createHash('sha256').update(v).digest('hex')
const hashes:Record<string,string>=JSON.parse(readFileSync('checksums.json','utf8'))
for(const [p,h]of Object.entries(hashes))if(sha(readFileSync(p))!==h)throw Error('changed input '+p)
const config=JSON.parse(readFileSync('gate-inputs/gate.json','utf8')),mode=process.argv[2]
console.log('NEXT_INPUT '+JSON.stringify({mode,manifest:sha(readFileSync('checksums.json')),config,bun:process.versions.bun}))
if(mode==='verify')process.exit(0)
const {restore,command,harnessHashes}=await import(resolve('research/verify-all/final-gate-common.ts'))
const temp=mkdtempSync('/tmp/lane-i-next-'),roots:string[]=[]
async function root(side:'base'|'candidate'){
 const rev=side==='base'?config.baseline:config.candidate,dir=join(temp,side),meta=restore(resolve('gate-inputs'),dir,rev)
 roots.push(dir)
 const source=Object.fromEntries(Object.keys(config.sources[side]).map(p=>[p,sha(readFileSync(join(dir,p)))]))
 if(JSON.stringify(source)!==JSON.stringify(config.sources[side]))throw Error('source hash mismatch '+side)
 const harness=harnessHashes(dir)
 if(JSON.stringify(harness)!==JSON.stringify(config.originalHarness))throw Error('canonical models/harness differ from original '+side)
 console.log('NEXT_SOURCE '+JSON.stringify({side,meta,source,harness,bun:command('bun',['--version']),cpu:readFileSync('/proc/cpuinfo','utf8').match(/^model name\s*:\s*(.+)$/m)?.[1]}))
 command('bun',['install','--frozen-lockfile'],dir)
 return dir
}
async function run(dir:string,args:string[],seconds:number,label:string,required=true){
 const r=await runResourceMeasured('bun',args,dir,label,seconds)
 console.log('NEXT_STEP '+JSON.stringify({label,args,seconds,exit:r.status,signal:r.signal,error:r.error?.message,wallMs:r.wallMs,resources:r.resources,stdoutSha256:sha(r.stdout),stderrSha256:sha(r.stderr),traceGzipBase64:gzipSync(r.stdout+'\n---stderr---\n'+r.stderr).toString('base64'),stderrTail:r.stderr.slice(-5000)}))
 if(required&&r.status!==0)throw Error(label+' exit '+r.status+' '+r.signal)
 return r
}
try{
 if(mode==='effect'){
  const repeat=Number(process.argv[3]),kind=process.argv[4]
  if(!Number.isInteger(repeat)||repeat<1||repeat>3||!['isolated','full'].includes(kind??''))throw Error('invalid effect pair')
  const dirs={base:await root('base'),candidate:await root('candidate')},outcomes:Record<string,unknown>={},order=repeat%2?['candidate','base']as const:['base','candidate']as const
  let failed=false
  for(const side of order){
   const args=['test','./core/effect-queue.test.ts',...(kind==='isolated'?['--test-name-pattern','the CLI on the pool']:[])]
   const r=await run(dirs[side],args,1200,`effect-${kind}-${repeat}-${side}`,false)
   outcomes[side]={exit:r.status,wallMs:r.wallMs};if(r.status!==0)failed=true
  }
  console.log('NEXT_EFFECT '+JSON.stringify({repeat,kind,order,outcomes}))
  if(failed)throw Error('effect pair contains a failed native test')
 }else if(mode==='binder'){
  for(const side of ['base','candidate']as const){const dir=await root(side);copyFileSync('regression-driver/symbolic-binder-probe.ts',join(dir,'symbolic-binder-probe.ts'))
   const r=await run(dir,['symbolic-binder-probe.ts'],60,'binder-'+side)
   const rows=r.stdout.split('\n').filter(l=>l.startsWith('SYMBOLIC_BINDER_CASE ')).map(l=>JSON.parse(l.slice(21)))
   if(rows.length!==3||rows.find(x=>x.name==='generated')?.checked!==true||rows.find(x=>x.name==='explicit-symbolic')?.checked!==true||rows.find(x=>x.name==='explicit-constant')?.tree!==false)throw Error('binder controls failed '+side)
  }
 }else{
  const dir=await root('candidate')
  if(mode==='check')await run(dir,['run','check'],300,'type-lint')
  else if(mode==='tests'){
   for(const file of config.newTests)if(!existsSync(join(dir,file)))throw Error('missing targeted test '+file)
   await run(dir,['test',...config.newTests],600,'new-tests')
  }
  else if(mode==='shard'){
   const n=Number(process.argv[3]);if(!Number.isInteger(n)||n<1||n>7)throw Error('invalid shard')
   await run(dir,['scripts/test-shards.ts','--shard',n+'/7'],1200,'shard-'+n)
  }else if(mode==='evidence'){
   command('cp',['-a',resolve('evidence-input'),join(dir,'evidence-input')])
   await run(dir,['test','research/lane-i/regressions/p1-scheduling-audit.test.ts','research/lane-i/regressions/resource-run.test.ts'],120,'audit-refusals')
   const a=join(dir,'evidence-input/confirmation/audit.json'),b=join(dir,'evidence-input/timeouts/audit.json'),before=[sha(readFileSync(a)),sha(readFileSync(b))]
   await run(dir,['research/lane-i/regressions/p1-confirm-audit.ts','evidence-input/confirmation','evidence-input/family.json'],120,'p1-confirm-audit')
   await run(dir,['research/lane-i/regressions/timeout-pairs-audit.ts','evidence-input/timeouts'],120,'timeout-pairs-audit')
   if(JSON.stringify(before)!==JSON.stringify([sha(readFileSync(a)),sha(readFileSync(b))]))throw Error('audit outputs changed')
  }else if(mode==='p1'){
   mkdirSync(join(dir,'research/lane-i-fastloop'),{recursive:true})
   for(const f of ['lane-b-cost.ts','audit-lane-b-cost.ts','check-cost-profile.ts'])copyFileSync('regression-driver/p1-tools/'+f,join(dir,'research/lane-i-fastloop',f))
   const family=resolve('evidence-input/family.json')
   process.env.LANE_B_PASS_ORDER='count-first';process.env.LANE_B_EARLY_FOCUS='off'
   for(let repeat=1;repeat<=3;repeat++){
    const out=join(temp,'p1-'+repeat);mkdirSync(out)
    await run(dir,['research/lane-i-fastloop/lane-b-cost.ts',family,'p1',out,'6000','7000'],25,'p1-'+repeat)
    const summary=JSON.parse(readFileSync(join(out,'summary.json'),'utf8'))
    const audit=await run(dir,['research/lane-i-fastloop/audit-lane-b-cost.ts',join(out,'capture.json.gz'),family],30,'p1-replay-'+repeat)
    const checked=JSON.parse(audit.stdout),capture=JSON.parse(gunzipSync(readFileSync(join(out,'capture.json.gz'))).toString());delete capture.captures
    console.log('NEXT_P1 '+JSON.stringify({repeat,summary,checked,proofGzipBase64:gzipSync(JSON.stringify(capture)).toString('base64'),familySha256:sha(readFileSync(family))}))
    if(!summary.checked||!summary.withinDiagnosticLine||!checked.checked||!checked.familyVerified||Math.abs(summary.units-1152.3382236)>1e-6)throw Error('p1 cost/replay regression')
    process.env.GDP_INFER_TRACE='2';process.env.GDP_COUNTS_TRACE='3'
    const whole=await run(dir,['research/protocols/ic3syn/run.ts','--ms','60000','--only','paxos_epr','--skip','broken'],60,'whole-paxos-'+repeat)
    const rows=whole.stdout.split('\n').flatMap(l=>{try{return[JSON.parse(l)]}catch{return[]}}).filter(x=>x.id==='paxos_epr')
    console.log('NEXT_PAXOS '+JSON.stringify({repeat,rows}))
    if(rows.length!==1||rows[0].search?.verdict!=='proven'||rows[0].search.work!==6915544||rows[0].search.full!==1037946)throw Error('whole-Paxos work regression')
   }
  }else throw Error('unknown mode')
 }
 console.log('NEXT_PASS '+JSON.stringify({mode,baseline:config.baseline,candidate:config.candidate}))
}finally{
 for(const dir of roots){const tracked=command('git',['status','--porcelain','--untracked-files=no'],dir);console.log('NEXT_CLEAN '+JSON.stringify({dir,tracked}));if(tracked)throw Error('tracked source changed during qualification')}
 rmSync(temp,{recursive:true,force:true})
}
