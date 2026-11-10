// Read-only follow-up on the gated source; no production overlays or flag changes.
import{readFileSync,mkdtempSync,mkdirSync,copyFileSync,rmSync}from'node:fs'
import{join,resolve}from'node:path'
import{createHash}from'node:crypto'
import{gzipSync,gunzipSync}from'node:zlib'
import{runResourceMeasured}from'./resource-run.ts'
const sha=(v:string|Uint8Array)=>createHash('sha256').update(v).digest('hex'),config=JSON.parse(readFileSync('config.json','utf8')),hashes:Record<string,string>=JSON.parse(readFileSync('checksums.json','utf8'))
for(const[p,h]of Object.entries(hashes))if(sha(readFileSync(p))!==h)throw Error('input hash mismatch '+p)
const kind=process.argv[2];if(kind!=='p1'&&kind!=='effect')throw Error('p1 or effect required')
const{restore,command}=await import(resolve('research/verify-all/final-gate-common.ts'))
const cpu=()=>readFileSync('/proc/cpuinfo','utf8').match(/^model name\s*:\s*(.+)$/m)?.[1]?.trim(),model=cpu(),bun=command('bun',['--version']),affinity=readFileSync('/proc/self/status','utf8').match(/^Cpus_allowed_list:\s*(.+)$/m)?.[1],temp=mkdtempSync('/tmp/a8-follow-up-'),records:any[]=[],dirs:Record<string,string>={}
const sides=kind==='p1'?['control','candidate']:['base','candidate']
async function run(side:string,args:string[],seconds:number,label:string){if(cpu()!==model)throw Error('CPU model changed');const r=await runResourceMeasured('bun',args,dirs[side]!,label,seconds);const raw={exit:r.status,signal:r.signal,wallMs:r.wallMs,resources:r.resources,stdoutSha256:sha(r.stdout),stderrSha256:sha(r.stderr),traceGzipBase64:gzipSync(r.stdout+'\n---stderr---\n'+r.stderr).toString('base64')};console.log('FOLLOW_STEP '+JSON.stringify({kind,side,args,label,...raw}));return{...r,raw}}
try{
 for(const side of sides){const dir=join(temp,side),revision=config.revisions[side],meta=restore(resolve('gate-inputs'),dir,revision);dirs[side]=dir
  const source=Object.fromEntries(Object.keys(config.sources[side]).map(p=>[p,sha(readFileSync(join(dir,p)))]));if(JSON.stringify(source)!==JSON.stringify(config.sources[side]))throw Error('source mismatch '+side)
  if(kind==='effect'&&sha(readFileSync(join(dir,'core/effect-queue.test.ts')))!==config.effectTestSha256)throw Error('effect test changed')
  console.log('FOLLOW_SOURCE '+JSON.stringify({kind,side,revision,meta,source,cpu:model,bun,affinity,manifest:sha(readFileSync('checksums.json'))}))
  command('bun',['install','--frozen-lockfile'],dir)
  if(kind==='p1'){mkdirSync(join(dir,'research/lane-i-fastloop'),{recursive:true});for(const file of ['lane-b-cost.ts','audit-lane-b-cost.ts','check-cost-profile.ts'])copyFileSync('driver/p1-tools/'+file,join(dir,'research/lane-i-fastloop',file))}
 }
 if(kind==='p1'){
  process.env.LANE_B_PASS_ORDER='count-first';process.env.LANE_B_EARLY_FOCUS='off'
  const family=resolve('family.json');if(sha(readFileSync(family))!==config.familySha256)throw Error('family changed')
  for(let repeat=1;repeat<=5;repeat++)for(const side of repeat%2?['candidate','control']:['control','candidate']){
   const out=join(temp,`p1-${repeat}-${side}`);mkdirSync(out)
   const found=await run(side,['research/lane-i-fastloop/lane-b-cost.ts',family,'p1',out,'6000','7000'],25,`p1-${repeat}-${side}`)
   if(found.status!==0)throw Error('p1 launch failed')
   const summary=JSON.parse(readFileSync(join(out,'summary.json'),'utf8')),capture=JSON.parse(gunzipSync(readFileSync(join(out,'capture.json.gz'))).toString());delete capture.captures
   const audit=await run(side,['research/lane-i-fastloop/audit-lane-b-cost.ts',join(out,'capture.json.gz'),family],30,`replay-${repeat}-${side}`),replay=audit.status===0?JSON.parse(audit.stdout):null
   const row={repeat,side,revision:config.revisions[side],summary,replay,proofGzipBase64:gzipSync(JSON.stringify(capture)).toString('base64')};records.push(row);console.log('FOLLOW_P1 '+JSON.stringify(row))
  }
  const whole:any[]=[]
  for(let repeat=1;repeat<=3;repeat++)for(const side of repeat%2?['candidate','control']:['control','candidate']){
   delete process.env.GDP_COUNTS_TRACE;delete process.env.GDP_INFER_TRACE
   const r=await run(side,['research/protocols/ic3syn/run.ts','--ms','60000','--only','paxos_epr','--skip','broken'],60,`paxos-${repeat}-${side}`),rows=r.stdout.split('\n').flatMap(l=>{try{return[JSON.parse(l)]}catch{return[]}}).filter(x=>x.id==='paxos_epr')
   const row={repeat,side,exit:r.status,rows};whole.push(row);console.log('FOLLOW_PAXOS '+JSON.stringify(row))
  }
  const checked=records.length===10&&records.every(r=>r.summary.checked&&r.summary.withinDiagnosticLine&&r.replay?.checked&&r.replay?.familyVerified),old=records.filter(r=>r.side==='control').map(r=>r.summary.units),current=records.filter(r=>r.side==='candidate').map(r=>r.summary.units),neutral=whole.filter(r=>r.side==='candidate').every(r=>r.exit===0&&r.rows.length===1&&r.rows[0].search?.verdict==='proven'&&r.rows[0].search.work===6915544&&r.rows[0].search.full===1037946)
  console.log('FOLLOW_P1_SUMMARY '+JSON.stringify({revisions:config.revisions,cpu:model,bun,pairs:5,checked,controlUnits:old,candidateUnits:current,ratio:current.reduce((a,b)=>a+b,0)/old.reduce((a,b)=>a+b,0),candidatePaxosNeutral:neutral,scope:'conditional frozen-family p1 and separate whole-Paxos work; not a final gate'}));if(!checked||!neutral)process.exitCode=1
 }else{
  const args=['test','./core/effect-queue.test.ts','--test-name-pattern','the CLI on the pool']
  for(let repeat=1;repeat<=5;repeat++){const order=repeat%2?['candidate','base']:['base','candidate'],outcomes:Record<string,unknown>={}
   for(const side of order){const r=await run(side,args,1200,`effect-${repeat}-${side}`);outcomes[side]={exit:r.status,signal:r.signal,wallMs:r.wallMs}}
   const row={repeat,order,outcomes,cpu:model,bun};records.push(row);console.log('FOLLOW_EFFECT_PAIR '+JSON.stringify(row))
  }
  const basePass=records.filter(r=>r.outcomes.base.exit===0).length,candidatePass=records.filter(r=>r.outcomes.candidate.exit===0).length,losses=records.filter(r=>r.outcomes.base.exit===0&&r.outcomes.candidate.exit!==0).map(r=>r.repeat)
  console.log('FOLLOW_EFFECT_SUMMARY '+JSON.stringify({cpu:model,bun,affinity,revisions:config.revisions,pairs:records.length,basePass,candidatePass,candidateOnlyLosses:losses,test:'core/effect-queue.test.ts: the CLI on the pool',scope:'five same-VM fresh-process pairs; no test or proof-budget changes'}))
 }
 for(const side of sides){const dirty=command('git',['status','--porcelain','--untracked-files=no'],dirs[side]);console.log('FOLLOW_CLEAN '+JSON.stringify({side,dirty}));if(dirty)throw Error('gated source changed')}
}finally{rmSync(temp,{recursive:true,force:true})}
