import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync,mkdtempSync,rmSync,existsSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const sourceName=process.env.G1_BASELINE==='1'?'baseline-source':'source'
const input=resolve('port-input'),root=mkdtempSync('/tmp/rolling-integration-'),[mode,...files]=process.argv.slice(2)
function run(command:string,args:string[]){const p=spawnSync(command,args,{cwd:root,env:process.env,encoding:'utf8',timeout:800000,maxBuffer:64*1024*1024});process.stdout.write(p.stdout??'');process.stderr.write(p.stderr??'');if(p.error||p.status!==0)throw Error(`${command} failed (${p.status}): ${p.error??''}`);return p.stdout??''}
function identities(){
 const blob=(bytes:Buffer)=>createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex')
 const file=join(input,'READER-EXCEPTION.json'),exception=existsSync(file)?JSON.parse(readFileSync(file,'utf8')):undefined
 let checked=0,excepted=false
 for(const line of readFileSync(join(input,'PROTECTED.tree'),'utf8').trim().split('\n')){
  const m=/^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line);a(m);const bytes=readFileSync(join(root,m[2]!)),actual=blob(bytes)
  if(exception&&m[2]==='kernel/reader.ts'){
   a.equal(exception.path,m[2]);a.equal(exception.originalBlob,m[1]);a.equal(exception.patchedBlob,actual);a.equal(exception.hooks,7)
   const text=bytes.toString(),hooks=text.match(/^    if \(completeWorkProfile\.enabled\) checkWorkEndpoint\('reader (?:value|decision|expression|condition|fact|form|sync)'\)\n/gm)??[]
   a.equal(hooks.length,7)
   const restored=text.replace("import {completeWorkProfile} from '../core/work-profile.ts'\n",'').replace("import {checkWorkEndpoint} from './prove.ts'\n",'').replace(/^    if \(completeWorkProfile\.enabled\) checkWorkEndpoint\('reader (?:value|decision|expression|condition|fact|form|sync)'\)\n/gm,'')
   a.equal(blob(Buffer.from(restored)),m[1],'reader decoding changed');excepted=true
  }else a.equal(actual,m[1],m[2]!)
  checked++
 }
 if(exception)a(excepted,'reader exception not checked')
 return checked
}
try{
 for(const name of ['source','gdp-ts','handwired'])run('tar',['-xf',join(input,(name==='source'?sourceName:name)+'.tar'),'-C',root])
 const before=identities();run('bun',['install','--frozen-lockfile'])
 if(mode==='types')run('bun',['run','check'])
 else if(mode==='test')run('bun',['test',...files])
 else if(mode==='family')run('bun',['research/lane-i/rolling-20261111/family-replay.ts','research/lane-i/rolling-20261111/closed-family-proof.json.gz','--mutations'])
 else if(mode==='source')run('bun',['research/lane-i/rolling-20261111/family-source-audit.ts','research/lane-i/rolling-20261111/closed-family-proof.json.gz'])
 else if(mode==='script')run('bun',files)
 else if(mode==='evaluation-benchmark'){writeFileSync(join(root,'research/evaluation-benchmark.ts'),readFileSync(join(input,'evaluation-benchmark.source')));run('bun',['--preload','./core/clock-tripwire-preload.ts','research/evaluation-benchmark.ts'])}
 else if((mode==='dispatch'||mode==='dispatch-report')){writeFileSync(join(root,'research/dispatch-probe.ts'),readFileSync(join(input,'dispatch-probe.source')));const out=run('bun',['--preload',join(root,'research/dispatch-probe.ts'),'research/protocols/ic3syn/run.ts','--ms','900000','--only','mldr','--skip','broken']);const events=out.split('\n').filter(line=>line.startsWith('DISPATCH_EVENT ')).map(line=>JSON.parse(line.slice(15)));const proposals=events.filter(e=>e.phase==='count-strategy-result'&&e.law==='inX: no quorum canVote/3'&&e.proposed===true&&e.checked===false&&e.status==='unchecked');if(mode==='dispatch')a(proposals.length>0,'Inv* unchecked strategy proposal did not return');a(!events.some(e=>e.phase==='count-strategy'&&e.law==='inX: no quorum canVote/3'&&e.stage==='step-check:true'),'early Inv* STEP check ran');console.log('FINAL_STEP_PROPOSAL '+JSON.stringify({returned:proposals.length,checked:false,status:'unchecked'}))}
 else if(mode==='reader-cap'){
  writeFileSync(join(root,'core/reader-cap-probe.ts'),readFileSync(join(root,'research/lane-i/rolling-20261111/reader-cap-probe.source')))
  for(const allowance of ['500000','5000000']){
   const records=[false,true].map(observed=>run('bun',['core/reader-cap-probe.ts',String(observed),allowance]).split('\n').find(line=>line.startsWith('READER_CAP ')))
   a(records[0]);a.deepEqual(records[1],records[0]);console.log('READER_CAP_IDENTITY '+JSON.stringify({allowance:Number(allowance),proofAndRawEqual:true}))
  }
 }
 else if(mode==='clock'||mode==='clock-full'){
  const dir=join(root,'research/lane-i/rolling-20261111'),old=readFileSync(join(dir,'old-clock-reference.source'))
  a.equal(createHash('sha256').update(old).digest('hex'),'3d8aca2fccdb344e51155501435841e22043eed974b417b627b2530a8b8a2a7e')
  const clockSource=mode==='clock-full'?old.toString().replaceAll('2000*fullRate','100000*fullRate').replaceAll('clock()+2000','clock()+100000'):old
  if(mode==='clock-full')console.log('CLOCK_FULL_SCOPE '+JSON.stringify({originalSHA256:createHash('sha256').update(old).digest('hex'),testOnlyAllowance:100000*250,primitiveCapsChanged:false}))
  writeFileSync(join(root,'core/f-old-clock-reference.test.ts'),clockSource)
  run('bun',['test','core/f-old-clock-reference.test.ts','-t','lifted discovery, exhaustive composition and native replay inherit a clock-free scope'])
  const probe=readFileSync(join(dir,'counter-probe.source'),'utf8')+"\nimport {rawWork} from './work-meter.ts'\nconsole.log('COMPLETE_RAW '+JSON.stringify(rawWork()))\n"
  writeFileSync(join(root,'core/f-counter-probe.ts'),mode==='clock-full'?probe.replaceAll('2000*fullRate','100000*fullRate').replaceAll('clock()+2000','clock()+100000'):probe)
  const records=[false,true].map(observed=>run('bun',['core/f-counter-probe.ts',String(observed)]).split('\n').filter(line=>line.startsWith('COUNTER_PROBE ')||line.startsWith('COMPLETE_RAW ')))
  a.equal(records[0]!.length,2);a.deepEqual(records[1],records[0]);console.log('INTEGRATED_CLOCK_IDENTITY '+JSON.stringify({oldTestSHA256:createHash('sha256').update(old).digest('hex'),proofAndCompleteRawEqual:true}))
 }else throw Error('unknown mode '+mode)
 a.equal(identities(),before)
 console.log('ROLLING_GATE '+JSON.stringify({sourceTree:readFileSync(join(input,sourceName+'.txt'),'utf8').trim(),mode,files,protected:before}))
}finally{rmSync(root,{recursive:true,force:true})}
