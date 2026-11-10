import{readFileSync,writeFileSync,mkdtempSync,mkdirSync,readdirSync,copyFileSync,symlinkSync,rmSync}from'node:fs'
import{resolve,join}from'node:path'
import{createHash}from'node:crypto'
import{gzipSync}from'node:zlib'
import{strict as assert}from'node:assert'
import{bracket,cpuModel,affinity,microSha256,type Floor}from'./quiet-host.ts'
const sha=(x:string|Uint8Array)=>createHash('sha256').update(x).digest('hex'),input=resolve('generator-input'),cfg=JSON.parse(readFileSync(join(input,'identity.json'),'utf8')),mode=process.argv[2]
if(!['checks','generation','structure'].includes(mode??''))throw Error('checks, generation or structure required')
const {restore,command}=await import(resolve('research/verify-all/final-gate-common.ts')),{runResourceMeasured}=await import(resolve('frozen/driver/resource-run.ts'))
let floor:Floor|undefined
if(mode==='generation'){const text=readFileSync(join('quiet-calibration',process.env.QUIET_FLOOR_LOG??'quiet-floor-calibration-v2.log'),'utf8'),i=text.indexOf('QUIET_FLOORS ');if(i<0)throw Error('missing frozen floors');const decoded=JSON.parse(text.slice(i+'QUIET_FLOORS '.length));assert.equal(decoded.microSha256,microSha256);floor=decoded.floors[cpuModel()];if(!floor){console.log('GENERATOR_CPU_SKIP '+JSON.stringify({cpu:cpuModel(),reason:'no qualified calibration floor'}));process.exit(2)}}
const temp=mkdtempSync('/tmp/lane-i-generator-'),dest=join(temp,'candidate'),rows:any[]=[]
const emit=(tag:string,row:unknown)=>console.log(tag+' '+JSON.stringify(row)),archive=join(temp,'source-input'),originalConsole=console.log
console.log=(...args:unknown[])=>{if(typeof args[0]==='string'&&args[0].startsWith('BAR_RESOURCE_'))return;originalConsole(...args)}
try{
 const cached=resolve('frozen/gate-inputs'),manifest=JSON.parse(readFileSync(join(cached,'manifest.json'),'utf8'));mkdirSync(archive)
 manifest.rootPacks=(manifest.rootPacks??['root.pack']).map((file:string,i:number)=>{const name='root-'+i+'.pack';symlinkSync(resolve(cached,file),join(archive,name));return name})
 for(const [name,module]of Object.entries(manifest.modules) as [string,any][]){const file='module-'+Object.keys(manifest.modules).indexOf(name)+'.pack';symlinkSync(resolve(cached,module.file),join(archive,file));module.file=file}
 symlinkSync(join(input,'baseline.pack'),join(archive,'baseline.pack'));manifest.rootPacks.push('baseline.pack');manifest.roots.push(cfg.integrationBase);manifest.revisions[cfg.integrationBase]={tree:cfg.baselineTree,submodules:manifest.revisions[cfg.cachedArchiveBase].submodules};writeFileSync(join(archive,'manifest.json'),JSON.stringify(manifest))
 const restored=restore(archive,dest,cfg.integrationBase);command('git',['apply','--check',join(input,'candidate.patch')],dest);command('git',['apply',join(input,'candidate.patch')],dest)
 const blobs=Object.fromEntries(Object.keys(cfg.expectedCandidateBlobs).map(p=>[p,command('git',['hash-object',p],dest)]));assert.deepEqual(blobs,cfg.expectedCandidateBlobs);emit('GENERATOR_SOURCE',{candidate:cfg.candidate,restored,blobs,cpu:cpuModel(),affinity:affinity(),patchSha256:sha(readFileSync(join(input,'candidate.patch'))),mode})
 command('bun',['install','--frozen-lockfile'],dest,180000)
 async function run(args:string[],label:string,seconds:number){const r=await runResourceMeasured('bun',args,dest,label,seconds);return{exit:r.status,signal:r.signal,wallMs:r.wallMs,stdoutSha256:sha(r.stdout),stderrSha256:sha(r.stderr),traceGzipBase64:gzipSync(r.stdout+'\n---stderr---\n'+r.stderr).toString('base64'),resourcesGzipBase64:gzipSync(JSON.stringify(r.resources)).toString('base64'),stdout:r.stdout}}
 if(mode==='checks'){
  const tooling=join(dest,'research/lane-i/generator');mkdirSync(tooling,{recursive:true});for(const name of readdirSync(input).filter(n=>n.endsWith('.ts')))copyFileSync(join(input,name),join(tooling,name))
  for(const[label,args]of [['targeted',['test','./core/field-laws.test.ts','./core/field-loaded.test.ts','./core/finite-work.test.ts','./core/finite-tiny.test.ts','./core/finite-tiny-houdini.test.ts','./core/support-order.test.ts','./core/counts-completion-order.test.ts','./kernel/model-values.test.ts']],['roster',['scripts/test-shards.ts','--list']],['type-lint',['run','check']]] as [string,string[]][]){if(label==='targeted'&&process.argv.includes('--tools-only'))continue;const r=await run(args,label,900);const{stdout:_stdout,...receipt}=r;emit('GENERATOR_CHECK',{label,args,...receipt});assert.equal(r.exit,0,label)}
 }else{
  const dir=join(dest,'research/track-gen');mkdirSync(dir,{recursive:true});for(const[a,b]of [['generation.source','t13-generation.ts'],['loaded-check.source','t18-loaded-summary.ts'],['check-loaded.source','t18-check-loaded-record.ts']])copyFileSync(join(input,a!),join(dir,b!))
  const {checkLoadedRecord}=await import(join(dir,'t18-loaded-summary.ts'));process.env.GDP_COUNTS_TRACE='1'
  if(mode==='structure'){const r=await run(['research/track-gen/t13-generation.ts','mldr'],'structure-only',90);assert.equal(r.exit,0);const path=join(temp,'structure-only.log');writeFileSync(path,r.stdout);const structural=checkLoadedRecord(path);emit('GENERATOR_STRUCTURAL_DIAGNOSTIC',{candidate:cfg.candidate,cpu:cpuModel(),qualified:false,scope:'AST presence only: no proof, timing, census or quiet-host qualification claim',structural})}else{
  for(let repeat=1;repeat<=3;repeat++){
   const result=await bracket(floor!,async()=>{const r=await run(['research/track-gen/t13-generation.ts','mldr'],'generation-'+repeat,90);assert.equal(r.exit,0);const path=join(temp,'generation-'+repeat+'.log');writeFileSync(path,r.stdout);const structural=checkLoadedRecord(path);const{stdout:_stdout,...receipt}=r;return{...receipt,structural}});emit('GENERATOR_QUIET_RUN',{repeat,...result});rows.push(result);if(!result.accepted)break
  }
  const complete=rows.length===3&&rows.every(r=>r.accepted),bodies=new Set(rows.filter(r=>r.accepted).map(r=>r.result.structural.canonicalHash)),names=new Set(rows.filter(r=>r.accepted).map(r=>r.result.structural.namesHash));emit('GENERATOR_PREFLIGHT',{candidate:cfg.candidate,cpu:cpuModel(),complete,requiredBodiesPresent:complete,deterministic:complete&&bodies.size===1&&names.size===1,scope:'candidate generation only; not 29/29 or revised-W qualification'});if(!complete||bodies.size!==1||names.size!==1)process.exitCode=2
  }
 }
 const after=Object.fromEntries(Object.keys(cfg.expectedCandidateBlobs).map(p=>[p,command('git',['hash-object',p],dest)]));assert.deepEqual(after,cfg.expectedCandidateBlobs);emit('GENERATOR_UNCHANGED',{candidate:cfg.candidate,production:true})
}finally{console.log=originalConsole;rmSync(temp,{recursive:true,force:true})}
