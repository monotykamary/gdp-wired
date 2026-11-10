// Diagnostic variants only. They never replace the accepted source or its test.
import{readFileSync,writeFileSync,copyFileSync,mkdtempSync,mkdirSync,readdirSync,rmSync}from'node:fs'
import{join,resolve}from'node:path'
import{gzipSync}from'node:zlib'
import{createHash}from'node:crypto'
import{runResourceMeasured}from'./resource-run.ts'
const sha=(v:string|Uint8Array)=>createHash('sha256').update(v).digest('hex')
const hashes:Record<string,string>=JSON.parse(readFileSync('checksums.json','utf8'))
for(const[p,h]of Object.entries(hashes))if(sha(readFileSync(p))!==h)throw Error('input mismatch '+p)
const config=JSON.parse(readFileSync('gate-inputs/gate.json','utf8')),repeat=Number(process.argv[2]),parent='d3adf3c9589ec014a158b6f42ecfb091c999bb43'
if(!Number.isInteger(repeat)||repeat<1||repeat>3)throw Error('repeat required')
const{restore,command}=await import(resolve('research/verify-all/final-gate-common.ts'))
const temp=mkdtempSync('/tmp/effect-source-trace-'),variants=[{name:'base',rev:config.baseline},{name:'parent',rev:parent},{name:'candidate',rev:config.candidate},{name:'prior-binder',rev:config.candidate},{name:'unshared-rows',rev:config.candidate}],results:any[]=[]
const files=['core/cli.ts','core/effect.ts','core/effect-prims.ts','core/effect-queue.test.ts','examples/effect-pool.ts']
try{
 for(let index=0;index<variants.length;index++){
  const variant=variants[(index+repeat-1)%variants.length]!,dir=join(temp,variant.name),meta=restore(resolve('gate-inputs'),dir,variant.rev)
  for(const file of files)if(sha(readFileSync(join(dir,file)))!==config.sources.base[file])throw Error('effect input changed '+file)
  const before=sha(readFileSync(join(dir,'kernel/prove.ts')))
  if(variant.name==='prior-binder')writeFileSync(join(dir,'kernel/prove.ts'),command('git',['show',parent+':kernel/prove.ts'],dir)+'\n')
  const after=sha(readFileSync(join(dir,'kernel/prove.ts'))),nativeKernel=sha(readFileSync(join(dir,'kernel/kernel.ts')))
  if(nativeKernel!==config.sources.base['kernel/kernel.ts'])throw Error('native checker changed')
  command('bun',['install','--frozen-lockfile'],dir)
  copyFileSync('regression-driver/effect-cli-trace.ts',join(dir,'effect-cli-trace.ts'))
  const out=join(temp,'dump-'+variant.name);mkdirSync(out)
  process.env.DUMP_DIR=out;process.env.DUMP_MIN='0';process.env.DUMP_N='3'
  if(variant.name==='unshared-rows')process.env.GDP_ROWS_SHARED='0';else delete process.env.GDP_ROWS_SHARED
  const r=await runResourceMeasured('bun',['--preload','./research/query/dump.ts','./effect-cli-trace.ts'],dir,'trace-'+repeat+'-'+variant.name,300)
  const line=r.stdout.split('\n').find(l=>l.startsWith('EFFECT_CLI_RESULT ')),outcome=line?JSON.parse(line.slice(18)):null
  const queries=readFileSync(join(out,'queries.jsonl'),'utf8'),records=queries.trim().split('\n').filter(Boolean).map(l=>JSON.parse(l))
  const goals=Object.fromEntries(readdirSync(out).filter(f=>f.endsWith('.json')).map(f=>[f,JSON.parse(readFileSync(join(out,f),'utf8'))]))
  const trace={repeat,variant:variant.name,revision:variant.rev,meta,experimental:variant.name==='prior-binder'||variant.name==='unshared-rows',before,after,nativeKernel,rowsShared:process.env.GDP_ROWS_SHARED??'default',outcome,exit:r.status,signal:r.signal,wallMs:r.wallMs,resources:r.resources,stdoutSha256:sha(r.stdout),stderrSha256:sha(r.stderr),traceGzipBase64:gzipSync(r.stdout+'\n---stderr---\n'+r.stderr).toString('base64'),queriesSha256:sha(queries),queriesGzipBase64:gzipSync(queries).toString('base64'),goalsGzipBase64:gzipSync(JSON.stringify(goals)).toString('base64'),queryCount:records.length,queryWork:records.reduce((n,q)=>n+(typeof q.work==='number'?q.work:0),0),slow:records.filter(q=>q.ms>500).sort((a,b)=>b.ms-a.ms).slice(0,12),tracked:command('git',['status','--porcelain','--untracked-files=no'],dir)}
  console.log('EFFECT_SOURCE_TRACE '+JSON.stringify(trace));results.push({variant:variant.name,exit:r.status,outcome,slow:trace.slow})
  if(r.status!==0||!outcome)throw Error('trace process failed')
 }
 console.log('EFFECT_SOURCE_SUMMARY '+JSON.stringify({repeat,baseline:config.baseline,candidate:config.candidate,results}))
}finally{rmSync(temp,{recursive:true,force:true})}
