// Research-only original-harness comparison. CPU skips are never successful repeats.
import {createHash} from 'node:crypto'
import {mkdtempSync,readFileSync,writeFileSync,mkdirSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {resolve,join} from 'node:path'
import {spawnSync} from 'node:child_process'
import {gzipSync,gunzipSync} from 'node:zlib'

const [mode,id,groupText='0',repeatsText='5']=process.argv.slice(2),group=Number(groupText),repeats=Number(repeatsText)
if(!['strict','census'].includes(mode!)||!id||!Number.isInteger(repeats)||repeats<1||(mode==='strict'&&repeats<5))throw Error('mode, protocol and at least five strict repeats required')
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim()
if(mode==='strict'&&cpu!=='AMD Ryzen 9 9950X 16-Core Processor'){console.log('T17_CPU_SKIP '+JSON.stringify({id,group,cpu}));process.exit(0)}
const root=process.cwd(),input=resolve('source-input'),archives=resolve('archives'),temp=mkdtempSync(join(tmpdir(),'t17-focus-'))
const digest=(value:string|Uint8Array)=>createHash('sha256').update(value).digest('hex')
const manifest=JSON.parse(readFileSync(join(input,'manifest.json'),'utf8')) as {shas:{main:string,prior:string,focus:string},hashes:{main:string,prior:string,focus:string}}
if(manifest.shas.main!=='4497c4b05c3111959a2b8d808c426a0e3cab3f01'||Object.values(manifest.shas).some(s=>!/^[a-f0-9]{40}$/.test(s))||Object.values(manifest.hashes).some(s=>!/^[a-f0-9]{64}$/.test(s)))throw Error('invalid immutable source manifest')
const expected:Record<string,string>={'source.tar':'26824362de21cb4ea3c87e78f09aa37dc49077b88ab8a6bb1421dd3eeb311979','handwired.tar':'73d44548dbe109a40ac933406324e17d7dee39e7dff1a6f1270ed030c31c1da4','gdp-ts.tar':'75d367da15decb1fefce2ae72ae50e7f3f737989094a760fde643c5b1f5c1496','main.patch':manifest.hashes.main,'prior.patch':manifest.hashes.prior,'focus.patch':manifest.hashes.focus}
const command=(bin:string,args:string[],cwd=temp)=>{const p=spawnSync(bin,args,{cwd,encoding:'utf8',maxBuffer:16*1024*1024});if(p.status!==0)throw Error(`${bin}: ${p.status}: ${p.stderr}\n${p.stdout}`);return p.stdout}
const shas=manifest.shas
const dirs={main:join(temp,'main'),prior:join(temp,'prior'),focus:join(temp,'focus')},sides=Object.keys(dirs) as (keyof typeof dirs)[]
const anchor='return {traced, get counted()'
const observer=`const __t17Trace = (...args: Parameters<typeof traced>): ReturnType<typeof traced> => {
 const w=__t17Work.n,f=__t17Full(),t=clock(),s=performance.now(),p={...cprof}
 let r: ReturnType<typeof traced> | undefined
 try { return r=traced(...args) } finally {
  console.error('T17_LAW '+JSON.stringify({law:args[0].name,family:args[1].length,pass:args[2],allowance:args[3],at:s,wallMs:performance.now()-s,units:clock()-t,work:__t17Work.n-w,full:__t17Full()-f,outcome:r?('proof' in r?'kept':r.stuck):'throw',profile:Object.fromEntries(Object.entries(cprof).map(([k,v])=>[k,v-(p[k]??0)]).filter(([,v])=>v))}))
 }
}
return {traced:__t17Trace, get counted()`
const metadata:Record<string,unknown>={}
try{
 for(const [file,hash]of Object.entries(expected)){const path=join(file.endsWith('.tar')?archives:input,file);if(digest(readFileSync(path))!==hash)throw Error(`input hash mismatch: ${file}`)}
 for(const side of sides){
  const dir=dirs[side];mkdirSync(dir)
  command('tar',['-xf',join(archives,'source.tar'),'-C',dir])
  for(const patch of side==='focus'?['prior','focus']:[side])command('git',['apply',join(input,patch+'.patch')],dir)
  for(const vendor of ['handwired','gdp-ts']){mkdirSync(join(dir,'vendor',vendor),{recursive:true});command('tar',['-xf',join(archives,vendor+'.tar'),'-C',join(dir,'vendor',vendor)])}
  command('bun',['install','--frozen-lockfile'],dir)
  const hashes=Object.fromEntries(['core/counts.ts','core/machine.ts','core/dsl.ts','research/protocols/ic3syn/run.ts','research/protocols/ic3syn/models.ts'].map(file=>[file,digest(readFileSync(join(dir,file)))]))
  if(mode==='strict'){
   const path=join(dir,'core/counts.ts'),source=readFileSync(path,'utf8')
   if(source.split(anchor).length!==2)throw Error('ambiguous trace anchor: '+side)
   const instrumented="import {work as __t17Work} from './solver.ts'\nimport {fullWork as __t17Full} from '../kernel/prove.ts'\n"+source.replace(anchor,observer)
   writeFileSync(path,instrumented);writeFileSync(join(dir,'.t17-preload.ts'),readFileSync(join(root,'measurement/t17-focus-preload.ts')))
   metadata[side]={sha:shas[side],hashes,instrumentedCounts:digest(instrumented)}
  }else{
   mkdirSync(join(dir,'research/track-gen'),{recursive:true})
   writeFileSync(join(dir,'research/track-gen/t17-census.ts'),readFileSync(join(root,'measurement/t13-generation.ts')))
   metadata[side]={sha:shas[side],hashes}
  }
 }
 console.log('T17_SOURCE '+JSON.stringify({mode,id,group,cpu,strictMs:60000,metadata,inputs:expected}))
 const env:NodeJS.ProcessEnv={...process.env,CI:'1',GIT_TERMINAL_PROMPT:'0',GDP_INFER_TRACE:'2',GDP_COUNTS_TRACE:'3'}
 delete env.GDP_COUNTS_FOCUS;delete env.GDP_COUNTS_GIVEN;delete env.GDP_COUNTS_COUNT_FIRST
 for(let repeat=1;repeat<=repeats;repeat++){
  const shift=(repeat+group)%3,order=[...sides.slice(shift),...sides.slice(0,shift)],generation:Record<string,unknown>={}
  for(const side of order){
   const args=mode==='strict'?['--preload','./.t17-preload.ts','research/protocols/ic3syn/run.ts','--ms','60000','--only',id,'--skip','broken']:['research/track-gen/t17-census.ts',id]
   const start=performance.now(),run=spawnSync('timeout',['-s','KILL','60','bun',...args],{cwd:dirs[side],env,encoding:'utf8',timeout:65000,maxBuffer:64*1024*1024}),wallMs=performance.now()-start,stdout=run.stdout??'',stderr=run.stderr??''
   const json=(text:string,prefix=''):any[]=>text.split('\n').flatMap(line=>{if(prefix&&!line.startsWith(prefix))return [];try{return [JSON.parse(line.slice(prefix.length))]}catch{return []}})
   const record={mode,id,group,repeat,order,side,sha:shas[side],cpu,exit:run.status,signal:run.signal,error:run.error?.message,wallMs,results:mode==='strict'?json(stdout).filter(row=>row.id===id):undefined,profile:json(stderr,'T17_PROFILE '),attempts:json(stderr,'T17_LAW '),stdoutSha256:digest(stdout),stderrSha256:digest(stderr),traceGzipBase64:gzipSync(stdout+'\n---stderr---\n'+stderr).toString('base64')}
   if(mode==='census'){
    const lines=stdout.split('\n').filter(line=>line.startsWith('T13_DATA_GZIP_BASE64 '))
    if(run.status!==0||lines.length!==1)throw Error('missing generation record: '+side+'/'+id)
    const capture=JSON.parse(gunzipSync(Buffer.from(lines[0]!.slice('T13_DATA_GZIP_BASE64 '.length),'base64')).toString())
    if(capture.queries!==0||capture.records.length!==1||capture.records[0].id!==id)throw Error('incorrect generation scope')
    generation[side]=capture.records[0]
   }
   console.log('T17_RUN '+JSON.stringify(record))
  }
  if(mode==='census')console.log('T17_CENSUS '+JSON.stringify({id,group,repeat,cpu,records:generation}))
 }
 console.log('T17_COMPLETE '+JSON.stringify({mode,id,group,repeats,cpu,sides,strictMs:60000}))
}finally{rmSync(temp,{recursive:true,force:true})}
