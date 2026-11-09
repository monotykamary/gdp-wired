// Fresh-process strict A/B comparison. Wrong CPUs are skipped, never accepted repeats.
import {readFileSync,writeFileSync,mkdtempSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
import {strict as assert} from 'node:assert'
const cohort=Number(process.argv[2]??0),mode=process.argv[3]??'strict',model=process.argv[4]
assert(['strict','census'].includes(mode))
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim()
if(mode==='strict'&&cpu!=='AMD Ryzen 9 9950X 16-Core Processor'){
 console.log('COMPLETION_CPU_SKIP '+JSON.stringify({cohort,cpu,required:'AMD Ryzen 9 9950X 16-Core Processor'}));process.exit(0)
}
const hash=(s:string|Buffer)=>createHash('sha256').update(s).digest('hex')
const root=process.cwd(),file=resolve('core/counts.ts'),after=readFileSync(file,'utf8'),before=readFileSync('scope-input/before-counts.source','utf8')
const identity=JSON.parse(readFileSync('scope-input/identity.json','utf8'))
assert.equal(hash(before),identity.beforeSha256);assert.equal(hash(after),identity.afterSha256)
const commonHashes=Object.fromEntries(['core/machine.ts','core/dsl.ts','core/solver.ts','kernel/kernel.ts','kernel/prove.ts','research/protocols/ic3syn/run.ts','research/protocols/ic3syn/models.ts'].map(p=>[p,hash(readFileSync(p))]))
const work=mkdtempSync(join(process.env.HOME??'/tmp','completion-scope-results-'))
writeFileSync('completion-scope-work.txt',work+'\n')
writeFileSync(join(work,'before-counts.source'),before);writeFileSync(join(work,'after-counts.source'),after)
const anchor='return {traced, get counted()',wrapper=`const __scopeTraced = (...args: Parameters<typeof traced>): ReturnType<typeof traced> => {
 const w=__scopeWork.n,f=__scopeFull(),t=clock(),s=performance.now(),p={...cprof}
 let r: ReturnType<typeof traced> | undefined
 try { return r=traced(...args) } finally {
  console.error('COMPLETION_LAW '+JSON.stringify({law:args[0].name,pass:args[2],at:s,wallMs:performance.now()-s,units:clock()-t,work:__scopeWork.n-w,full:__scopeFull()-f,outcome:r?('proof' in r?'kept':r.stuck):'throw',profile:Object.fromEntries(Object.entries(cprof).map(([k,v])=>[k,v-(p[k]??0)]).filter(([,v])=>v))}))
 }
}
return {traced:__scopeTraced, get counted()`
const instrument=(source:string)=>{
 assert.equal(source.split(anchor).length,2,'unique public trace anchor')
 return "import {work as __scopeWork} from './solver.ts'\nimport {fullWork as __scopeFull} from '../kernel/prove.ts'\n"+source.replace(anchor,wrapper)
}
const parse=(text:string,prefix='')=>text.split('\n').flatMap(line=>{
 if(prefix&&!line.startsWith(prefix))return[]
 try{return[JSON.parse(line.slice(prefix.length))]}catch{return[]}
})
const summaries:any[]=[]
const meta={identity,commonHashes,cohort,mode,model,cpu,gateBase:'4497c4b05c3111959a2b8d808c426a0e3cab3f01',control:'febca10f',candidateProduction:'337294ea4ba1095b92d2e3bf8a4aad245ac8fd91',strictMs:mode==='strict'?60000:null,source:{before:hash(before),after:hash(after)},newProcesses:true,focusDisabled:false}
writeFileSync(join(work,'meta.json'),JSON.stringify(meta,null,2)+'\n')
try{
 for(let repeat=1;repeat<=(mode==='strict'?5:3);repeat++){
  const order=(cohort+repeat)%2?['after','before']:['before','after'],outcomes:any={}
  for(const side of order){
   writeFileSync(file,mode==='strict'?instrument(side==='before'?before:after):side==='before'?before:after)
   const args=mode==='strict'?['--preload','./research/track-m/completion-scope-phase.ts','research/protocols/ic3syn/run.ts','--ms','60000','--only','consensus_forall','--skip','broken']:['research/track-m/completion-scope-generation.ts',model!]
   const seconds=mode==='strict'?'60':'120',start=performance.now()
   const run=spawnSync('timeout',['-s','KILL',seconds,'bun',...args],{cwd:root,encoding:'utf8',timeout:(Number(seconds)+5)*1000,maxBuffer:96*1024*1024,env:{...process.env,CI:'1',GIT_TERMINAL_PROMPT:'0',GDP_COUNTS_FOCUS:'1',GDP_INFER_TRACE:'2',GDP_COUNTS_TRACE:'3'}})
   const stdout=run.stdout??'',stderr=run.stderr??'',raw=stdout+'\n---stderr---\n'+stderr
   writeFileSync(join(work,`${repeat}-${side}.log.gz`),gzipSync(raw))
   const results=parse(stdout).filter(r=>r.id==='consensus_forall'),profile=parse(stderr,'LANE_I_PROFILE '),attempts=parse(stderr,'COMPLETION_LAW ')
   const names=profile.find(p=>p.event==='candidate-names')?.names
   const finish=profile.find(p=>p.event==='result'),generation=profile.find(p=>p.event==='candidates'),zero=finish?finish.at-finish.searchMs:undefined
   const receipt={exit:run.status,signal:run.signal,error:run.error?.message,wallMs:performance.now()-start,results,profile,attempts,stdoutSha256:hash(stdout),stderrSha256:hash(stderr)}
   writeFileSync(join(work,`${repeat}-${side}.json`),JSON.stringify(receipt,null,2)+'\n')
   if(mode==='strict'){
    assert(results.length<=1,'duplicate semantic result')
    outcomes[side]={exit:run.status,signal:run.signal,result:results[0]??null,namesCount:names?.length??null,namesSha256:names?hash(JSON.stringify(names)):null,postGenerationMs:finish&&generation?finish.at-generation.at:null,generationWallMs:generation&&zero!==undefined?generation.at-zero:null,attemptWork:attempts.reduce((s,a)=>s+a.work,0),attemptFull:attempts.reduce((s,a)=>s+a.full,0)}
   }else{
    const marks=[...stdout.matchAll(/T13_DATA_GZIP_BASE64 (\S+)/g)]
    assert.equal(run.status,0,'generation child failed');assert.equal(marks.length,1,'generation receipt cardinality')
    const {gunzipSync}=await import('node:zlib'),data=JSON.parse(gunzipSync(Buffer.from(marks[0]![1]!,'base64')).toString())
    assert.equal(data.queries,0);assert.equal(data.records.length,1);assert.equal(data.records[0].id,model)
    outcomes[side]={count:data.records[0].count,canonicalSha256:hash(JSON.stringify(data.records[0].canonical)),namesSha256:hash(JSON.stringify(data.records[0].names)),wallMs:data.records[0].wallMs}
   }
  }
  if(mode==='census'){assert.equal(outcomes.before.canonicalSha256,outcomes.after.canonicalSha256,'generated canonical law roster changed');assert.equal(outcomes.before.namesSha256,outcomes.after.namesSha256,'generated law names changed')}
  const row={repeat,order,outcomes};summaries.push(row)
  writeFileSync(join(work,'summary.json'),JSON.stringify({meta,records:summaries},null,2)+'\n')
  console.log('COMPLETION_SCOPE_REPEAT '+JSON.stringify(row))
 }
 console.log('COMPLETION_SCOPE_DONE '+JSON.stringify({meta,records:summaries.length,archiveDirectory:work}))
}finally{writeFileSync(file,after)}
