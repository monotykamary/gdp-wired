// Receipt-only audit. CPU skips and censored children never become successful repeats.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {strict as assert} from 'node:assert'
const marked=(text:string,prefix:string)=>text.split('\n').filter(l=>l.startsWith(prefix+' ')).map(l=>JSON.parse(l.slice(prefix.length+1)))
const digest=(s:unknown)=>typeof s==='string'&&/^[a-f0-9]{64}$/.test(s)
export function auditCompletionLog(text:string,mode:'strict'|'census',expected:any,model?:string){
 const skips=marked(text,'COMPLETION_CPU_SKIP'),rows=marked(text,'COMPLETION_SCOPE_REPEAT'),done=marked(text,'COMPLETION_SCOPE_DONE')
 if(skips.length){assert.equal(mode,'strict');assert.equal(skips.length,1);assert.equal(rows.length+done.length,0);assert.notEqual(skips[0].cpu,'AMD Ryzen 9 9950X 16-Core Processor');return {skipped:true,cpu:skips[0].cpu,pairs:0}}
 assert.equal(done.length,1,'terminal receipt cardinality');const meta=done[0].meta
 assert.equal(meta.mode,mode);assert.deepEqual(meta.identity,expected)
 assert.equal(meta.source.before,expected.beforeSha256);assert.equal(meta.source.after,expected.afterSha256)
 assert.equal(meta.gateBase,expected.gateBase);assert.equal(meta.focusDisabled,false);assert.equal(meta.newProcesses,true)
 for(const p of ['core/machine.ts','core/dsl.ts','core/solver.ts','kernel/kernel.ts','kernel/prove.ts','research/protocols/ic3syn/run.ts','research/protocols/ic3syn/models.ts'])assert(digest(meta.commonHashes[p]),'missing protected source hash')
 const count=mode==='strict'?5:3;assert.equal(rows.length,count);assert.equal(done[0].records,count)
 if(mode==='strict'){assert.equal(meta.cpu,'AMD Ryzen 9 9950X 16-Core Processor');assert.equal(meta.strictMs,60000)}else assert.equal(meta.model,model)
 let completePairs=0,provenPairs=0,verdictLosses=0;const measurements:any[]=[]
 for(const [index,row]of rows.entries()){
  assert.equal(row.repeat,index+1);assert.deepEqual(row.order,(meta.cohort+row.repeat)%2?['after','before']:['before','after'])
  assert.deepEqual(Object.keys(row.outcomes).sort(),['after','before'])
  const b=row.outcomes.before,a=row.outcomes.after
  if(mode==='census'){
   assert(Number.isSafeInteger(b.count)&&b.count>=0);assert.equal(a.count,b.count)
   assert(digest(b.canonicalSha256)&&digest(b.namesSha256));assert.equal(a.canonicalSha256,b.canonicalSha256);assert.equal(a.namesSha256,b.namesSha256)
   completePairs++
  }else{
   const complete=(o:any)=>o.exit===0&&o.result?.id==='consensus_forall'&&['proven','unknown','refuted'].includes(o.result.search?.verdict)&&Number.isFinite(o.result.search.full)&&Number.isFinite(o.result.search.work)
   const good=complete(b)&&complete(a);if(good){completePairs++;assert(digest(b.namesSha256));assert.equal(a.namesSha256,b.namesSha256)}
   if(good&&b.result.search.verdict==='proven'&&a.result.search.verdict==='proven')provenPairs++
   if(complete(b)&&b.result.search.verdict==='proven'&&(!complete(a)||a.result.search.verdict!=='proven'))verdictLosses++
   measurements.push({repeat:row.repeat,complete:good,before:b,after:a})
  }
 }
 return {skipped:false,cpu:meta.cpu,model:meta.model,pairs:completePairs,provenPairs,verdictLosses,source:meta.source,commonHashes:meta.commonHashes,measurements}
}
if(import.meta.main){
 const [mode,dir,jobsFile,identityFile,output]=process.argv.slice(2)
 assert(mode==='strict'||mode==='census');assert(dir&&jobsFile&&identityFile&&output)
 const jobs=JSON.parse(readFileSync(jobsFile,'utf8')) as {name:string}[],expected=JSON.parse(readFileSync(identityFile,'utf8'))
 const terminal=new Map(readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>{const [name,exit]=line.split('\t');return[name,Number(exit)]}))
 assert.equal(terminal.size,jobs.length);assert.equal(new Set(jobs.map(j=>j.name)).size,jobs.length)
 const accepted:any[]=[],issues:any[]=[]
 for(const job of jobs){
  try{assert.equal(terminal.get(job.name),0,'worker failed');const row=auditCompletionLog(readFileSync(join(dir,job.name+'.log'),'utf8'),mode,expected,mode==='census'?job.name.replace(/^gen-/,''):undefined);accepted.push({job:job.name,...row})}catch(e){issues.push({job:job.name,error:String(e)})}
 }
 if(mode==='strict'){
  const placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8'))
  for(const row of accepted.filter(r=>!r.skipped)){assert.equal(placement[row.job]?.cpu,'AMD Ryzen 9 9950X 16-Core Processor');assert.equal(placement[row.job]?.exclusive,true)}
 }
 const result={mode,expectedJobs:jobs.length,acceptedJobs:accepted.filter(r=>!r.skipped).length,skippedJobs:accepted.filter(r=>r.skipped).length,pairs:accepted.reduce((n,r)=>n+r.pairs,0),provenPairs:accepted.reduce((n,r)=>n+(r.provenPairs??0),0),verdictLosses:accepted.reduce((n,r)=>n+(r.verdictLosses??0),0),issues,accepted}
 writeFileSync(output,JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify({...result,accepted:undefined}));if(issues.length)process.exitCode=1
}
