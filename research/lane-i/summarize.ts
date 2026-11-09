// Iteration receipt audit, NOT Lane D's final gate or a merge authorization.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
const root=process.argv[2]??'runs/lane-i/v1'
const read=(path:string)=>readFileSync(join(root,path),'utf8')
const expected=JSON.parse(readFileSync('research/lane-i/census.jobs.json','utf8')) as {name:string}[]
const issues:string[]=[]
const digest=(text:string)=>createHash('sha256').update(text).digest('hex')
function batch(dir:string,names:string[]){
 const lines=read(dir+'/summary.tsv').trim().split('\n').map(x=>x.split('\t'))
 const place=JSON.parse(read(dir+'/placement.json')) as Record<string,{exclusive:boolean,co_tenants:number,type:string,cpu:string,vm:string}>
 const rows=new Map(lines.map(row=>[row[0]!,row]))
 if(rows.size!==names.length||lines.length!==names.length||lines.some(row=>!names.includes(row[0]!)))issues.push(dir+': roster mismatch')
 return names.map(name=>{
  const row=rows.get(name),p=place[name],log=read(dir+'/'+name+'.log')
  if(!row||row[1]!=='0'||row[3]!=='boat')issues.push(name+': failed/missing/non-boat job')
  if(!p?.exclusive||p.co_tenants!==0||p.type!=='large'||!p.cpu)issues.push(name+': invalid CPU placement')
  return {name,exit:row?.[1],seconds:row?.[2],placement:p,log,sha256:digest(log)}
 })
}
const census=batch('census',expected.map(j=>j.name)).map(job=>{
 const rows=[...job.log.matchAll(/^LANE_I_CENSUS (.+)$/gm)]
 if(rows.length!==1)throw Error(job.name+': receipt cardinality')
 const row=JSON.parse(rows[0]![1]!) as {id:string,repeat:number,identical:boolean,base:unknown,candidate:unknown,names?:string[]}
 if(job.name!==`gen-${row.id}-r${row.repeat}`)issues.push(job.name+': identity mismatch')
 if(row.id!=='mldr'&&!row.identical)issues.push(job.name+': unrelated generation list changed')
 return {...job,log:undefined,...row}
})
const validationNames=['check',...Array.from({length:4},(_,i)=>'changed-tests-'+(i+1)),...Array.from({length:3},(_,i)=>'mldr-r'+(i+1))]
const validation=batch('validation',validationNames)
const tests=validation.filter(j=>j.name.startsWith('changed-tests')).map(j=>({name:j.name,counts:j.log.match(/\d+ pass\s+\d+ fail[^]*?\d+ expect\(\) calls/),sha256:j.sha256,placement:j.placement}))
const mldr=validation.filter(j=>j.name.startsWith('mldr-')).map(j=>{
 const sides=['base','candidate'].map(side=>{
  const start=j.log.indexOf(`LANE_I_BEGIN mldr ${j.name.slice(-1)} mldr ${side}`),end=j.log.indexOf(`LANE_I_END mldr ${j.name.slice(-1)} mldr ${side}`,start)
  if(start<0||end<0)throw Error(j.name+': missing phase '+side)
  const text=j.log.slice(start,end),result=text.split('\n').filter(s=>s.startsWith('{')).map(s=>{try{return JSON.parse(s)}catch{return null}}).find(x=>x?.id==='mldr')
  const candidates=[...text.matchAll(/counts: candidates at (\d+) ms: (.*)/g)].map(m=>({unitsBefore:Number(m[1]),laws:m[2]!.split('; ')}))
  const attempts=[...text.matchAll(/counts: try (.*?) \| ls (\d+) pass ([01]) ms (\d+) took (\d+) wall (\d+) \[(.*?)\] -> (.*)/g)].map(m=>({law:m[1],family:Number(m[2]),pass:Number(m[3]),allowance:Number(m[4]),units:Number(m[5]),wallMs:Number(m[6]),profile:m[7],outcome:m[8]}))
  const firstAttempt=text.indexOf('counts: try '),rounds=text.split('\n').filter(s=>s.startsWith('counts: round '))
  return {side,result,exit:/LANE_I_EXIT \S+ (\d+)/.exec(text)?.[1],candidates,attempts,rounds,traceHasFirstAttempt:firstAttempt>=0,safetyTried:attempts.some(a=>a.law==='one primary per term'),safetyKept:attempts.some(a=>a.law==='one primary per term'&&a.outcome==='kept')}
 })
 return {name:j.name,placement:j.placement,sha256:j.sha256,sides}
})
const report={finalGate:false,identity:JSON.parse(read('input/identity.json')),issues,census,tests,mldr,validation:validation.map(({log:_log,...job})=>job)}
writeFileSync(join(root,'summary.json'),JSON.stringify(report,null,2)+'\n')
console.log(JSON.stringify({finalGate:false,issues,censusPairs:census.length,unrelatedIdentical:census.filter(r=>r.id!=='mldr'&&r.identical).length,mldr:mldr.map(j=>({name:j.name,cpu:j.placement?.cpu,sides:j.sides.map(s=>({side:s.side,result:s.result,laws:s.candidates.at(-1)?.laws.length,attempts:s.attempts.length,safetyTried:s.safetyTried,safetyKept:s.safetyKept}))}))},null,2))
if(issues.length)process.exitCode=1
