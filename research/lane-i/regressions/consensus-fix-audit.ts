// Three-repeat strict cohorts, reusing the original trace/semantic verifier.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {parseReceipts} from './receipt-audit.ts'
const [dir,jobsPath,sourcesPath]=process.argv.slice(2)
if(!dir||!jobsPath||!sourcesPath)throw Error('usage: consensus-fix-audit.ts output-dir jobs.json sources.json')
const read=(path:string)=>JSON.parse(readFileSync(path,'utf8'))
const jobs=read(jobsPath),sources=read(sourcesPath),placement=read(join(dir,'placement.json')),backend=read(join(dir,'backends.json')),hashes=read(join(import.meta.dir,'paxos-harness-hashes.json'))
const statuses=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t')),issues:string[]=[],pairs:any[]=[],skips:any[]=[]
if(statuses.length!==jobs.length||new Set(statuses.map(row=>row[0])).size!==jobs.length||statuses.some(row=>!jobs.some((job:any)=>job.name===row[0])))issues.push('job roster mismatch')
if(backend.where?.boat!==jobs.length||backend.fallbacks?.length)issues.push('non-boat or fallback execution')
for(const job of jobs){
 const id=Number(job.name.split('-').at(-1)),status=statuses.find(row=>row[0]===job.name),p=placement[job.name],text=readFileSync(join(dir,job.name+'.log'),'utf8')
 if(status?.[1]!=='0'||status?.[3]!=='boat'||!p?.exclusive||p.co_tenants!==0)issues.push(job.name+': failed/nonexclusive execution')
 const checked=parseReceipts(text,'strict',id,sources)
 issues.push(...checked.issues.map(issue=>job.name+': '+issue))
 if([...checked.pairs,...checked.skips].some(row=>row.cpu!==p?.cpu))issues.push(job.name+': placement CPU mismatch')
 for(const line of text.split('\n').filter(line=>line.startsWith('STRICT_PAIR '))){
  const row=JSON.parse(line.slice(12))
  for(const side of ['base','candidate']){
   const rev=side==='base'?sources.baseline:sources.candidate,expected=hashes[rev],actual=row.hashes?.[side]
   if(!expected||JSON.stringify(Object.keys(actual??{}).sort())!==JSON.stringify(Object.keys(expected).sort())||Object.entries(expected).some(([path,hash])=>actual[path]!==hash))issues.push(job.name+': protected source hash mismatch')
  }
 }
 pairs.push(...checked.pairs);skips.push(...checked.skips)
}
const allProven=pairs.length>0&&pairs.every(pair=>pair.metrics.base.verdict==='proven'&&pair.metrics.candidate.verdict==='proven'),enoughPairs=pairs.length>=5,noLoss=issues.length===0&&enoughPairs&&allProven
const result={sources,issues,acceptedPairs:pairs.length,requiredPairs:5,enoughPairs,skips,allProven,noLoss,pairs,finalGate:false}
writeFileSync(join(dir,'consensus-fix-audit.json'),JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify({...result,pairs:undefined,skips:skips.length}))
if(!noLoss)process.exitCode=1
