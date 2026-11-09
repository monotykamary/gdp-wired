import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync,gzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {auditSummary,decodeReceipt,summarize,cpu} from './merge-bisect-audit.ts'
const [dir,jobsFile,pointsFile,priorDir,priorJobs]=process.argv.slice(2)
if(!dir||!jobsFile||!pointsFile)throw new Error('usage: cohort-audit.ts dir jobs points [prior-dir prior-jobs]')
const read=(path:string)=>existsSync(path)?readFileSync(path,'utf8'):gunzipSync(readFileSync(path+'.gz')).toString('utf8')
const jobs=JSON.parse(readFileSync(jobsFile,'utf8')),points=JSON.parse(readFileSync(pointsFile,'utf8')),placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')),status=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(row=>row.split('\t')),backends=JSON.parse(readFileSync(join(dir,'backends.json'),'utf8'))
const issues:string[]=[],accepted:any[]=[],skips:any[]=[],seen=new Set<number>()
if(backends.where?.boat!==jobs.length||backends.fallbacks?.length)issues.push('non-boat execution')
for(const job of jobs){
 const id=Number(/cohort\.ts (\d+)/.exec(job.cmd)?.[1]),p=placement[job.name],rows=status.filter(row=>row[0]===job.name)
 if(rows.length!==1||rows[0]?.[1]!=='0'||rows[0]?.[3]!=='boat')issues.push(job.name+': failed scheduler result')
 const text=read(join(dir,job.name+'.log')),skipLines=text.split('\n').filter(line=>line.startsWith('COHORT_CPU_SKIP '))
 if(skipLines.length){const skip=JSON.parse(skipLines[0]!.slice(16));if(skipLines.length!==1||skip.id!==id||skip.cpu===cpu||skip.cpu!==p?.cpu||text.includes('COHORT_RESULT_GZIP'))issues.push(job.name+': invalid skip');else skips.push(skip);continue}
 try{
  const prefix='COHORT_RESULT_GZIP ',lines=text.split('\n').filter(line=>line.startsWith(prefix));if(lines.length!==1)throw new Error('missing/duplicate cohort result')
  const group=JSON.parse(gunzipSync(Buffer.from(lines[0]!.slice(prefix.length),'base64')).toString('utf8'))
  if(group.id!==id||seen.has(id)||group.cpu!==cpu||p?.cpu!==cpu||p?.exclusive!==true||p.co_tenants!==0)throw new Error('cohort identity/placement mismatch');seen.add(id)
  if(JSON.stringify(group.revisions)!==JSON.stringify(points)||group.results.length!==points.length||new Set(group.results.map((row:any)=>row.revision)).size!==points.length)throw new Error('cohort roster mismatch')
  for(const result of group.results){
   if(!points.includes(result.revision)||result.exit!==0){issues.push(job.name+': failed child '+result.revision);continue}
   const {summary,traces}=decodeReceipt(result.stdout),errors=auditSummary(summary,traces,result.revision,1)
   if(summary.replica!==id||summary.repeats!==1||summary.cohort!==true)errors.push('child cohort identity mismatch')
   if(errors.length)issues.push(...errors.map(error=>job.name+': '+error));else accepted.push(summary)
  }
 }catch(e){issues.push(job.name+': '+String(e))}
}
if(priorDir&&priorJobs){for(const job of JSON.parse(readFileSync(priorJobs,'utf8'))){const text=read(join(priorDir,job.name+'.log'));if(text.includes('BISECT_CPU_SKIP '))continue;try{const {summary,traces}=decodeReceipt(text),revision=/merge-bisect\.ts ([a-f0-9]{40})/.exec(job.cmd)?.[1];if(!revision)throw new Error('invalid prior job');const errors=auditSummary(summary,traces,revision);if(errors.length)issues.push(...errors.map(error=>'prior '+job.name+': '+error));else accepted.push(summary)}catch(e){issues.push('prior '+job.name+': '+String(e))}}}
const keys=accepted.map(row=>row.revision+':'+row.replica);if(new Set(keys).size!==keys.length)issues.push('duplicate revision/cohort')
const packed=gzipSync(JSON.stringify(accepted));writeFileSync(join(dir,'accepted-summaries.json.gz'),packed)
const output={issues,skips:skips.length,acceptedReceipts:accepted.length,acceptedSha256:createHash('sha256').update(packed).digest('hex'),byRevision:summarize(accepted)}
writeFileSync(join(dir,'cohort-audit.json'),JSON.stringify(output,null,2)+'\n');console.log(JSON.stringify(output));if(issues.length)process.exitCode=1
