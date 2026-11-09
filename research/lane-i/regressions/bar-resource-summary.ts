import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {parseReceipts,baseline,candidate,type ReceiptSources} from './receipt-audit.ts'
import {validPeakRss} from './rss-audit.ts'
import {checkedPortfolioHandoff} from './bar-portfolio.ts'
const [dir,jobsFile,identityFile]=process.argv.slice(2);if(!dir||!jobsFile)throw new Error('usage: bar-resource-summary.ts dir jobs [identity]')
const identity:ReceiptSources=identityFile?JSON.parse(readFileSync(identityFile,'utf8')):{baseline,candidate}
if(!/^[a-f0-9]{40}$/.test(identity.baseline)||!/^[a-f0-9]{40}$/.test(identity.candidate))throw new Error('invalid source identity')
const jobs=JSON.parse(readFileSync(jobsFile,'utf8')),placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')),status=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t')),backends=JSON.parse(readFileSync(join(dir,'backends.json'),'utf8'))
const issues:string[]=[],rows:any[]=[],counts:Record<string,number>={}
if(backends.where?.boat!==jobs.length||backends.fallbacks?.length)issues.push('non-boat execution')
for(const job of jobs){
 const path=join(dir,job.name+'.log'),text=existsSync(path)?readFileSync(path,'utf8'):gunzipSync(readFileSync(path+'.gz')).toString('utf8'),index=Number(/\.ts (\d+)/.exec(job.cmd)?.[1]),p=placement[job.name],st=status.filter(row=>row[0]===job.name),audit=parseReceipts(text,'bar',index,identity)
 const ends=text.split('\n').filter(line=>line.startsWith('BAR_RESOURCE_END ')).map(line=>JSON.parse(line.slice('BAR_RESOURCE_END '.length)))
 issues.push(...audit.issues.map(issue=>job.name+': '+issue));if(st.length!==1||st[0]?.[1]!=='0'||st[0]?.[3]!=='boat')issues.push(job.name+': scheduler failure');if(p?.exclusive!==true||p.co_tenants!==0)issues.push(job.name+': nonexclusive placement')
 for(const line of text.split('\n').filter(line=>line.startsWith('BAR_PAIR '))){
  const row=JSON.parse(line.slice(9)),outcomes:Record<string,unknown>={};if(row.cpu!==p?.cpu)issues.push(job.name+': CPU mismatch')
  for(const side of ['base','candidate']){
   const o=row.outcomes[side],r=o.resources;if(!r){issues.push(job.name+': missing resources');continue}
   const matches=ends.filter(end=>end.label===`${index}-${row.repeat}-${side}`)
   if(r.telemetryVersion===2&&(matches.length!==1||!validPeakRss(r,matches[0])))issues.push(job.name+': RSS samples/terminal marker mismatch')
   const delta=r.after.vmstat.oom_kill-r.before.vmstat.oom_kill,pids=r.seenPids.filter((pid:number)=>(r.kernel??'').includes('Killed process '+pid+' ')),killed=o.signal==='SIGKILL'||o.exit===137
   if(delta!==r.oomDelta||r.kernelPidOom!==((pids.length>0)&&/oom|Out of memory|Killed process/.test(r.kernel)))issues.push(job.name+': resource evidence mismatch')
   const kind=o.exit===0?'completed':o.exit===124?'strict-timeout':r.watchdog?'outer-watchdog':pids.length?'confirmed-kernel-oom':killed&&delta>0?'oom-correlated-pid-unconfirmed':killed?'unattributed-sigkill':o.error?'launcher-error':'nonzero'
   if(kind!==r.classification)issues.push(job.name+': classification mismatch')
   const attribution=kind==='unattributed-sigkill'&&checkedPortfolioHandoff(row.view,o)?'portfolio-parent-handoff':kind
   counts[attribution]=(counts[attribution]??0)+1
   outcomes[side]={attribution,answer:o.answer,exit:o.exit,signal:o.signal,wallMs:o.wallMs,classification:kind,oomDelta:delta,kernelPids:pids,peakRssKiB:r.telemetryVersion===2?r.peakRssKiB:null,minAvailableKiB:r.minAvailableKiB,journalExit:r.journalExit,resourcesVersion:r.telemetryVersion??1}
  }
  rows.push({index,task:row.task,repeat:row.repeat,view:row.view,cpu:row.cpu,outcomes})
 }
}
const complete=rows.filter(row=>row.outcomes.base?.exit===0&&row.outcomes.candidate?.exit===0),differences=complete.filter(row=>row.outcomes.base.answer!==row.outcomes.candidate.answer)
const output={identity,issues,rssScope:'250ms sampled process-tree maximum, not an exact OS high-water mark',pairs:rows.length,children:rows.length*2,counts,completePairs:complete.length,completeDifferences:differences,rows,scope:'Infrastructure attribution only. Incomplete children never establish a semantic candidate loss or a passing no-loss gate.'}
writeFileSync(join(dir,'resource-summary.json'),JSON.stringify(output,null,2)+'\n');console.log(JSON.stringify(output));if(issues.length)process.exitCode=1
