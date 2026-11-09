import {readFileSync,writeFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const dir=import.meta.dir,bytes=readFileSync(dir+'/accepted-summaries.json.gz'),audit=JSON.parse(readFileSync(dir+'/cohort-audit.json','utf8'))
if(audit.issues.length||createHash('sha256').update(bytes).digest('hex')!==audit.acceptedSha256)throw Error('unqualified or altered accepted summaries')
const groups=JSON.parse(gunzipSync(bytes).toString()),revisions=[...new Set(groups.map((row:any)=>row.revision))]
const summaries=revisions.map(revision=>{
 const cohorts=groups.filter((row:any)=>row.revision===revision),records=cohorts.flatMap((row:any)=>row.records.map((record:any)=>({...record,replica:row.replica,cpu:row.cpu})))
 const sides=Object.fromEntries(['base','candidate'].map(side=>{
  const xs=records.map((record:any)=>({replica:record.replica,repeat:record.repeat,...record.outcomes[side].results[0].search}))
  return[side,{proven:xs.filter((x:any)=>x.verdict==='proven').length,unknown:xs.filter((x:any)=>x.verdict==='unknown').length,work:[...new Set(xs.map((x:any)=>x.work))],full:[...new Set(xs.map((x:any)=>x.full))],notProven:xs.filter((x:any)=>x.verdict!=='proven').map((x:any)=>({replica:x.replica,repeat:x.repeat,verdict:x.verdict,ms:x.ms,work:x.work,full:x.full}))}]
 }))
 const firstBound=records.map((r:any)=>{const a=r.outcomes.candidate.attempts.find((x:any)=>x.law==="Decision keeps members's bound through members$Decision"&&x.pass===1);return a?{outcome:a.outcome,work:a.work,full:Math.round(a.full*1e6)/1e6,countCompletion:a.profile?.['#count-completion']??0}:null})
 return{revision,cpus:[...new Set(records.map((r:any)=>r.cpu))],repeats:records.length,...sides,firstBound:[...new Set(firstBound.map((x:any)=>JSON.stringify(x)))].map((x:any)=>JSON.parse(x))}
})
const result={issues:[],summaries,scope:'Historical b09 paired diagnosis; not a gate against main8214a543.',finalGate:false}
writeFileSync(dir+'/repair-summary.json',JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify(result))
