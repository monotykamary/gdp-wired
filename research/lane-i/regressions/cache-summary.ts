// Interpret the screening separately from the required ordinary strict cohort.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {verifyTrace,baseline,candidate,type Pair} from './receipt-audit.ts'
type Outcome=Pair['outcomes']['base']&{side:string,rowsShared?:string,guard?:boolean,cache:unknown[],lawEvents?:unknown[]}
type RecordRow={group:number,repeat:number,cpu:string,strictMs:number,meta:Pair['meta'],order:string[],outcomes:Record<string,Outcome>,patch?:{file:string,before:string,after:string}}
const dir=process.argv[2],guard=process.argv[3]==='guard';if(!dir)throw new Error('probe output directory required')
const workers=guard?2:4,variants=['base','candidate',guard?'candidate-refuted-guard':'candidate-no-shared-rows'],issues:string[]=[],rows:unknown[]=[],verdicts:Record<string,Record<string,number>>={}
const status=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t')),placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')),backend=JSON.parse(readFileSync(join(dir,'backends.json'),'utf8'))
if(status.length!==workers||backend.where?.boat!==workers||backend.fallbacks?.length)issues.push('invalid worker boat roster')
const jsonLines=(text:string,prefix='')=>text.split('\n').flatMap(line=>{if(prefix&&!line.startsWith(prefix))return[];try{return[JSON.parse(line.slice(prefix.length))]}catch{return[]}})
for(let group=1;group<=workers;group++){
 const name=(guard?'refuted-guard-probe-':'row-cache-probe-')+group,p=placement[name],s=status.filter(row=>row[0]===name),records:RecordRow[]=jsonLines(readFileSync(join(dir,name+'.log'),'utf8'),guard?'GUARD_PROBE ':'CACHE_PROBE ')
 if(s.length!==1||s[0]![1]!=='0'||s[0]![3]!=='boat'||p?.exclusive!==true||p.co_tenants!==0)issues.push(name+': failed worker or nonexclusive placement')
 if(records.length!==2||new Set(records.map(row=>row.repeat)).size!==2)issues.push(name+': missing/duplicate pair')
 for(const row of records){
  if(row.group!==group||![1,2].includes(row.repeat)||row.cpu!==p?.cpu||row.strictMs!==60000)issues.push(name+': invalid identity/CPU/deadline')
  if(row.meta.base.revision!==baseline||row.meta.candidate.revision!==candidate||!row.meta.base.clean||!row.meta.candidate.clean)issues.push(name+': source mismatch')
  if(row.order.length!==3||new Set(row.order).size!==3||variants.some(v=>!row.order.includes(v)))issues.push(name+': bad order')
  const outcomes:Record<string,unknown>={}
  let names:string|undefined
  for(const variant of variants){
   const o=row.outcomes[variant];if(!o){issues.push(name+': missing variant '+variant);continue}
   issues.push(...verifyTrace(o).map(issue=>name+'/'+variant+': '+issue))
   const raw=gunzipSync(Buffer.from(o.traceGzipBase64,'base64')).toString('utf8'),separator='\n---stderr---\n',at=raw.indexOf(separator),stdout=raw.slice(0,at),stderr=raw.slice(at+separator.length),results=jsonLines(stdout).filter(r=>r?.id==='consensus_forall'),profile=jsonLines(stderr,'LANE_I_PROFILE '),cache=jsonLines(stderr,'LANE_I_CACHE ')
   if(JSON.stringify(results)!==JSON.stringify(o.results)||JSON.stringify(profile)!==JSON.stringify(o.profile)||JSON.stringify(cache)!==JSON.stringify(o.cache))issues.push(name+'/'+variant+': raw/summary mismatch')
   if(o.side!==(variant==='base'?'base':'candidate')||(guard?o.guard!==(variant==='candidate-refuted-guard'):o.rowsShared!==(variant==='candidate-no-shared-rows'?'0':'1')))issues.push(name+'/'+variant+': wrong ablation flag')
   if(guard){if(JSON.stringify(jsonLines(stderr,'LANE_I_LAW '))!==JSON.stringify(o.lawEvents))issues.push(name+'/'+variant+': law-event mismatch');if(row.patch?.file!=='core/counts.ts'||row.patch.before!=='5dbe4953b89f3791c71a29816aa5c0294611cb96c661708c29ead1dc0424b31d'||row.patch.after!=='69dc7ef220906a593670a7742312d4015dd6997587844b653ad1d0b4402fee86')issues.push(name+': prototype patch mismatch')}
   const generated=JSON.stringify(profile.filter(r=>r.event==='candidate-names').map(r=>r.names));if(names!==undefined&&names!==generated)issues.push(name+': generated name lists differ');names=generated
   const result=results[0],finish=profile.find(r=>r.event==='result'),generation=profile.find(r=>r.event==='candidates'),zero=finish?finish.at-finish.searchMs:undefined,outcome=o.exit===0&&results.length===1?result.search.verdict:'incomplete-process'
   verdicts[variant]??={};verdicts[variant]![outcome]=(verdicts[variant]![outcome]??0)+1
   const attempts=[...stderr.matchAll(/counts: try (.*?) \| ls (\d+) pass ([01]) ms (\d+) took (\d+) wall (\d+) \[(.*?)\] -> (.*)/g)].map(m=>({labelPrefix:m[1],family:Number(m[2]),pass:Number(m[3]),allowance:Number(m[4]),units:Number(m[5]),wallMs:Number(m[6]),profile:m[7],outcome:m[8]}))
   outcomes[variant]={outcome,exit:o.exit,signal:o.signal,wallMs:o.wallMs,result:result?.search,generationWallMs:generation&&zero!==undefined?generation.at-zero:null,finiteFilterMs:generation?.profile?.filter??null,generationProfile:generation?.profile,resultProfile:finish?.profile,cache,attempts,...(guard?{lawEvents:o.lawEvents}:{}),stdoutSha256:o.stdoutSha256,stderrSha256:o.stderrSha256}
  }
  rows.push({group,repeat:row.repeat,cpu:row.cpu,order:row.order,...(guard?{patch:row.patch}:{}),outcomes})
 }
}
const report={researchOnly:true,ordinaryStrictCohort:false,baseline,candidate,batch:backend.boat?.batch,issues,verdicts,rows,scope:'Screening, not a production fix. Incomplete processes are not semantic unknowns. Trace labels are prefixes, not unique full law identities.'}
writeFileSync(join(dir,guard?'guard-summary.json':'cache-summary.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({issues,verdicts,rows:rows.length}));if(issues.length)process.exitCode=1
