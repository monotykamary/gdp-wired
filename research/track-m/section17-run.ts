// Three paired/interleaved repetitions for each research config, one VM.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const out=process.argv[2];if(!out)throw new Error('OUTPUT required')
const parse=(text:string):any[]=>text.split('\n').flatMap(l=>{try{return [JSON.parse(l)]}catch{return []}})
const runs:any[]=[]
for(const repeat of [1,2,3])for(const comparison of repeat%2?['pool','combo']:['combo','pool']){
 const order=(repeat+(comparison==='combo'?1:0))%2?['baseline',comparison]:[comparison,'baseline']
 for(const mode of order){
  const id=`${comparison}-r${repeat}-${mode}`,journal=join(out,id+'.events.jsonl'),stdout=join(out,id+'.stdout.log'),stderr=join(out,id+'.stderr.log'),start=performance.now()
  console.log(JSON.stringify({event:'start',id}))
  const p=Bun.spawn(['/usr/bin/timeout','-s','KILL','60',process.execPath,join(out,mode+'.js'),'--ms','60000','--only','mldr','--skip','broken'],{env:{...process.env,TRACK_M_POOL_MODE:mode,TRACK_M_POOL_LOG:journal,GDP_COUNTS_TRACE:'',GDP_COUNTS_PROF:''},stdout:Bun.file(stdout),stderr:Bun.file(stderr)})
  const exitCode=await p.exited,wallMs=performance.now()-start,events=parse(readFileSync(journal,'utf8')),protocol=events.find(e=>e.event==='protocol-start'),done=events.find(e=>e.event==='protocol-end'),generated=events.filter(e=>e.event==='generated').flatMap(e=>e.laws),names=[...new Set(generated.map(l=>l.name))] as string[]
  const accepted=new Set(events.filter(e=>e.event==='checked-family').flatMap(e=>e.laws)),laws=names.map(name=>{const starts=events.filter(e=>e.event==='attempt-start'&&e.law===name),ends=events.filter(e=>e.event==='attempt-end'&&e.law===name),inflight=starts.length!==ends.length;return {law:name,verdict:accepted.has(name)?'checked':ends.some(e=>e.outcome==='proof')?'conditional-proof':starts.length?'unknown':'not-attempted',attempts:starts.length,completed:ends.length,censored:inflight,units:ends.reduce((n,e)=>n+e.usedUnits,0),wallMs:ends.reduce((n,e)=>n+e.wallMs,0),unitsComplete:!inflight}})
  const totalUnits=done?.usedUnits??(protocol?Math.max(0,...events.map(e=>e.units-protocol.startUnits)):0),search=parse(readFileSync(stdout,'utf8')).find(r=>r.id==='mldr'),censored=[124,137].includes(exitCode)
  const row={id,repeat,comparison,mode,exitCode,censored,wallMs,searchWallMs:done?.wallMs??null,totalUnits,totalUnitsComplete:!!done,unattributedUnits:done?totalUnits-laws.reduce((n,l)=>n+l.units,0):null,search,laws,draws:events.filter(e=>e.event==='law-draw'),targets:Object.fromEntries(['Inv2973','Inv*'].map(target=>{const found=laws.filter(l=>l.law.startsWith(target+':')||l.law===target);return [target,{generated:found.length>0,closed:found.some(l=>l.verdict==='checked'),laws:found.map(l=>l.law)}]}))}
  runs.push(row);writeFileSync(join(out,'measurements.json'),JSON.stringify({researchOnly:true,baseline:'5974b916',protocol:'mldr',strictWallSeconds:60,repeatCount:3,command:'run.ts --ms 60000 --only mldr --skip broken',runs},null,2)+'\n')
  console.log(JSON.stringify({event:'end',id,exitCode,censored,wallMs,totalUnits,laws:laws.length,targets:row.targets,verdict:search?.search?.verdict}))
  if(exitCode!==0&&!censored)throw new Error('unexpected child failure: '+id)
 }
}
