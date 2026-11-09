import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
export const base='b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c',cpu='AMD Ryzen 9 9950X 16-Core Processor'
const hash=(s:string)=>createHash('sha256').update(s).digest('hex')
export const expectedHarness:Record<string,Record<string,string>>=JSON.parse(readFileSync(new URL('./merge-harness-hashes.json',import.meta.url),'utf8'))
const lines=(s:string,prefix='')=>s.split('\n').flatMap(line=>{if(prefix&&!line.startsWith(prefix))return[];try{return[JSON.parse(line.slice(prefix.length))]}catch{return[]}})
export function decodeReceipt(text:string){
 const raw=text.split('\n').filter(line=>line.startsWith('BISECT_SUMMARY_GZIP '))
 if(raw.length!==1)throw new Error('expected one compressed summary')
 const summary=JSON.parse(gunzipSync(Buffer.from(raw[0]!.slice(20),'base64')).toString('utf8'))
 const traceLines=text.split('\n').filter(line=>line.startsWith('BISECT_TRACES_GZIP '))
 if(traceLines.length!==1)throw new Error('complete raw trace missing; recover original worker stdout')
 const trace=gunzipSync(Buffer.from(traceLines[0]!.slice(19),'base64')).toString('utf8')
 if(hash(trace)!==summary.traceSha256)throw new Error('raw trace digest mismatch')
 return {summary,traces:JSON.parse(trace)}
}
export function auditSummary(row:any,traces:any[],revision:string,minimumRepeats=5){
 const issues:string[]=[],check=(ok:boolean,message:string)=>{if(!ok)issues.push(message)}
 check(row.revision===revision&&row.baseline===base,'revision mismatch');check(row.cpu===cpu,'wrong CPU');check(row.strictMs===60000,'budget mismatch');check(row.repeats>=minimumRepeats&&row.records?.length===row.repeats,'missing repeats')
 check(row.meta?.base?.revision===base&&row.meta?.candidate?.revision===revision&&row.meta?.base?.clean===true&&row.meta?.candidate?.clean===true,'source restore mismatch')
 for(const side of ['base','candidate']){const expected=expectedHarness[side==='base'?base:revision];check(!!expected&&Object.keys(row.hashes?.[side]??{}).length===Object.keys(expected).length&&Object.entries(expected).every(([path,digest])=>row.hashes?.[side]?.[path]===digest),'protected harness differs from pinned source: '+side)}
 const seen=new Set<number>()
 for(const record of row.records??[]){
  check(Number.isInteger(record.repeat)&&record.repeat>=1&&record.repeat<=row.repeats&&!seen.has(record.repeat),'invalid or duplicate repeat');seen.add(record.repeat)
  const expected=(row.replica+record.repeat)%2?['candidate','base']:['base','candidate'];check(JSON.stringify(record.order)===JSON.stringify(expected),'order mismatch')
  for(const side of ['base','candidate']){
   const out=record.outcomes?.[side],matches=traces.filter(t=>t.repeat===record.repeat&&t.side===side)
   check(matches.length===1,`${record.repeat}/${side}: missing or duplicate raw trace`);if(!out||matches.length!==1)continue
   const raw=matches[0];check(hash(raw.stdout)===out.stdoutSha256&&hash(raw.stderr)===out.stderrSha256,`${record.repeat}/${side}: trace hash mismatch`)
   check(JSON.stringify(lines(raw.stdout).filter(r=>r.id==='consensus_forall'))===JSON.stringify(out.results),`${record.repeat}/${side}: semantic trace mismatch`)
   check(JSON.stringify(lines(raw.stderr,'LANE_I_PROFILE '))===JSON.stringify(out.profile),`${record.repeat}/${side}: phase trace mismatch`)
   check(JSON.stringify(lines(raw.stderr,'BISECT_LAW '))===JSON.stringify(out.attempts),`${record.repeat}/${side}: law trace mismatch`)
   const finished=out.profile?.find((p:any)=>p.event==='result'),generated=out.profile?.find((p:any)=>p.event==='candidates'),zero=finished?finished.at-finished.searchMs:undefined
   check(out.generationWallMs===(generated&&zero!==undefined?generated.at-zero:null),`${record.repeat}/${side}: generation metric mismatch`)
   check(out.finitePassMs===(generated?.profile?.finiteHoudini??0),`${record.repeat}/${side}: finite metric mismatch`)
   check(out.preProverWallMs===(out.attempts?.length&&zero!==undefined?out.attempts[0].at-zero:null),`${record.repeat}/${side}: pre-prover metric mismatch`)
   if(out.exit===0&&out.results?.[0]?.search)check(out.attempts?.length>0&&out.profile.filter((p:any)=>p.event==='result').length===1,`${record.repeat}/${side}: missing complete phase trace`)
   for(const attempt of out.attempts??[])check(typeof attempt.law==='string'&&['full','work','wallMs','units'].every(k=>Number.isFinite(attempt[k])&&attempt[k]>=0),`${record.repeat}/${side}: invalid law metric`)
  }
 }
 check(traces.length===2*row.repeats,'raw trace cardinality')
 return issues
}
const median=(xs:number[])=>{const a=xs.filter(Number.isFinite).sort((a,b)=>a-b);return a.length?a.length%2?a[a.length>>1]!:(a[a.length/2-1]!+a[a.length/2]!)/2:null}
export function summarize(rows:any[]){
 const groups=new Map<string,any[]>()
 for(const row of rows)groups.set(row.revision,[...(groups.get(row.revision)??[]),...row.records.map((record:any)=>({...record,replica:row.replica}))])
 return [...groups].map(([revision,records])=>{
  const complete=records.filter(r=>['base','candidate'].every(side=>r.outcomes[side].exit===0&&r.outcomes[side].results?.length===1&&['proven','unknown','refuted'].includes(r.outcomes[side].results[0].search?.verdict)))
  const proven=complete.filter(r=>['base','candidate'].every(side=>r.outcomes[side].results[0].search.verdict==='proven'))
  const metric=(side:string,key:string)=>median(proven.map(r=>r.outcomes[side].results[0].search[key]))
  const perLaw=new Map<string,{full:number[],work:number[],wall:number[]}>()
  for(const record of proven){const sums=new Map<string,{base:any,candidate:any}>();for(const side of ['base','candidate'] as const)for(const a of record.outcomes[side].attempts){const pair=sums.get(a.law)??{base:{full:0,work:0,wall:0},candidate:{full:0,work:0,wall:0}};pair[side].full+=a.full;pair[side].work+=a.work;pair[side].wall+=a.wallMs;sums.set(a.law,pair)}for(const [law,s]of sums){const g=perLaw.get(law)??{full:[],work:[],wall:[]};g.full.push(s.candidate.full-s.base.full);g.work.push(s.candidate.work-s.base.work);g.wall.push(s.candidate.wall-s.base.wall);perLaw.set(law,g)}}
  return {revision,attempted:records.length,complete:complete.length,bothProven:proven.length,qualified:complete.length>=5,paired:{msDelta:median(proven.map(r=>r.outcomes.candidate.results[0].search.ms-r.outcomes.base.results[0].search.ms)),generationDelta:median(proven.map(r=>r.outcomes.candidate.generationWallMs-r.outcomes.base.generationWallMs)),postGenerationDelta:median(proven.map(r=>(r.outcomes.candidate.results[0].search.ms-r.outcomes.candidate.generationWallMs)-(r.outcomes.base.results[0].search.ms-r.outcomes.base.generationWallMs)))},lost:complete.filter(r=>r.outcomes.base.results[0].search.verdict==='proven'&&r.outcomes.candidate.results[0].search.verdict!=='proven').map(r=>({replica:r.replica,repeat:r.repeat})),base:{ms:metric('base','ms'),work:metric('base','work'),full:metric('base','full')},candidate:{ms:metric('candidate','ms'),work:metric('candidate','work'),full:metric('candidate','full')},generationWallMs:{base:median(complete.map(r=>r.outcomes.base.generationWallMs)),candidate:median(complete.map(r=>r.outcomes.candidate.generationWallMs))},finitePassMs:{base:median(complete.map(r=>r.outcomes.base.finitePassMs)),candidate:median(complete.map(r=>r.outcomes.candidate.finitePassMs))},lawDeltas:[...perLaw].map(([law,g])=>({law,full:median(g.full),work:median(g.work),wallMs:median(g.wall)})).sort((a,b)=>(b.full??0)-(a.full??0))}
 })
}
if(import.meta.main){
 const args=process.argv.slice(2);if(args.length<2||args.length%2)throw new Error('usage: merge-bisect-audit.ts output-dir jobs.json [output-dir jobs.json ...]')
 const accepted:any[]=[],issues:string[]=[],skips:any[]=[],seen=new Set<string>()
 for(let i=0;i<args.length;i+=2){const dir=args[i]!,jobs=JSON.parse(readFileSync(args[i+1]!,'utf8')),placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')),backends=JSON.parse(readFileSync(join(dir,'backends.json'),'utf8')),status=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(row=>row.split('\t'))
  if(backends.where?.boat!==jobs.length||backends.fallbacks?.length)issues.push(dir+': non-boat execution')
  for(const job of jobs){const identity=/merge-bisect\.ts ([a-f0-9]{40}) (\d+) (\d+)/.exec(job.cmd);if(!identity){issues.push(job.name+': malformed job');continue}const file=join(dir,job.name+'.log'),text=existsSync(file)?readFileSync(file,'utf8'):existsSync(file+'.gz')?gunzipSync(readFileSync(file+'.gz')).toString('utf8'):'';const s=status.filter(row=>row[0]===job.name),p=placement[job.name]
   if(s.length!==1||s[0]?.[1]!=='0'||s[0]?.[3]!=='boat'){issues.push(job.name+': failed scheduler result');continue}
   const cpuSkips=lines(text,'BISECT_CPU_SKIP ')
   if(cpuSkips.length){if(cpuSkips.length!==1||cpuSkips[0].cpu===cpu||cpuSkips[0].cpu!==p?.cpu||text.includes('BISECT_SUMMARY_GZIP'))issues.push(job.name+': invalid CPU skip');else skips.push({name:job.name,...cpuSkips[0]});continue}
   try{const {summary,traces}=decodeReceipt(text),errors=auditSummary(summary,traces,identity[1]!);if(summary.replica!==Number(identity[2])||summary.repeats!==Number(identity[3]))errors.push('job identity mismatch');if(p?.exclusive!==true||p.co_tenants!==0||p.cpu!==cpu)errors.push('placement mismatch');const key=summary.revision+':'+summary.replica;if(seen.has(key))errors.push('duplicate replica');seen.add(key);if(errors.length)issues.push(...errors.map(error=>job.name+': '+error));else accepted.push(summary)}catch(e){issues.push(job.name+': '+String(e))}
  }
 }
 const output={issues,skips,acceptedJobs:accepted.length,byRevision:summarize(accepted)};writeFileSync(join(args[0]!,'bisection-audit.json'),JSON.stringify(output,null,2)+'\n');console.log(JSON.stringify(output));if(issues.length)process.exitCode=1
}
