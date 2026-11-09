// A diagnostic receipt is not a proof or permission to accept a red gate.
import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
export const baseline='b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c',candidate='b09da82d9ada6e0cdc31f943292cfea727f5752e'
const targetCpu='AMD Ryzen 9 9950X 16-Core Processor'
const sha=(text:string)=>createHash('sha256').update(text).digest('hex')
type Verdict={verdict?:string,ms?:number,work?:number,full?:number,why?:string}
type Outcome={exit:number|null,signal?:string|null,results?:{id:string,search:Verdict}[],answer?:string,wallMs:number,generationWallMs?:number|null,preAttemptWallMs?:number|null,profile?:{event:string,profile?:Record<string,number>,names?:string[]}[],attempts?:{law:string,units:number,wallMs:number}[],stages?:{stage?:string,answer?:string,work?:number,full?:number}[],wrong?:boolean,trackedChanges?:string,stdoutSha256:string,stderrSha256:string,traceGzipBase64:string}
export type Pair={group?:number,index?:number,repeat:number,cpu:string,strictMs?:number,strictSeconds?:number,view?:string,task?:string,bun?:string,meta:Record<'base'|'candidate',{revision:string,clean:boolean}>,outcomes:Record<'base'|'candidate',Outcome>}
function rawTrace(outcome:Outcome){
 const text=gunzipSync(Buffer.from(outcome.traceGzipBase64,'base64')).toString('utf8'),separator='\n---stderr---\n',at=text.indexOf(separator)
 if(at<0)throw new Error('missing trace separator')
 return{stdout:text.slice(0,at),stderr:text.slice(at+separator.length)}
}
const attemptsIn=(text:string)=>[...text.matchAll(/counts: try (.*?) \| ls (\d+) pass ([01]) ms (\d+) took (\d+) wall (\d+) \[(.*?)\] -> (.*)/g)].map(m=>({law:m[1],family:Number(m[2]),pass:Number(m[3]),allowance:Number(m[4]),units:Number(m[5]),wallMs:Number(m[6]),outcome:m[8]}))
const jsonLines=(text:string,prefix='')=>text.split('\n').flatMap(line=>{if(prefix&&!line.startsWith(prefix))return[];try{return[JSON.parse(line.slice(prefix.length))]}catch{return[]}})
export function verifyTrace(outcome:Outcome):string[]{
 try{
  const text=gunzipSync(Buffer.from(outcome.traceGzipBase64,'base64')).toString('utf8'),separator='\n---stderr---\n',at=text.indexOf(separator)
  if(at<0)return['missing trace separator']
  return[...(sha(text.slice(0,at))===outcome.stdoutSha256?[]:['stdout hash mismatch']),...(sha(text.slice(at+separator.length))===outcome.stderrSha256?[]:['stderr hash mismatch'])]
 }catch{return['invalid compressed trace']}
}
export function auditPair(pair:Pair,kind:'strict'|'bar',index:number){
 const issues:string[]=[],check=(ok:boolean,message:string)=>{if(!ok)issues.push(message)}
 check(Number.isInteger(pair.repeat)&&pair.repeat>=1&&pair.repeat<=3,'repeat outside 1..3')
 check((kind==='strict'?pair.group:pair.index)===index,'job identity mismatch')
 check(kind==='strict'?pair.strictMs===60000:pair.strictSeconds===60,'non-original time budget')
 check(typeof pair.cpu==='string'&&pair.cpu.length>0,'missing CPU')
 if(kind==='strict')check(pair.cpu===targetCpu,'wrong strict CPU')
 if(kind==='bar'&&pair.view==='tip')check(pair.bun==='1.4.4','wrong TIP runtime')
 const metrics:Record<string,unknown>={}
 for(const side of ['base','candidate'] as const){
  const meta=pair.meta?.[side],outcome=pair.outcomes?.[side]
  check(meta?.revision===(side==='base'?baseline:candidate)&&meta.clean===true,side+': source mismatch')
  if(!outcome){issues.push(side+': missing outcome');continue}
  for(const issue of verifyTrace(outcome))issues.push(side+': '+issue)
  check(Number.isFinite(outcome.wallMs)&&outcome.wallMs>=0,side+': invalid wall time')
  if(kind==='strict'){
   try { const raw=rawTrace(outcome),results=jsonLines(raw.stdout).filter(row=>row?.id==='consensus_forall'),profile=jsonLines(raw.stderr,'LANE_I_PROFILE ');check(JSON.stringify(results)===JSON.stringify(outcome.results),side+': semantic result differs from trace');check(JSON.stringify(profile)===JSON.stringify(outcome.profile),side+': timing differs from trace');check(JSON.stringify(attemptsIn(raw.stderr))===JSON.stringify(outcome.attempts),side+': per-law work differs from trace') } catch { issues.push(side+': cannot verify semantic trace') }
   check(outcome.exit===0,side+': strict process failed or timed out')
   const result=outcome.results?.[0]
   check(outcome.results?.length===1&&result?.id==='consensus_forall',side+': missing/duplicate semantic result')
   check(['proven','unknown','refuted'].includes(result?.search?.verdict??''),side+': invalid semantic verdict')
   check(typeof result?.search?.ms==='number'&&result.search.ms>=0&&result.search.ms<=60000,side+': invalid internal time')
   check(outcome.profile?.filter(row=>row.event==='result').length===1,side+': missing/duplicate result timing')
   metrics[side]={...result?.search,wallMs:outcome.wallMs,generationWallMs:outcome.generationWallMs,preAttemptWallMs:outcome.preAttemptWallMs,finitePassMs:outcome.profile?.find(row=>row.event==='candidates')?.profile?.finiteHoudini,attempts:outcome.attempts,names:outcome.profile?.filter(row=>row.event==='candidate-names').map(row=>row.names)}
  }else{
   try { const stages=jsonLines(rawTrace(outcome).stdout);check(JSON.stringify(stages)===JSON.stringify(outcome.stages),side+': stages differ from trace');const last=pair.view?.startsWith('its')?[...stages].reverse().find(stage=>'answer'in stage):stages.at(-1),answer=(pair.view==='tip'&&last?.stage!=='answer'?undefined:last?.answer)??(outcome.exit===124?'timeout':'error');check(answer===outcome.answer,side+': answer differs from trace') } catch { issues.push(side+': cannot verify bar trace') }
   check(typeof outcome.answer==='string',side+': missing bar answer')
   check(outcome.trackedChanges==='',side+': tracked source changed')
   check(!outcome.wrong,side+': wrong benchmark answer')
   metrics[side]={answer:outcome.answer,exit:outcome.exit,signal:outcome.signal,wallMs:outcome.wallMs,stages:outcome.stages}
  }
 }
 return{issues,pair:{index,repeat:pair.repeat,cpu:pair.cpu,view:pair.view,task:pair.task,metrics}}
}
export function parseReceipts(text:string,kind:'strict'|'bar',index:number){
 const prefix=kind==='strict'?'STRICT_PAIR ':'BAR_PAIR ',issues:string[]=[],pairs:ReturnType<typeof auditPair>['pair'][]=[],seen=new Set<number>(),skips:{group:number,cpu:string}[]=[]
 for(const line of text.split('\n')){
  if(line.startsWith('STRICT_CPU_SKIP ')){
   try{const row=JSON.parse(line.slice(16));if(kind!=='strict'||row.group!==index||typeof row.cpu!=='string'||row.cpu===targetCpu)issues.push('invalid CPU skip');skips.push(row)}catch{issues.push('malformed CPU skip')}
  }
  if(!line.startsWith(prefix))continue
  try{const row:Pair=JSON.parse(line.slice(prefix.length)),audit=auditPair(row,kind,index);if(seen.has(row.repeat))issues.push('duplicate repeat '+row.repeat);seen.add(row.repeat);issues.push(...audit.issues.map(issue=>'repeat '+row.repeat+': '+issue));pairs.push(audit.pair)}catch{issues.push('malformed pair record')}
 }
 if(skips.length){if(skips.length!==1||pairs.length)issues.push('mixed or duplicate CPU skip')}
 else if(pairs.length!==3||seen.size!==3)issues.push('expected exactly three paired repeats')
 return{issues,pairs,skips}
}
if(import.meta.main){
 const [kind,dir,jobsPath]=process.argv.slice(2)
 if((kind!=='strict'&&kind!=='bar')||!dir||!jobsPath)throw new Error('usage: receipt-audit.ts strict|bar output-dir jobs.json')
 const jobs:{name:string,cmd:string}[]=JSON.parse(readFileSync(jobsPath,'utf8')),status=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t')),placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')),backend=JSON.parse(readFileSync(join(dir,'backends.json'),'utf8'))
 const issues:string[]=[],pairs:unknown[]=[],skips:unknown[]=[]
 if(status.length!==jobs.length||new Set(status.map(row=>row[0])).size!==jobs.length)issues.push('summary roster cardinality')
 if(backend.where?.boat!==jobs.length||backend.fallbacks?.length)issues.push('non-boat or fallback execution')
 for(const job of jobs){
  const rows=status.filter(row=>row[0]===job.name),p=placement[job.name]
  if(rows.length!==1||rows[0]![1]!=='0'||rows[0]![3]!=='boat')issues.push(job.name+': failed/missing scheduler result')
  if(p?.exclusive!==true||p.co_tenants!==0)issues.push(job.name+': nonexclusive placement')
  const raw=join(dir,job.name+'.log'),gz=raw+'.gz'
  if(!existsSync(raw)&&!existsSync(gz)){issues.push(job.name+': missing log');continue}
  const text=existsSync(gz)?gunzipSync(readFileSync(gz)).toString('utf8'):readFileSync(raw,'utf8'),match=/\.ts (\d+)(?: |$)/.exec(job.cmd)
  if(!match){issues.push(job.name+': missing job index');continue}
  const read=parseReceipts(text,kind,Number(match[1]));issues.push(...read.issues.map(issue=>job.name+': '+issue));pairs.push(...read.pairs);skips.push(...read.skips)
  if(read.pairs.some(row=>row.cpu!==p?.cpu)||read.skips.some(row=>row.cpu!==p?.cpu))issues.push(job.name+': CPU differs from placement')
 }
 if(kind==='strict'&&pairs.length<10)issues.push('fewer than ten matching-CPU pairs')
 const output={kind,baseline,candidate,batch:backend.boat?.batch,issues,pairs,skips,scope:'Receipt audit only, not a proof or final gate. Bar error outcomes remain errors.'}
 writeFileSync(join(dir,'receipt-audit.json'),JSON.stringify(output,null,2)+'\n');console.log(JSON.stringify({kind,pairs:pairs.length,skips:skips.length,issues}));if(issues.length)process.exitCode=1
}
