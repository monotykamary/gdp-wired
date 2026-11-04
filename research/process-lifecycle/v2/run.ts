import {readFileSync,writeFileSync,writeSync,mkdirSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {deflateRawSync} from 'node:zlib'
const start=Date.now(),sha=(b:Buffer|string)=>createHash('sha256').update(b).digest('hex')
let seq=0,bytes=0
function emit(event:string,data:unknown){const line=Buffer.from('LIFECYCLE_V2 '+JSON.stringify({seq:seq++,elapsedMs:Date.now()-start,event,data})+'\n');if(bytes+line.length>300000)throw Error('stdout evidence cap reached; previous receipts preserved');let i=0;while(i<line.length)i+=writeSync(1,line.subarray(i));bytes+=line.length}
function pack(text:string){const raw=Buffer.from(text);return {encoding:'deflate-raw/base64',bytes:raw.length,sha256:sha(raw),data:deflateRawSync(raw).toString('base64')}}
const outcomes:Record<string,any>={}
function phase(name:string,cmd:string,args:string[],budgetMs:number){
 const timeout=Math.min(budgetMs,Math.max(1,27000-(Date.now()-start)-500))
 emit('phase-start',{name,cmd,args,budgetMs,timeout})
 const t=Date.now(),r=spawnSync(cmd,args,{encoding:'utf8',timeout,killSignal:'SIGKILL',maxBuffer:128*1024,env:{...process.env,PYTHONDONTWRITEBYTECODE:'1'}})
 const out=r.stdout??'',err=r.stderr??''
 const status={name,code:r.status,signal:r.signal,error:r.error?String(r.error):null,durationMs:Date.now()-t,stdout:pack(out),stderr:pack(err)}
 outcomes[name]={...status,ok:!r.error&&!r.signal,out}
 emit('phase-result',status)
 writeFileSync('lifecycle-v2-work/'+name+'.stdout',out);writeFileSync('lifecycle-v2-work/'+name+'.stderr',err)
 return outcomes[name]
}
const parse=(s:string)=>{try{return JSON.parse(s)}catch{return null}}
try{
 emit('start',{scope:'pure serialized model only; no OS lifecycle experiment',requestedSeconds:60,nativeSeconds:30,budgetsMs:{setup:4000,probe:2000,broken:4000,good:13000,certificates:3000},sequentialCeilingsMs:26000,finishTargetMs:27000,stdoutCap:300000,runtime:{bun:process.versions.bun,node:process.versions.node}})
 mkdirSync('lifecycle-v2-work',{recursive:false})
 const manifest=readFileSync('review-input/input-manifest.json');emit('manifest',{sha256:sha(manifest)})
 const setup=phase('setup','bun',['--no-install','research/process-lifecycle/v2/phase.ts','setup'],4000)
 if(!setup.ok||setup.code!==0)throw Error('pinned setup failed; no model checks attempted')
 const probe=phase('probe','python3',['research/process-lifecycle/probe.py'],2000)
 const bad=phase('broken','bun',['--no-install','core/cli.ts','check','research/process-lifecycle/broken.py','--json','--no-propose','--ms','500'],4000)
 const good=phase('good','bun',['--no-install','core/cli.ts','check','research/process-lifecycle/model.py','--json','--no-propose','--ms','500','--cert','lifecycle-v2-work/certs'],13000)
 const cert=phase('certificates','bun',['--no-install','research/process-lifecycle/v2/phase.ts','certificates'],3000)
 const g=parse(good.out),b=parse(bad.out),laws=g?.rules?.flatMap((r:any)=>r.laws)??[],negative=b?.rules?.flatMap((r:any)=>r.laws)??[]
 const certificateRows=cert.out.trim().split('\n').map(parse).filter(Boolean),certSummary=certificateRows.find((r:any)=>r.event==='certificate-summary')
 const passed=probe.ok&&probe.code===0&&good.ok&&good.code===0&&bad.ok&&bad.code===1&&laws.length===9&&laws.every((l:any)=>l.verdict==='proven')&&negative.length===1&&negative.every((l:any)=>l.verdict==='broken'&&l.run?.length&&l.replayed)&&cert.ok&&cert.code===0&&certSummary?.accepted===true
 emit('final',{passed,positiveLaws: laws.map((l:any)=>({name:l.name,verdict:l.verdict,cert:l.cert})),brokenLaws:negative,certificates:certSummary??null,probePassed:probe.ok&&probe.code===0,manifestSha256:sha(manifest),scope:'conditional safety only; no locking/deadline/delivery implementation claim'})
 process.exitCode=passed?0:2
}catch(e){try{emit('fatal',{error:String(e),completedPhases:Object.keys(outcomes)})}catch{}process.exitCode=2}
