// The driver and bootstrap import BUILTINS ONLY. Importers run only in fresh children.
import {readFileSync,writeFileSync,writeSync,mkdirSync,mkdtempSync,rmSync} from 'node:fs'
import {spawn} from 'node:child_process'
import {createHash} from 'node:crypto'
import {deflateRawSync} from 'node:zlib'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
const start=Date.now(),sha=(b:Buffer|string)=>createHash('sha256').update(b).digest('hex')
let seq=0,bytes=0,stage=''
function emit(event:string,data:unknown){const line=Buffer.from('LIFECYCLE_V3 '+JSON.stringify({seq:seq++,elapsedMs:Date.now()-start,event,data})+'\n');if(bytes+line.length>300000)throw Error('stdout evidence cap reached; previous receipts preserved');let i=0;while(i<line.length)i+=writeSync(1,line.subarray(i));bytes+=line.length}
function pack(raw:Buffer){return {encoding:'deflate-raw/base64',bytes:raw.length,sha256:sha(raw),data:deflateRawSync(raw).toString('base64')}}
const outcomes:Record<string,any>={}
async function phase(name:string,cmd:string,args:string[],budgetMs:number,cwd=stage){
 const timeout=Math.min(budgetMs,Math.max(1,27000-(Date.now()-start)-500))
 emit('phase-start',{name,cmd,args,budgetMs,timeout})
 const t=Date.now(),child=spawn(cmd,args,{cwd,stdio:['ignore','pipe','pipe'],env:{...process.env,PYTHONDONTWRITEBYTECODE:'1',LIFECYCLE_STAGE:stage}})
 let out=Buffer.alloc(0),err=Buffer.alloc(0),pending='',failure:string|null=null
 const stop=(why:string)=>{failure=failure??why;child.kill('SIGKILL')}
 const timer=setTimeout(()=>stop('child deadline exceeded'),timeout)
 child.stdout.on('data',(b:Buffer)=>{try{
  const remaining=128*1024-out.length;out=Buffer.concat([out,b.subarray(0,remaining)])
  if(b.length>remaining){stop('stdout cap exceeded');return}
  pending+=b.toString();let i:number
  while((i=pending.indexOf('\n'))>=0){const line=pending.slice(0,i);pending=pending.slice(i+1);if(line.startsWith('V3_BOUNDARY '))emit('boundary',{phase:name,...JSON.parse(line.slice(12))})}
 }catch(e){stop(String(e))}})
 child.stderr.on('data',(b:Buffer)=>{const remaining=128*1024-err.length;err=Buffer.concat([err,b.subarray(0,remaining)]);if(b.length>remaining)stop('stderr cap exceeded')})
 child.on('error',e=>{failure=String(e)})
 const [code,signal]=await new Promise<[number|null,string|null]>(resolve=>child.on('close',(code,signal)=>resolve([code,signal])))
 clearTimeout(timer)
 const status={name,code,signal,error:failure,durationMs:Date.now()-t,stdout:pack(out),stderr:pack(err)}
 outcomes[name]={...status,ok:!failure&&!signal,out:out.toString()}
 emit('phase-result',status)
 writeFileSync(join(stage,'work',name+'.stdout'),out);writeFileSync(join(stage,'work',name+'.stderr'),err)
 return outcomes[name]
}
const parse=(s:string)=>{try{return JSON.parse(s)}catch{return null}}
try{
 emit('start',{scope:'pure serialized model only; no OS lifecycle experiment',requestedSeconds:60,nativeSeconds:30,budgetsMs:{bootstrap:3000,load:1000,probe:2000,broken:4000,good:13000,certificates:3000},sequentialCeilingsMs:26000,finishTargetMs:27000,stdoutCap:300000,runtime:{bun:process.versions.bun,node:process.versions.node}})
 stage=mkdtempSync(join(tmpdir(),'astra-lifecycle-v3-'));mkdirSync(join(stage,'work'));writeFileSync(join(stage,'.owner'),'astra-lifecycle-v3',{flag:'wx'})
 const manifest=readFileSync('review-input/input-manifest.json');emit('manifest',{sha256:sha(manifest)})
 const bootstrap=await phase('bootstrap','bun',['--no-install','research/process-lifecycle/v3/bootstrap.ts',stage],3000,process.cwd())
 if(!bootstrap.ok||bootstrap.code!==0)throw Error('builtins-only bootstrap failed; no importer or model check attempted')
 const load=await phase('load','bun',['--no-install','research/process-lifecycle/v3/load.ts'],1000)
 if(!load.ok||load.code!==0)throw Error('fresh importer failed; no model checks attempted')
 const probe=await phase('probe','python3',['research/process-lifecycle/probe.py'],2000)
 const bad=await phase('broken','bun',['--no-install','core/cli.ts','check','research/process-lifecycle/broken.py','--json','--no-propose','--ms','500'],4000)
 const good=await phase('good','bun',['--no-install','core/cli.ts','check','research/process-lifecycle/model.py','--json','--no-propose','--ms','500','--cert','work/certs'],13000)
 const cert=await phase('certificates','bun',['--no-install','research/process-lifecycle/v3/certificates.ts'],3000)
 const g=parse(good.out),b=parse(bad.out),laws=g?.rules?.flatMap((r:any)=>r.laws)??[],negative=b?.rules?.flatMap((r:any)=>r.laws)??[]
 const certificateRows=cert.out.trim().split('\n').map(parse).filter(Boolean),certSummary=certificateRows.find((r:any)=>r.event==='certificate-summary')
 const passed=probe.ok&&probe.code===0&&good.ok&&good.code===0&&bad.ok&&bad.code===1&&laws.length===9&&laws.every((l:any)=>l.verdict==='proven')&&negative.length===1&&negative.every((l:any)=>l.verdict==='broken'&&l.run?.length&&l.replayed)&&cert.ok&&cert.code===0&&certSummary?.accepted===true
 emit('final',{passed,positiveLaws:laws.map((l:any)=>({name:l.name,verdict:l.verdict,cert:l.cert})),brokenLaws:negative,certificates:certSummary??null,probePassed:probe.ok&&probe.code===0,manifestSha256:sha(manifest),scope:'conditional safety only; no locking/deadline/delivery implementation claim'})
 process.exitCode=passed?0:2
}catch(e){try{emit('fatal',{error:String(e),completedPhases:Object.keys(outcomes)})}catch{}process.exitCode=2}
finally{if(stage)rmSync(stage,{recursive:true,force:true})}
