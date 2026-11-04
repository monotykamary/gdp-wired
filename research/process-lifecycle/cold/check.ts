// Fresh process: consumes saved documents only. No extraction or proof generation.
import {readFileSync,writeSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {spawnSync} from 'node:child_process'
import {basename} from 'node:path'
// Repo API is referenced only for types; runtime must use the verified frozen bundle.
import type * as CheckerModule from '../../../interchange/check.ts'
const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex'),need=(x:unknown,m:string)=>{if(!x)throw Error(m)}
let emitted=0
function emit(data:unknown){const b=Buffer.from('LIFECYCLE_COLD '+JSON.stringify(data)+'\n');if(emitted+b.length>250000)throw Error('evidence cap');let n=0;while(n<b.length)n+=writeSync(1,b.subarray(n));emitted+=b.length}
try{
 const raw=readFileSync('manifest.json'),manifest=JSON.parse(raw.toString()),pin=process.argv[2]
 need(sha(raw)===pin,'manifest pin mismatch')
 function inventory(){return manifest.files.map((f:any)=>({path:f.path,sha256:sha(readFileSync(f.path)),expected:f.sha256}))}
 const before=inventory();need(before.every((f:any)=>f.sha256===f.expected),'input drift before checking')
 // No source-tree fallback: this absolute file URL names only the staged checker.
 const stagedChecker=new URL('./checker/interchange/check.ts',import.meta.url)
 const {checkDocument}:typeof CheckerModule=await import(stagedChecker.href)
 emit({event:'inputs-before',manifestSha256:sha(raw),files:before})
 need(manifest.certificates.length===9&&new Set(manifest.certificates.map((c:any)=>c.name)).size===9,'expected nine distinct source laws')
 const results=[]
 for(const c of manifest.certificates){
  const bytes=readFileSync(c.path),beforeHash=sha(bytes);let metadataAccepted=false,metadataError:string|null=null,result:any
  let doc:any;try{doc=JSON.parse(bytes.toString())}catch(e){metadataError=String(e)}
  try{
   need(c.file==='research/process-lifecycle/model.py'&&c.entry==='Lifecycle','wrong full identity')
   const source=readFileSync('source/'+c.file,'utf8').split('\n')
   need(source[c.line-1]?.trim()===`# gdp: law ${c.name}: ${c.expr}`,'annotation mismatch')
   need(doc.meta.file===c.file&&doc.meta.entry===c.entry&&doc.meta.law===c.name&&doc.meta.expr===c.expr,'full source identity mismatch')
   need(doc.meta.where===basename(c.file)+':'+c.line,'location mismatch within full source identity')
   need(doc.kind===c.kind,'certificate kind mismatch');metadataAccepted=true
  }catch(e){metadataError=String(e)}
  // Invoke every document even when its metadata contract fails; neither verdict masks the other.
  try{result=checkDocument(doc)}catch(e){result={accepted:false,claims:[],error:String(e)}}
  const afterHash=sha(readFileSync(c.path)),accepted=metadataAccepted&&result.accepted&&result.claims.some((x:any)=>x.name===c.name&&x.accepted)&&beforeHash===afterHash
  const receipt={event:'certificate',path:c.path,name:c.name,beforeSha256:beforeHash,afterSha256:afterHash,metadataAccepted,metadataError,result,accepted}
  results.push(receipt);emit(receipt)
 }
 emit({event:'source-replay-start',exactActions:[0,-1,1,2]})
 const replay=spawnSync('python3',['-I','-S','-B','replay.py'],{encoding:'utf8',timeout:3000,killSignal:'SIGKILL',maxBuffer:32768,env:{...process.env,PYTHONDONTWRITEBYTECODE:'1'}})
 let receipt:any=null;try{receipt=JSON.parse(replay.stdout)}catch{}
 const replayAccepted=!replay.error&&!replay.signal&&replay.status===0&&receipt?.accepted===true&&JSON.stringify(receipt.actions)==='[0,-1,1,2]'&&receipt.states?.length===5&&receipt.states.at(-1).phase===2&&receipt.states.at(-1).inflight===1
 emit({event:'source-replay',code:replay.status,signal:replay.signal,error:replay.error?String(replay.error):null,stdout:replay.stdout,stderr:replay.stderr,stdoutSha256:sha(replay.stdout??''),receipt,accepted:replayAccepted})
 const after=inventory(),manifestAfter=sha(readFileSync('manifest.json')),unchanged=manifestAfter===pin&&after.every((f:any)=>f.sha256===f.expected)
 emit({event:'inputs-after',manifestSha256:manifestAfter,files:after,unchanged})
 const accepted=results.length===9&&results.every(r=>r.accepted)&&replayAccepted&&unchanged
 emit({event:'final',accepted,certificateCount:results.length,acceptedCertificates:results.filter(r=>r.accepted).length,claimCount:results.reduce((n,r)=>n+r.result.claims.length,0),exactSourceReplayAccepted:replayAccepted,inputsUnchanged:unchanged,manifestSha256:pin,v3OriginalFinalPassed:false,v3VerdictPreserved:true,noProver:true,noExtraction:true,noRegeneratedCertificates:true,scope:'new cold checker/source-replay acceptance only; conditional pure lifecycle model, not an actual supervisor'})
 process.exitCode=accepted?0:2
}catch(e){emit({event:'fatal',error:String(e)});process.exitCode=2}
