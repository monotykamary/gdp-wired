import {spawn} from 'node:child_process'
import {fileURLToPath} from 'node:url'
import {parseRequest,Refusal,toolNames,toolDescriptions,inputSchema} from './protocol.ts'
import {configureRoots,type ConsultationOptions} from './workspace.ts'

type RecordValue=Record<string,unknown>
type StatusRecord={unit:string,revision:string,proven:boolean,checked:boolean,laws:string[],assumptions?:unknown}
export function createConsultation(options:ConsultationOptions={}) {
const roots=configureRoots(options.workspaceRoots)
const records=new Map<string,StatusRecord>()
let cancelActive:(()=>void)|undefined
let closed=false
let queue:Promise<unknown>=Promise.resolve()
const refusal=(code:string,message:string,fix:string)=>({schema:'gdp-wired/agent-tool/v1',ok:false,refusal:{code,message,fix},explanation:`${message} Fix: ${fix}`})
const result=(value:RecordValue)=>({content:[{type:'text',text:JSON.stringify(value)}],structuredContent:value,isError:value.ok===false})
function runWorker(tool:string,args:unknown,signal?:AbortSignal):Promise<RecordValue>{return new Promise((resolve,reject)=>{
  if(closed||signal?.aborted){reject(new Refusal('cancelled','Create a new session or retry without an aborted signal.','Consultation was cancelled.'));return}
  const input=JSON.stringify({tool,args,...(tool==='check'?{roots}:{})})
  if(Buffer.byteLength(input)>131072){reject(new Refusal('input-budget-exceeded','Reduce the request to128KiB.','Worker input exceeds128KiB.'));return}
  const worker=import.meta.url.endsWith('.ts')?'./worker.ts':'./worker.js'
  const child=spawn(process.execPath,[fileURLToPath(new URL(worker,import.meta.url))],{stdio:['pipe','pipe','pipe'],env:{PATH:process.env.PATH,HOME:process.env.HOME,TMPDIR:process.env.TMPDIR,LANG:'C.UTF-8',GDP_WORK_FULL:'1',GDP_WORK_W:'500000'}})
  let out='',err='',failure:Error|undefined
  // Wait for close before releasing the session queue: no overlap/orphan on cancellation.
  const fail=(e:Error)=>{if(failure)return;failure=e;child.kill('SIGTERM')}
  const cancel=()=>fail(new Refusal('cancelled','Retry in an open session with a fresh signal.','Consultation was cancelled; no conclusion is available.'))
  cancelActive=cancel
  signal?.addEventListener('abort',cancel,{once:true})
  if(signal?.aborted)cancel()
  child.stdout.on('data',(x:Buffer)=>{out+=x.toString();if(Buffer.byteLength(out)>262144)fail(new Error('worker output exceeds256KiB'))})
  child.stderr.on('data',(x:Buffer)=>{if(err.length<8192)err+=x.toString().slice(0,8192-err.length)})
  child.on('error',fail)
  child.on('close',code=>{cancelActive=undefined;signal?.removeEventListener('abort',cancel);if(failure){reject(failure);return}if(code!==0){reject(new Error(`worker exited (${code}): ${err}`));return}try{const v=JSON.parse(out) as RecordValue;if(!v||typeof v.ok!=='boolean'||v.schema!=='gdp-wired/agent-tool/v1')throw Error('invalid worker envelope');resolve(v)}catch{reject(new Error(`worker failed (${code}): ${err||'invalid JSON'}`))}})
  child.stdin.on('error',fail)
  child.stdin.end(input)
})}
async function dispatch(request:unknown,signal?:AbortSignal):Promise<RecordValue|null>{
  if(!request||typeof request!=='object'||Array.isArray(request))return {jsonrpc:'2.0',id:null,error:{code:-32600,message:'Invalid Request'}}
  const q=request as RecordValue, id=q.id
  if(id!==undefined&&id!==null&&typeof id!=='string'&&(typeof id!=='number'||!Number.isFinite(id)))return {jsonrpc:'2.0',id:null,error:{code:-32600,message:'Invalid request id'}}
  if(q.jsonrpc!=='2.0'||typeof q.method!=='string')return {jsonrpc:'2.0',id:id??null,error:{code:-32600,message:'Invalid Request'}}
  if(id===undefined)return null
  const respond=(r:unknown)=>({jsonrpc:'2.0',id,result:r})
  if(q.method==='initialize')return respond({protocolVersion:'2024-11-05',capabilities:{tools:{listChanged:false}},serverInfo:{name:'gdp-wired-agent-consult',version:'1.0.0'},instructions:roots.length?'Scalar rule tools plus explicit trusted-workspace check. Workspace check executes project code/imports; not an OS sandbox. Only server-configured roots authorize files. Counted-work profile provisional; external runtime is not counted. Cancellation/exhaustion are not conclusions.':'Data-only scalar natural rule consultation by default. Workspace check disabled: no server roots. Checked model proofs only; counted-work profile provisional. Cancellation/exhaustion are not conclusions.'})
  if(q.method==='ping')return respond({})
  if(q.method==='tools/list')return respond({tools:toolNames.map(name=>({name,description:toolDescriptions[name],inputSchema:inputSchema(name)}))})
  if(q.method!=='tools/call')return {jsonrpc:'2.0',id,error:{code:-32601,message:'Method not found'}}
  const params=q.params as RecordValue|undefined,tool=params?.name,args=params?.arguments
  try{
    if(closed||signal?.aborted)throw new Refusal('cancelled','Use an open session and a fresh signal.','Consultation was cancelled.')
    const parsed=parseRequest(tool,args)
    if(parsed.tool==='check'&&!roots.length)throw new Refusal('workspace-unconfigured','Configure trusted workspaceRoots on the server; callers cannot grant roots.','File checking is disabled by default.')
    if(parsed.tool==='status'){
      const key=parsed.unit+'@'+parsed.revision,known=records.get(key)
      if(!known)return respond(result({...refusal('missing-evidence','No local checked evidence exists for this exact unit/revision.','Call prove/check_change on the same rule and laws first; native labels require separately validated runtime evidence.'),tool:'status',subject:{unit:parsed.unit,revision:parsed.revision},label:'not adequate'}))
      const proven=known.proven===true&&known.checked===true
      return respond(result({schema:'gdp-wired/agent-tool/v1',tool:'status',ok:true,subject:{unit:known.unit,revision:known.revision},label:proven?'proven':'not adequate',result:{proven:known.proven,checked:known.checked,laws:known.laws,nativeLabel:null,assumptions:known.assumptions??null,source:'local isolated existing-kernel proof receipt'},explanation:`${known.unit}: ${proven?'all requested laws were proven and checked':'one or more requested laws remain unproven or unchecked'}. No conformance or harness-checked evidence is available; a supplied label is never accepted.`,budget:{apiCalls:0,work:{numerator:'0',denominator:'1'}}}))
    }
    const value=await runWorker(parsed.tool,args,signal)
    if(closed||signal?.aborted)throw new Refusal('cancelled','Retry in an open session with a fresh signal.','Consultation was cancelled; no evidence was retained.')
    if(Array.isArray(value.statusEvidence))for(const raw of value.statusEvidence){const s=raw as StatusRecord;if(typeof s.unit!=='string'||typeof s.revision!=='string'||!/^[a-f0-9]{64}$/.test(s.revision)||typeof s.proven!=='boolean'||typeof s.checked!=='boolean'||!Array.isArray(s.laws))continue;const key=s.unit+'@'+s.revision,old=records.get(key);if(!old||!old.proven||s.proven&&s.checked)records.set(key,s);while(records.size>256)records.delete(records.keys().next().value!)}
    delete value.statusEvidence
    return respond(result(value))
  }catch(e){return respond(result(e instanceof Refusal?refusal(e.code,e.message,e.fix):refusal('worker-failure',e instanceof Error?e.message:String(e),'Inspect stderr and retry the supported scalar request with counted budgets; do not infer a proof.')))}
}
function handle(request:unknown,options:{signal?:AbortSignal}={}):Promise<RecordValue|null>{
  const next=queue.then(()=>dispatch(request,options.signal))
  queue=next.catch(()=>undefined)
  return next
}
function close():Promise<void>{closed=true;records.clear();cancelActive?.();return queue.then(()=>undefined)}
async function call(tool:unknown,args:unknown,options:{signal?:AbortSignal}={}){
  const response=await handle({jsonrpc:'2.0',id:1,method:'tools/call',params:{name:tool,arguments:args}},options)
  return (response!.result as {structuredContent:RecordValue}).structuredContent
}
return {handle,call,close}
}

export async function serveStdio(options:ConsultationOptions={}){
const session=createConsultation(options)
const stop=()=>{void session.close();process.exitCode=1;process.stdin.destroy()}
process.on('SIGTERM',stop);process.on('SIGINT',stop)
try {
let pending='';for await(const chunk of process.stdin){pending+=chunk.toString();if(Buffer.byteLength(pending)>131072&&!pending.includes('\n'))throw new Error('MCP request exceeds128KiB');let split:number;while((split=pending.indexOf('\n'))>=0){const line=pending.slice(0,split);pending=pending.slice(split+1);if(!line.trim())continue;let response:RecordValue|null;try{if(Buffer.byteLength(line)>131072)throw Error('request too large');response=await session.handle(JSON.parse(line))}catch{response={jsonrpc:'2.0',id:null,error:{code:-32700,message:'Parse error or request exceeds128KiB'}}}if(response)process.stdout.write(JSON.stringify(response)+'\n')}}if(pending.trim())process.stdout.write(JSON.stringify({jsonrpc:'2.0',id:null,error:{code:-32700,message:'Incomplete JSON line'}})+'\n')
} finally {await session.close();process.removeListener('SIGTERM',stop);process.removeListener('SIGINT',stop)}
}

