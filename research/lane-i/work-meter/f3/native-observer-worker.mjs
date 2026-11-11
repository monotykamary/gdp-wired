import {parentPort,workerData} from 'node:worker_threads'
import {Session} from 'node:inspector'
import {writeSync} from 'node:fs'
import {archiveProfile} from './profile-archive.mjs'
import {selectProfileWindow} from './profile-window.mjs'
import {readNativeSpan,sameNativeSpan} from './native-spans.mjs'
const shared=new Int32Array(workerData),session=new Session(),now=()=>performance.now()
const emit=(tag,value)=>writeSync(1,tag+' '+JSON.stringify(value)+'\n')
const post=(method,params={})=>new Promise((resolve,reject)=>session.post(method,params,(error,result)=>error?reject(error):resolve(result)))
let last=Atomics.load(shared,1),since=now(),span=readNativeSpan(shared),spanSince=since,reports=0,busy=false,stopping=false,invalid=0,archiveBytes=0
const keepalive=setInterval(()=>{},1000)
try{
 session.connectToMainThread();await post('Profiler.enable');await post('Profiler.setSamplingInterval',{interval:10000});await post('Profiler.start')
 const stop=async()=>{if(stopping||busy)return;stopping=true;clearInterval(timer);try{await post('Profiler.stop')}finally{clearInterval(keepalive);session.disconnect();parentPort.close()}}
 parentPort.on('message',message=>{if(message==='stop')void stop()})
 const timer=setInterval(async()=>{
  if(busy||stopping)return
  if(Atomics.load(shared,0)!==1){if(Atomics.load(shared,0)===2)void stop();return}
  const next=Atomics.load(shared,1),time=now(),before=readNativeSpan(shared)
  if(!sameNativeSpan(span,before)){span=before;spanSince=time}
  if(next!==last){last=next;since=time;return}
  if(time-since<=250||reports>=16)return
  busy=true
  try{
   const {profile}=await post('Profiler.stop'),raw=selectProfileWindow(profile,time-since)
   const heartbeatAfter=Atomics.load(shared,1),whileRunning=Atomics.load(shared,0)===1,after=readNativeSpan(shared)
   const stable=heartbeatAfter===next&&whileRunning,nativeMs=time-spanSince
   const native=before.id>0&&nativeMs>250?selectProfileWindow(profile,nativeMs):undefined
   const attributed=stable&&sameNativeSpan(before,after)&&!!native?.timing.valid&&native.timing.samplesInWindow>0
   let archive
   if(stable||!raw.timing.valid&&invalid++<2){archive=archiveProfile(profile);archiveBytes+=archive.gzipBytes;if(archiveBytes>2*1024*1024)throw Error('total profile archive limit; cannot qualify capture');emit('F3_NATIVE_PROFILE',{report:reports+1,...archive});if(!raw.timing.valid)emit('F3_NATIVE_INVALID_PROFILE',{sha256:archive.sha256,bytes:archive.bytes,retained:true})}
   emit(stable?'F3_NATIVE_RAW_SILENCE':'F3_NATIVE_WINDOW_CHANGED',{rawSilentMs:time-since,whileRunning,heartbeatBefore:next,heartbeatAfter,stable,reports:++reports,profileSha256:archive?.sha256,stack:raw.stack,profileWindow:raw.timing,native:{before,after,quietMs:nativeMs,attributed,stack:native?.stack,profileWindow:native?.timing},scope:'bounded Node invocation attribution; not exact native instructions, Bun F3 or W'})
   await post('Profiler.start');since=now()
  }catch(error){emit('F3_NATIVE_ERROR',{error:String(error)});process.exitCode=1}
  finally{busy=false;if(Atomics.load(shared,0)===2)void stop()}
 },100)
 parentPort.postMessage({ready:true})
}catch(error){clearInterval(keepalive);parentPort.postMessage({error:String(error)});session.disconnect();parentPort.close()}
