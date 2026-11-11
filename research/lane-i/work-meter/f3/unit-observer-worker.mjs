import {parentPort,workerData} from 'node:worker_threads'
import {Session} from 'node:inspector'
import {writeSync} from 'node:fs'
import {readUnitSnapshot,observeUnitProgress} from './unit-snapshot.mjs'
import {selectProfileWindow} from './profile-window.mjs'
import {archiveProfile} from './profile-archive.mjs'
const {buffer,weights}=workerData,control=new Int32Array(buffer,0,4),session=new Session(),traceNow=()=>performance.now()
const emit=(tag,value)=>writeSync(1,tag+' '+JSON.stringify(value)+'\n')
const post=(method,params={})=>new Promise((resolve,reject)=>session.post(method,params,(error,result)=>error?reject(error):resolve(result)))
let previous=readUnitSnapshot(buffer,weights),since=traceNow(),lastTick=since,maxTickGapMs=0,busy=false,stopping=false,reports=0,invalidSnapshots=0,coverageCapped=false,archiveBytes=0
const keepalive=setInterval(()=>{},1000)
try{
 session.connectToMainThread();await post('Profiler.enable');await post('Profiler.setSamplingInterval',{interval:10000});await post('Profiler.start')
 const stop=async()=>{if(stopping||busy)return;stopping=true;clearInterval(timer);try{await post('Profiler.stop')}finally{emit('F3_UNIT_OBSERVER_SUMMARY',{reports,invalidSnapshots,coverageCapped,maxTickGapMs});clearInterval(keepalive);session.disconnect();parentPort.close()}}
 parentPort.on('message',message=>{if(message==='stop')void stop()})
 const timer=setInterval(async()=>{
  const time=traceNow();maxTickGapMs=Math.max(maxTickGapMs,time-lastTick);lastTick=time
  if(Atomics.load(control,1)!==1){if(Atomics.load(control,1)===2)void stop();return}
  const before=readUnitSnapshot(buffer,weights),progress=observeUnitProgress(previous,before)
  if(!before.valid){invalidSnapshots++;return}
  if(!progress.eligible||progress.advanced){previous=before;since=time;return}
  previous=before
  if(time-since<=250||busy||stopping)return
  if(reports>=16){coverageCapped=true;return}
  busy=true
  try{
   const {profile}=await post('Profiler.stop'),selected=selectProfileWindow(profile,time-since),after=readUnitSnapshot(buffer,weights)
   const stable=observeUnitProgress(before,after).unchanged&&Atomics.load(control,1)===1
   const archive=archiveProfile(profile);archiveBytes+=archive.gzipBytes
   if(archiveBytes>2*1024*1024)throw Error('total profile archive limit; capture cannot qualify')
   emit('F3_UNIT_PROFILE',{report:reports+1,...archive})
   emit(stable?'F3_UNIT_SILENCE':'F3_UNIT_CHANGED',{report:++reports,unitSilentMs:time-since,unitsBefore:before.units,unitsAfter:after.units,stable,stack:selected.stack,profileWindow:selected.timing,profileSha256:archive.sha256})
   await post('Profiler.start')
  }catch(error){emit('F3_UNIT_ERROR',{error:String(error)});process.exitCode=1;coverageCapped=true}
  finally{busy=false;if(Atomics.load(control,1)===2)void stop()}
 },100)
 parentPort.postMessage({ready:true})
}catch(error){clearInterval(keepalive);parentPort.postMessage({error:String(error)});session.disconnect();parentPort.close()}
