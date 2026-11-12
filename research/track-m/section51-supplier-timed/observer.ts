import {openSync,writeSync,closeSync,fsyncSync} from 'node:fs'
import {join} from 'node:path'
import {gzipSync} from 'node:zlib'
import {PrefixOracle,type Event,type Snapshot} from './oracle.ts'
import {encode,save} from './io.ts'
import {projectCountEvent,COUNT_PROJECTION} from './count-projection.ts'
import {TRACE_SCHEMA,TRACE_RESULT_SCHEMA,SERIALIZATION} from './trace-contract.ts'
import {MeasurementRows} from './measurement-rows.ts'
export type Limits={compressedBytes:number,rawBytes:number,records:number,recordBytes:number,bufferBytes:number,shardBytes:number,files:number}
export function observer(out:string,baseline:Snapshot,limits:Limits,identity:unknown){
 const oracle=new PrefixOracle(baseline),parts:Buffer[]=[]
 let measurement=new MeasurementRows(baseline,[])
 let pending=0,raw=0,compressed=0,records=0,events=0,index=0,fd:number|undefined,shardBytes=0,closed=false
 let firstViolation:unknown,limit:unknown
 const shards:{path:string,bytes:number}[]=[]
 function fail(reason:string){limit??={reason,records,events,raw,compressed};return false}
 function closeShard(){if(fd!==undefined){fsyncSync(fd);closeSync(fd);fd=undefined;shards[index-1]!.bytes=shardBytes}}
 function flush():boolean{
  if(!pending)return true
  const chunk=gzipSync(Buffer.concat(parts,pending),{level:1})
  if(compressed+chunk.length>limits.compressedBytes)return fail('compressed-byte-limit')
  if(fd===undefined||shardBytes+chunk.length>limits.shardBytes){closeShard();if(index>=limits.files)return fail('file-limit');const name='trace-'+String(index++).padStart(3,'0')+'.jsonl.gz';fd=openSync(join(out,name),'wx',0o600);shards.push({path:name,bytes:0});shardBytes=0}
  let at=0;while(at<chunk.length){const n=writeSync(fd!,chunk,at,chunk.length-at);if(n<=0)throw Error('short trace write');at+=n}
  compressed+=chunk.length;shardBytes+=chunk.length;parts.length=0;pending=0;return true
 }
 function record(row:unknown){
  if(limit||closed)return
  let bytes:Buffer
  try{bytes=encode(row,limits.recordBytes)}catch(e){fail(String(e));return}
  if(records+1>limits.records||raw+bytes.length>limits.rawBytes){fail('record-or-raw-byte-limit');return}
  if(pending&&pending+bytes.length>limits.bufferBytes&&!flush())return
  parts.push(bytes);pending+=bytes.length;raw+=bytes.length;records++
  if(pending>=limits.bufferBytes)flush()
 }
 record({kind:'header',schema:TRACE_SCHEMA,identity,limits,serialization:SERIALIZATION,countsProjection:COUNT_PROJECTION});record({kind:'baseline',snapshot:baseline})
 return {
  beginMeasurement(callerNames:readonly string[]){measurement=new MeasurementRows(baseline,callerNames)},
  measurement(verdict:any){return {...measurement.finish(verdict),traceComplete:!limit,traceLimit:limit??null,independentlyReplayed:false}},
  event(event:Event){measurement.observeLedger(event);events++;if(!firstViolation){try{oracle.observe(event)}catch(e){firstViolation={error:String(e),event}}}record({kind:'event',event})},
  count(event:unknown,snapshot:Snapshot){try{measurement.observe(event,snapshot);record({kind:'counts',...projectCountEvent(event),snapshot})}catch(e){fail(String(e))}},
  finish(snapshot:Snapshot){
   try{oracle.finish(snapshot)}catch(e){firstViolation??={error:String(e),snapshot}}
   record({kind:'final',snapshot,oracleViolation:firstViolation??null});flush();closeShard();closed=true
   // Once a cap stops the stream, no continuation, sampling, larger cap or
   // conformance claim is allowed. Native work may finish, but the pair is censored.
   const result={schema:TRACE_RESULT_SCHEMA,identity,serialization:SERIALIZATION,countsProjection:COUNT_PROJECTION,complete:!limit,limits,records,events,rawBytes:raw,compressedBytes:compressed,shards,limit:limit??null,oracle:{passed:!firstViolation&&!limit,qualification:false,firstViolation:firstViolation??null}}
   save(join(out,'trace-result.json'),result);return result
  }
 }
}
