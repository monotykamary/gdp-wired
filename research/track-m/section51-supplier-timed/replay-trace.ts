// Bounded postprocessing of the same instrumented arm; no proof or extra root.
import {readFileSync,createReadStream,lstatSync} from 'node:fs'
import {createGunzip} from 'node:zlib'
import {join} from 'node:path'
import {PrefixOracle} from './oracle.ts'
import {save} from './io.ts'
import {loadAuthority,validateHeader,stable} from './trace-contract.ts'
import {COUNT_PROJECTION} from './count-projection.ts'
import {MeasurementRows} from './measurement-rows.ts'
const [input,out]=process.argv.slice(2);if(!input||!out)throw Error('sealed input and output required')
const read=(name:string)=>{const path=join(out,name);if(!lstatSync(path).isFile()||lstatSync(path).size>64*1024*1024)throw Error('oversized/nonregular trace metadata');return JSON.parse(readFileSync(path,'utf8'))}
const verdict=read('verdict.json'),trace=read('trace-result.json'),authority=loadAuthority(input,verdict,trace),limits=authority.limits
const originalLaws=read('original-laws.json')
if(!Array.isArray(originalLaws)||originalLaws.some((law:any)=>typeof law?.name!=='string'))throw Error('missing original safety inventory')
const measurement=new MeasurementRows(verdict.initial,originalLaws.map((law:any)=>law.name))
let raw=0,compressed=0,records=0,events=0,oracle:PrefixOracle|undefined,final:any,violation:unknown,stage='header'
for(const shard of trace.shards){
 const path=join(out,shard.path),stat=lstatSync(path)
 if(!stat.isFile()||stat.size!==shard.bytes||stat.size>limits.shardBytes)throw Error('actual shard size/type mismatch')
 compressed+=stat.size;if(compressed>limits.compressedBytes)throw Error('decode compressed limit')
 const stream=createReadStream(path,{highWaterMark:65536}).pipe(createGunzip({chunkSize:65536}));let pending=Buffer.alloc(0)
 for await(const data of stream){
  const chunk=Buffer.from(data);raw+=chunk.length;if(raw>limits.rawBytes)throw Error('decode raw limit')
  pending=Buffer.concat([pending,chunk]);let nl:number
  while((nl=pending.indexOf(10))>=0){
   if(nl+1>limits.recordBytes)throw Error('decode record limit')
   const record=JSON.parse(pending.subarray(0,nl).toString());pending=pending.subarray(nl+1);records++
   if(records>limits.records)throw Error('decode count limit')
   if(stage==='header'){validateHeader(record,authority);stage='baseline'}
   else if(stage==='baseline'){if(record.kind!=='baseline'||stable(record.snapshot)!==stable(verdict.initial))throw Error('baseline mismatch');oracle=new PrefixOracle(record.snapshot);stage='events'}
   else if(stage==='events'&&record.kind==='event'){measurement.observeLedger(record.event);events++;if(!violation){try{oracle!.observe(record.event)}catch(e){violation={error:String(e),event:record.event}}}}
   else if(stage==='events'&&record.kind==='counts'){
    measurement.observe(record.event,record.snapshot)
    if(record.projection!==COUNT_PROJECTION||!Array.isArray(record.omittedCallbacks)||record.omittedCallbacks.length>1||record.omittedCallbacks.some((k:any)=>k!=='replayEvidence'))throw Error('foreign counts projection')
   }
   else if(stage==='events'&&record.kind==='final'){final=record.snapshot;try{oracle!.finish(final)}catch(e){violation??={error:String(e),snapshot:final}}stage='done'}
   else throw Error('unexpected or duplicated stream record')
  }
  if(pending.length>=limits.recordBytes)throw Error('decode unterminated record limit')
 }
 if(pending.length)throw Error('partial shard record')
}
if(stage!=='done'||records!==trace.records||events!==trace.events||raw!==trace.rawBytes||compressed!==trace.compressedBytes||stable(final)!==stable(verdict.final))throw Error('full stream accounting mismatch')
const result={schema:'mldr-3g-trace-replay/v2',sealSHA256:authority.sealSHA256,configSHA256:authority.configSHA256,rootRaw:authority.rootRaw,complete:true,records,events,rawBytes:raw,compressedBytes:compressed,oraclePassed:!violation,firstViolation:violation??null,qualification:false}
const measured={...measurement.finish(verdict),traceComplete:true,traceLimit:null,independentlyReplayed:false}
if(stable(measured)!==stable(read('measurement-rows.json')))throw Error('live and replay measurement reports differ')
save(join(out,'measurement-rows-replayed.json'),{...measured,independentlyReplayed:true})
save(join(out,'trace-replay.json'),result)
if(result.oraclePassed!==trace.oracle.passed)throw Error('live/offline oracle disagreement')
