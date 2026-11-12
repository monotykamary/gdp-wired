// Pure trace assertions plus bounded reading of the separately sealed authority.
import {readFileSync,lstatSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
import {COUNT_PROJECTION} from './count-projection.ts'
import {requireRootRaw} from './root-policy.ts'
export const TRACE_SCHEMA='mldr-3g-ledger-trace/v2',TRACE_RESULT_SCHEMA='mldr-3g-trace-result/v2',SERIALIZATION='mldr-3g-data/v2'
export const stable=(x:any):string=>JSON.stringify(x,(_k,v)=>v&&typeof v==='object'&&!Array.isArray(v)?Object.fromEntries(Object.keys(v).sort().map(k=>[k,v[k]])):v)
function need(v:unknown,s:string):asserts v{if(!v)throw Error(s)}
const sha=(b:Uint8Array)=>createHash('sha256').update(b).digest('hex')
const integer=(n:any)=>Number.isSafeInteger(n)&&n>0
export function validateLimits(l:any){
 const keys=['compressedBytes','rawBytes','records','recordBytes','bufferBytes','shardBytes','files']
 need(l&&stable(Object.keys(l).sort())===stable(keys.sort())&&keys.every(k=>integer(l[k])),'invalid sealed trace limit vector')
 need(l.recordBytes<=l.rawBytes&&l.bufferBytes<=l.rawBytes&&l.shardBytes<=l.compressedBytes,'inconsistent sealed trace limits')
}
export function validateTraceResult(config:any,verdict:any,trace:any){
 validateLimits(config.trace)
 const rootRaw=requireRootRaw(config)
 need(config.source.commit==='9eb09b8326fc2670fad6725f774ab1b252c4d343'&&config.source.tree==='20e56881dd613158a5ac53b3633bd8b3e3db8ed5'&&config.profileSHA256==='a5f077dc8156a7bb550dc0ed279de96b20aa3a167c32fbaaaaad925fc9f8a272','wrong sealed production identity')
 const i=verdict.identity
 need(config.serialization?.schema===SERIALIZATION&&verdict.schema==='mldr-3g-diagnostic/v2'&&i?.serialization===SERIALIZATION,'unsupported native data schema')
 need(verdict.mode==='instrumented'&&i?.mode==='instrumented'&&i.protocol==='mldr'&&i.rootRaw===config.rootRaw&&i.sourceCommit===config.source.commit&&i.sourceTree===config.source.tree&&i.profileSHA256===config.profileSHA256&&i.runtime?.version===config.runtime.bun.version&&i.runtime?.sha256===config.runtime.bun.sha256,'wrong instrumented invocation')
 need(trace.schema===TRACE_RESULT_SCHEMA&&trace.serialization===SERIALIZATION&&trace.countsProjection===COUNT_PROJECTION&&trace.complete===true&&trace.limit===null,'incomplete/foreign trace result')
 need(stable(trace.identity)===stable(i)&&stable(trace.limits)===stable(config.trace)&&stable(verdict.trace)===stable(trace),'trace differs from sealed authority or native verdict')
 const l=config.trace
 need(integer(trace.records)&&trace.records<=l.records&&Number.isSafeInteger(trace.events)&&trace.events>=0&&trace.events<=trace.records&&integer(trace.rawBytes)&&trace.rawBytes<=l.rawBytes&&integer(trace.compressedBytes)&&trace.compressedBytes<=l.compressedBytes,'trace totals exceed sealed limits')
 need(Array.isArray(trace.shards)&&trace.shards.length>0&&trace.shards.length<=l.files,'trace shard count exceeds sealed limit')
 let total=0
 for(const [index,s] of trace.shards.entries()){
  need(s.path==='trace-'+String(index).padStart(3,'0')+'.jsonl.gz'&&integer(s.bytes)&&s.bytes<=l.shardBytes,'invalid trace shard name/size')
  total+=s.bytes;need(Number.isSafeInteger(total)&&total<=l.compressedBytes,'trace shard total exceeds sealed limit')
 }
 need(total===trace.compressedBytes&&typeof trace.oracle?.passed==='boolean','trace summary mismatch')
 return {limits:l,identity:i,rootRaw}
}
export function validateHeader(header:any,authority:{limits:any,identity:any}){
 need(header.kind==='header'&&header.schema===TRACE_SCHEMA&&header.serialization===SERIALIZATION&&header.countsProjection===COUNT_PROJECTION,'foreign trace header schema')
 need(stable(header.identity)===stable(authority.identity)&&stable(header.limits)===stable(authority.limits),'trace header identity/limits mismatch')
}
export function loadAuthority(input:string,verdict:any,trace:any){
 const read=(name:string)=>{const p=join(input,name);need(lstatSync(p).isFile()&&lstatSync(p).size<=1024*1024,'oversized/nonregular authority file');return readFileSync(p)}
 const index=read('INPUTS.sha256'),configBytes=read('CONFIG.json'),sealBytes=read('SEAL.json'),seal=JSON.parse(sealBytes.toString()),authorization=JSON.parse(read('AUTHORIZATION.json').toString())
 const configEntries=index.toString().split('\n').filter(line=>/  (?:\.\/)?CONFIG\.json$/.test(line))
 need(configEntries.length===1&&configEntries[0]!.split(' ')[0]===sha(configBytes),'CONFIG not bound to input index')
 need(seal.inputIndexSHA256===sha(index)&&authorization.sealSHA256===sha(sealBytes),'input authority seal mismatch')
 const config=JSON.parse(configBytes.toString()),authority=validateTraceResult(config,verdict,trace)
 return {...authority,sealSHA256:sha(sealBytes),configSHA256:sha(configBytes)}
}
