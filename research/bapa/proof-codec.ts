// Lossless data only. The outer CAPTURE.json is the sole complete marker.
// The inherited streaming writer's O(graph-nodes) identity table is NOT a RAM cap.
import {createHash} from 'node:crypto'
import {openSync,closeSync,readSync,readFileSync,writeFileSync,fsyncSync,mkdirSync,renameSync,unlinkSync,lstatSync} from 'node:fs'
import {join,dirname} from 'node:path'
import {StringDecoder} from 'node:string_decoder'
import {writeGraphCapsule,type Manifest} from './proof-graph.ts'
import {inspectProvenance,retainedLawCoverage,projectionOf,type NativeBundle} from './proof-capture.ts'
const hash=(data:string|Uint8Array)=>createHash('sha256').update(data).digest('hex')
const SHARD=8*1024*1024, LINE=1024*1024, TEXT=16*1024
function syncDir(path:string):void { const fd=openSync(path,'r');try{fsyncSync(fd)}finally{closeSync(fd)} }
function writeNew(path:string,text:string):void { const fd=openSync(path,'wx');try{writeFileSync(fd,text);fsyncSync(fd)}finally{closeSync(fd)} }
export type CaptureManifest = {
  schema:'bapa-native-certificate/v1', complete:true, route:NativeBundle['route'],
  identity:NativeBundle['identity'], graphManifestSha256:string, projection:NativeBundle['projection'],
  publicLawIndices?:number[]|null, familyLaws?:number, certificateKeys?:string[], terms:number
}
export function writeFamilyCapsule(directory:string,bundle:NativeBundle,metadata?:(value:object)=>unknown):{manifestSha256:string} {
  if(JSON.stringify(bundle.projection)!==JSON.stringify(projectionOf(bundle)))throw Error('invalid projection qualification')
  mkdirSync(directory,{recursive:false})
  const graph=join(directory,'graph'), pending=join(directory,'CAPTURE.pending'), complete=join(directory,'CAPTURE.json')
  try {
    writeGraphCapsule(graph,bundle,{metadata})
    const manifest:CaptureManifest={schema:'bapa-native-certificate/v1',complete:true,route:bundle.route,identity:bundle.identity,projection:bundle.projection,
      graphManifestSha256:hash(readFileSync(join(graph,'manifest.json'))),
      ...('final'in bundle?{publicLawIndices:bundle.publicLawIndices,familyLaws:bundle.final.laws.length,certificateKeys:Object.keys(bundle.final.proof.certs)}:{}),terms:bundle.terms.terms.length}
    const text=JSON.stringify(manifest)+'\n'
    writeNew(pending,text)
    syncDir(graph);syncDir(directory)
    renameSync(pending,complete)
    syncDir(directory);syncDir(dirname(directory))
    return {manifestSha256:hash(text)}
  } catch(error) {
    // Keep incomplete data for custody; never advertise it as a certificate.
    try{unlinkSync(complete)}catch{}
    try{syncDir(directory)}catch{}
    throw error
  }
}
export type ReadLimits={maxBytes:number,maxNodes:number,maxStrings:number,maxArrayLength:number,maxShards:number}
const nat=(v:unknown):number=>{if(typeof v!=='number'||!Number.isSafeInteger(v)||v<0)throw Error('invalid graph integer');return v}
const bit=(v:unknown):boolean=>{if(typeof v!=='boolean')throw Error('invalid graph bit');return v}
function boundedFile(path:string,max:number):Buffer {
  const s=lstatSync(path)
  if(!s.isFile()||s.size>max)throw Error('invalid or oversized capsule file')
  const data=readFileSync(path)
  if(data.length!==s.size||data.length>max)throw Error('capsule file changed')
  return data
}
function* records(directory:string,manifest:Manifest):Generator<unknown[]> {
  for(let i=0;i<manifest.shards.length;i++) {
    const shard=manifest.shards[i]!,name=`shard-${String(i).padStart(6,'0')}.jsonl`,path=join(directory,name)
    if(shard.name!==name||nat(shard.bytes)<1||shard.bytes>SHARD||!/^[0-9a-f]{64}$/.test(shard.sha256))throw Error('invalid graph shard')
    const stat=lstatSync(path)
    if(!stat.isFile()||stat.size!==shard.bytes)throw Error('graph shard size mismatch')
    const fd=openSync(path,'r'),buffer=Buffer.alloc(128*1024),decoder=new StringDecoder('utf8'),digest=createHash('sha256')
    let text='',bytes=0
    try {
      for(;;) {
        const n=readSync(fd,buffer,0,buffer.length,null);if(!n)break
        bytes+=n;if(bytes>shard.bytes)throw Error('graph shard grew')
        digest.update(buffer.subarray(0,n));text+=decoder.write(buffer.subarray(0,n))
        let end:number
        while((end=text.indexOf('\n'))>=0) {
          const line=text.slice(0,end);if(Buffer.byteLength(line)+1>LINE)throw Error('graph line exceeds bound')
          const row:unknown=JSON.parse(line);if(!Array.isArray(row))throw Error('invalid graph record')
          yield row;text=text.slice(end+1)
        }
        if(Buffer.byteLength(text)>LINE)throw Error('graph line exceeds bound')
      }
      text+=decoder.end()
      if(text.length||bytes!==shard.bytes||digest.digest('hex')!==shard.sha256)throw Error('graph shard integrity mismatch')
    } finally {closeSync(fd)}
  }
}
// Fresh-process data loader. All sizes are explicit input limits, not forecasts.
// No term registration, native checking, function deserialization or evaluation.
export function readCertificateGraph(directory:string,expectedManifestSha256:string,limits:ReadLimits,onMetadata?:(object:object,value:unknown)=>void):unknown {
  // Check required names: Object.values would silently skip an omitted bound.
  for(const key of ['maxBytes','maxNodes','maxStrings','maxArrayLength','maxShards'] as const) {
    const value=limits?.[key]
    if(typeof value!=='number'||!Number.isSafeInteger(value)||value<1)throw Error('invalid graph limit: '+key)
  }
  if(!/^[0-9a-f]{64}$/.test(expectedManifestSha256))throw Error('missing graph manifest binding')
  const bytes=boundedFile(join(directory,'manifest.json'),Math.min(limits.maxBytes,8*1024*1024))
  if(hash(bytes)!==expectedManifestSha256)throw Error('graph manifest binding mismatch')
  const m=JSON.parse(bytes.toString()) as Manifest
  if(m.schema!=='closing-graph/v1'||m.complete!==true||!Array.isArray(m.shards)||!m.shards.length||m.shards.length>limits.maxShards)throw Error('invalid graph manifest')
  if(nat(m.nodes)>limits.maxNodes||nat(m.strings)>limits.maxStrings)throw Error('graph object limit')
  let total=bytes.length
  for(const s of m.shards){total+=nat(s.bytes);if(!Number.isSafeInteger(total)||total>limits.maxBytes)throw Error('graph byte limit')}
  const protos:Record<string,object|null>={object:Object.prototype,null:null,array:Array.prototype,map:Map.prototype,set:Set.prototype,
    error:Error.prototype,typeError:TypeError.prototype,rangeError:RangeError.prototype,referenceError:ReferenceError.prototype,
    syntaxError:SyntaxError.prototype,uriError:URIError.prototype,evalError:EvalError.prototype,aggregateError:AggregateError.prototype}
  const objects:object[]=[],tags:string[]=[],strings:string[]=[],seals:[boolean,boolean][]=[],arrays:number[]=[]
  let root:unknown[]|undefined,open=-1,stringId=-1,stringParts:string[]=[]
  const metadataIds=new Set<number>()
  for(const row of records(directory,m)) {
    const [kind]=row
    if(kind==='root') {if(root||row.length!==2||!Array.isArray(row[1]))throw Error('invalid graph root');root=row[1]}
    else if(kind==='node') {
      const id=nat(row[1]),tag=row[2]
      if(row.length!==4||open!==-1||id!==objects.length||id>=m.nodes||typeof tag!=='string'||!Object.hasOwn(protos,tag))throw Error('invalid graph node')
      if(tag==='array') {const n=nat(row[3]);if(n>limits.maxArrayLength||n>0xffffffff)throw Error('array limit');objects.push(new Array(n));arrays[id]=n}
      else {if(row[3]!==null)throw Error('invalid node length');objects.push(tag==='map'?new Map():tag==='set'?new Set():Object.create(protos[tag]!))}
      tags.push(tag);open=id
    } else if(kind==='string') {
      const id=nat(row[1]);if(row.length!==2||stringId!==-1||id!==strings.length||id>=m.strings)throw Error('invalid graph string')
      stringId=id;strings.push('');stringParts=[]
    } else if(kind==='text') {
      if(row.length!==3||nat(row[1])!==stringId||typeof row[2]!=='string'||row[2].length>TEXT)throw Error('invalid graph text')
      stringParts.push(row[2])
    } else if(kind==='string-end') {
      if(row.length!==2||nat(row[1])!==stringId)throw Error('invalid graph string end')
      strings[stringId]=stringParts.join('');stringId=-1;stringParts=[]
    } else if(['prop','map','set','meta','seal'].includes(String(kind))) {
      const id=nat(row[1]),sizes:Record<string,number>={prop:7,map:4,set:3,meta:3,seal:4}
      if(id!==open||row.length!==sizes[String(kind)])throw Error('graph edge outside its node')
      if(kind==='seal'){seals[id]=[bit(row[2]),bit(row[3])];open=-1}
      if(kind==='meta'){if(metadataIds.has(id)||!onMetadata)throw Error('unexpected graph metadata');metadataIds.add(id)}
    } else throw Error('unknown graph record')
  }
  if(!root||open!==-1||stringId!==-1||objects.length!==m.nodes||strings.length!==m.strings)throw Error('incomplete graph records')
  const deref=(wire:unknown):unknown=>{
    if(!Array.isArray(wire))throw Error('invalid graph reference')
    const [kind,value]=wire
    if(kind==='u'&&wire.length===1)return undefined
    if(wire.length!==2)throw Error('invalid graph reference arity')
    if(kind==='v'&&(value===null||typeof value==='boolean'||typeof value==='string'&&value.length<=TEXT))return value
    if(kind==='n'&&typeof value==='string'&&/^[0-9a-f]{16}$/.test(value)){const n=Buffer.from(value,'hex').readDoubleBE(),check=Buffer.alloc(8);check.writeDoubleBE(n);if(check.toString('hex')!==value)throw Error('numeric bit pattern not preserved by this runtime');return n}
    if(kind==='b'&&typeof value==='string'&&/^-?(0|[1-9][0-9]*)$/.test(value))return BigInt(value)
    const i=nat(value)
    if(kind==='r'&&i<objects.length)return objects[i]
    if(kind==='s'&&i<strings.length)return strings[i]
    throw Error('unknown graph reference')
  }
  const metadata:[object,unknown][]=[]
  for(const row of records(directory,m)) {
    const kind=row[0];if(['root','node','string','text','string-end','seal'].includes(String(kind)))continue
    const id=nat(row[1]),object=objects[id]!
    if(kind==='prop') {
      const key=deref(row[2]);if(typeof key!=='string'||Object.hasOwn(object,key))throw Error('invalid or duplicate graph property')
      if(tags[id]==='array'&&/^(0|[1-9][0-9]*)$/.test(key)&&Number(key)<0xffffffff&&Number(key)>=arrays[id]!)throw Error('array property past length')
      Object.defineProperty(object,key,{value:deref(row[3]),writable:bit(row[4]),enumerable:bit(row[5]),configurable:bit(row[6])})
    } else if(kind==='map') {
      if(tags[id]!=='map')throw Error('invalid map node')
      const map=object as Map<unknown,unknown>,key=deref(row[2]);if(map.has(key))throw Error('duplicate map entry');map.set(key,deref(row[3]))
    } else if(kind==='set') {
      if(tags[id]!=='set')throw Error('invalid set node')
      const set=object as Set<unknown>,value=deref(row[2]);if(set.has(value))throw Error('duplicate set entry');set.add(value)
    } else if(kind==='meta')metadata.push([object,deref(row[2])])
    else throw Error('unknown graph edge')
  }
  for(let i=0;i<objects.length;i++) {
    const [extensible,lengthWritable]=seals[i]!
    if(tags[i]==='array')Object.defineProperty(objects[i],'length',{writable:lengthWritable})
    if(!extensible)Object.preventExtensions(objects[i])
  }
  for(const [object,value]of metadata)onMetadata!(object,value)
  return deref(root)
}
export function readFamilyCapsule(directory:string,expectedSha256:string,limits:ReadLimits,onMetadata?:(object:object,value:unknown)=>void):{manifest:CaptureManifest,data:unknown} {
  const bytes=boundedFile(join(directory,'CAPTURE.json'),1024*1024)
  if(!/^[0-9a-f]{64}$/.test(expectedSha256)||hash(bytes)!==expectedSha256)throw Error('capture manifest binding mismatch')
  const manifest=JSON.parse(bytes.toString()) as CaptureManifest
  if(manifest.schema!=='bapa-native-certificate/v1'||manifest.complete!==true||!['counted-family','plain','inferred','witness'].includes(manifest.route))throw Error('incomplete final-family capture')
  const data=readCertificateGraph(join(directory,'graph'),manifest.graphManifestSha256,limits,onMetadata) as NativeBundle
  if(!data||typeof data!=='object'||data.route!==manifest.route||JSON.stringify(data.identity)!==JSON.stringify(manifest.identity)||data.terms?.terms.length!==manifest.terms||data.verdict?.proven!==true||data.verdict.checked!==true)throw Error('capture envelope mismatch')
  if(JSON.stringify(data.projection)!==JSON.stringify(projectionOf(data))||JSON.stringify(data.projection)!==JSON.stringify(manifest.projection))throw Error('projection qualification mismatch')
  if(data.route==='counted-family') {
    if(data.schema!=='bapa-family/v1'||data.final.checked!==true||data.final.laws.length!==manifest.familyLaws||JSON.stringify(Object.keys(data.final.proof.certs))!==JSON.stringify(manifest.certificateKeys)||JSON.stringify(retainedLawCoverage(data.original.laws,data.final.laws))!==JSON.stringify(manifest.publicLawIndices)||JSON.stringify(data.publicLawIndices)!==JSON.stringify(manifest.publicLawIndices))throw Error('family manifest mismatch')
  } else if(data.schema!=='bapa-proof/v1'||inspectProvenance(data.proof).route!==data.route)throw Error('producer manifest mismatch')
  return {manifest,data}
}
