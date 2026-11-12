// Test-only verifier. Not imported by or shipped in the write-only harness.
import {openSync,closeSync,readSync,readFileSync,statSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {StringDecoder} from 'node:string_decoder'
import type {GraphOptions,Manifest} from './graph-writer.ts'
const SHARD=8*1024*1024,LINE=1024*1024,TEXT=16*1024
const builtin:Record<string,object>={object:Object.prototype,null:null as unknown as object,array:Array.prototype,map:Map.prototype,set:Set.prototype,error:Error.prototype,typeError:TypeError.prototype,rangeError:RangeError.prototype,referenceError:ReferenceError.prototype,syntaxError:SyntaxError.prototype,uriError:URIError.prototype,evalError:EvalError.prototype,aggregateError:AggregateError.prototype}
type Ref=unknown[]
const natural=(v:unknown):number=>{if(typeof v!=='number'||!Number.isSafeInteger(v)||v<0)throw Error('invalid graph integer');return v}
const bit=(v:unknown):boolean=>{if(typeof v!=='boolean')throw Error('invalid graph bit');return v}
function* records(directory:string,manifest:Manifest):Generator<unknown[]>{
 for(let i=0;i<manifest.shards.length;i++){
  const shard=manifest.shards[i]!,name=`shard-${String(i).padStart(6,'0')}.jsonl`
  if(shard.name!==name||!Number.isSafeInteger(shard.bytes)||shard.bytes<1||shard.bytes>SHARD||!/^[0-9a-f]{64}$/.test(shard.sha256))throw Error('invalid shard descriptor')
  const path=join(directory,name);if(statSync(path).size!==shard.bytes)throw Error('graph shard size mismatch')
  const fd=openSync(path,'r'),buffer=Buffer.alloc(128*1024),decoder=new StringDecoder('utf8'),hash=createHash('sha256')
  let text='',bytes=0
  const line=(s:string):unknown[]=>{const row:unknown=JSON.parse(s);if(!Array.isArray(row))throw Error('invalid graph record');return row}
  try{
   for(;;){const count=readSync(fd,buffer,0,buffer.length,null);if(!count)break;bytes+=count;hash.update(buffer.subarray(0,count));text+=decoder.write(buffer.subarray(0,count))
    let end:number;while((end=text.indexOf('\n'))>=0){if(end>LINE)throw Error('graph line exceeds bound');yield line(text.slice(0,end));text=text.slice(end+1)}
    if(Buffer.byteLength(text)>LINE)throw Error('graph line exceeds bound')
   }
   text+=decoder.end();if(text.length||bytes!==shard.bytes||hash.digest('hex')!==shard.sha256)throw Error('graph shard integrity mismatch')
  }finally{closeSync(fd)}
 }
}
export function readGraphCapsule(directory:string,options:GraphOptions={}):unknown{
 const path=join(directory,'manifest.json');if(statSync(path).size>8*1024*1024)throw Error('graph manifest exceeds bound')
 const manifest=JSON.parse(readFileSync(path,'utf8')) as Manifest
 if(manifest.schema!=='closing-graph/v1'||manifest.complete!==true||!Array.isArray(manifest.shards)||!manifest.shards.length)throw Error('incomplete graph capsule')
 natural(manifest.nodes);natural(manifest.strings)
 const prototypes={...builtin,...options.prototypes},objects:object[]=[],strings:string[]=[],chunks=new Map<number,string[]>(),tags:string[]=[]
 let root:Ref|undefined
 for(const row of records(directory,manifest)){
  const [kind]=row
  if(kind==='node'){
   const id=natural(row[1]),tag=row[2];if(id!==objects.length||typeof tag!=='string'||!Object.hasOwn(prototypes,tag))throw Error('invalid graph node')
   if(tag==='array'){const n=natural(row[3]);if(n>0xffffffff)throw Error('invalid array length');objects.push(new Array(n))}
   else objects.push(tag==='map'?new Map():tag==='set'?new Set():Object.create(prototypes[tag]!))
   tags.push(tag)
  }else if(kind==='root'){if(root!==undefined||!Array.isArray(row[1]))throw Error('invalid graph root');root=row[1]}
  else if(kind==='string'){const id=natural(row[1]);if(id!==strings.length||chunks.size)throw Error('invalid graph string');strings.push('');chunks.set(id,[])}
  else if(kind==='text'){const id=natural(row[1]),data=row[2];if(typeof data!=='string'||data.length>TEXT||!chunks.has(id))throw Error('invalid graph text');chunks.get(id)!.push(data)}
  else if(kind==='string-end'){const id=natural(row[1]),data=chunks.get(id);if(!data)throw Error('invalid graph string end');strings[id]=data.join('');chunks.delete(id)}
  else if(!['prop','map','set','meta','seal'].includes(String(kind)))throw Error('unknown graph record')
 }
 if(!root||chunks.size||objects.length!==manifest.nodes||strings.length!==manifest.strings)throw Error('incomplete graph records')
 const deref=(wire:unknown):unknown=>{
  if(!Array.isArray(wire))throw Error('invalid graph reference')
  const [kind,value]=wire
  if(kind==='u'&&wire.length===1)return undefined
  if(kind==='v'&&wire.length===2&&(value===null||typeof value==='boolean'||typeof value==='string'&&value.length<=TEXT))return value
  if(kind==='n'&&typeof value==='string'&&/^[0-9a-f]{16}$/.test(value))return Buffer.from(value,'hex').readDoubleBE()
  if(kind==='b'&&typeof value==='string'&&/^-?(0|[1-9][0-9]*)$/.test(value))return BigInt(value)
  const index=natural(value)
  if(kind==='r'&&index<objects.length)return objects[index]
  if(kind==='s'&&index<strings.length)return strings[index]
  throw Error('unknown graph reference')
 }
 const seals=new Map<number,[boolean,boolean]>(),metadata:[object,unknown][]=[]
 for(const row of records(directory,manifest)){
  const kind=row[0];if(['node','root','string','text','string-end'].includes(String(kind)))continue
  const id=natural(row[1]),object=objects[id];if(!object)throw Error('graph edge has no node')
  if(kind==='prop'){
   const key=deref(row[2]);if(typeof key!=='string'||Object.hasOwn(object,key))throw Error('invalid or duplicate graph property')
   Object.defineProperty(object,key,{value:deref(row[3]),writable:bit(row[4]),enumerable:bit(row[5]),configurable:bit(row[6])})
  }else if(kind==='map'){if(tags[id]!=='map')throw Error('invalid map node');(object as Map<unknown,unknown>).set(deref(row[2]),deref(row[3]))}
  else if(kind==='set'){if(tags[id]!=='set')throw Error('invalid set node');(object as Set<unknown>).add(deref(row[2]))}
  else if(kind==='meta')metadata.push([object,deref(row[2])])
  else if(kind==='seal'){if(seals.has(id))throw Error('duplicate graph seal');seals.set(id,[bit(row[2]),bit(row[3])])}
  else throw Error('unknown graph edge')
 }
 if(seals.size!==objects.length)throw Error('unsealed graph node')
 for(let i=0;i<objects.length;i++){
  const object=objects[i]!,[extensible,lengthWritable]=seals.get(i)!
  if(tags[i]==='array')Object.defineProperty(object,'length',{writable:lengthWritable})
  if(!extensible)Object.preventExtensions(object)
 }
 if(metadata.length&&!options.restoreMetadata)throw Error('graph metadata handler is required')
 for(const [object,value]of metadata)options.restoreMetadata!(object,value)
 return deref(root)
}
