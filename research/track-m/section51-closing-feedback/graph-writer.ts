// Streaming, order/descriptor/alias preserving diagnostic graph codec.
// No code is deserialized. An incomplete directory has no manifest and is invalid.
import {mkdirSync,readdirSync,openSync,closeSync,writeSync,fsyncSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
const SHARD=8*1024*1024,LINE=1024*1024,TEXT=16*1024
const builtin:Record<string,object>={object:Object.prototype,null:null as unknown as object,array:Array.prototype,map:Map.prototype,set:Set.prototype,error:Error.prototype,typeError:TypeError.prototype,rangeError:RangeError.prototype,referenceError:ReferenceError.prototype,syntaxError:SyntaxError.prototype,uriError:URIError.prototype,evalError:EvalError.prototype,aggregateError:AggregateError.prototype}
type Ref=unknown[]
export type Manifest={schema:'closing-graph/v1',complete:true,nodes:number,strings:number,shards:{name:string,bytes:number,sha256:string}[]}
export type GraphOptions={prototypes?:Record<string,object>,metadata?:(object:object)=>unknown,restoreMetadata?:(object:object,value:unknown)=>void}
const natural=(v:unknown):number=>{if(typeof v!=='number'||!Number.isSafeInteger(v)||v<0)throw Error('invalid graph integer');return v}
const bit=(v:unknown):boolean=>{if(typeof v!=='boolean')throw Error('invalid graph bit');return v}
function writeAll(fd:number,data:Buffer){let offset=0;while(offset<data.length){const n=writeSync(fd,data,offset,data.length-offset);if(n<=0)throw Error('short capsule write');offset+=n}}
export function writeGraphCapsule(directory:string,root:unknown,options:GraphOptions={}):Manifest{
 mkdirSync(directory,{recursive:true});if(readdirSync(directory).length)throw Error('graph output must be a new empty directory')
 const prototypes={...builtin,...options.prototypes},tags=new Map<object,string>(),ids=new WeakMap<object,number>(),pending:(object|undefined)[]=[],shards:Manifest['shards']=[]
 for(const [name,prototype]of Object.entries(prototypes))if(!tags.has(prototype))tags.set(prototype,name)
 let fd:number|undefined,bytes=0,parts:string[]=[],buffered=0,digest=createHash('sha256'),stringCount=0
 const flush=()=>{if(!buffered)return;const data=Buffer.from(parts.join(''));writeAll(fd!,data);digest.update(data);parts=[];buffered=0}
 const close=()=>{if(fd===undefined)return;flush();fsyncSync(fd);closeSync(fd);fd=undefined;shards.push({name:`shard-${String(shards.length).padStart(6,'0')}.jsonl`,bytes,sha256:digest.digest('hex')})}
 const emit=(record:unknown[])=>{
  const line=JSON.stringify(record)+'\n',size=Buffer.byteLength(line)
  if(size>LINE)throw Error('graph record exceeds line bound')
  if(fd!==undefined&&bytes+size>SHARD)close()
  if(fd===undefined){fd=openSync(join(directory,`shard-${String(shards.length).padStart(6,'0')}.jsonl`),'wx');bytes=0;digest=createHash('sha256')}
  parts.push(line);buffered+=size;bytes+=size;if(buffered>=256*1024)flush()
 }
 const ref=(value:unknown):Ref=>{
  if(value===undefined)return ['u']
  if(value===null||typeof value==='boolean')return ['v',value]
  if(typeof value==='number'){const bits=Buffer.allocUnsafe(8);bits.writeDoubleBE(value);return ['n',bits.toString('hex')]}
  if(typeof value==='bigint')return ['b',String(value)]
  if(typeof value==='string'){
   if(value.length<=TEXT)return ['v',value]
   const id=stringCount++;emit(['string',id]);for(let i=0;i<value.length;i+=TEXT)emit(['text',id,value.slice(i,i+TEXT)]);emit(['string-end',id]);return ['s',id]
  }
  if(typeof value!=='object')throw Error('functions and symbols are not graph data')
  let id=ids.get(value);if(id===undefined){id=pending.length;ids.set(value,id);pending.push(value)}return ['r',id]
 }
 try{
  emit(['root',ref(root)])
  for(let id=0;id<pending.length;id++){
   const object=pending[id]!,prototype=Object.getPrototypeOf(object)
   const tag=tags.get(prototype)
   if(tag===undefined)throw Error('unsupported graph prototype')
   emit(['node',id,tag,Array.isArray(object)?object.length:null])
   if(tag==='map')for(const [key,value]of object as Map<unknown,unknown>)emit(['map',id,ref(key),ref(value)])
   if(tag==='set')for(const value of object as Set<unknown>)emit(['set',id,ref(value)])
   for(const key of Reflect.ownKeys(object)){
    if(typeof key!=='string')throw Error('symbol graph property')
    const d=Object.getOwnPropertyDescriptor(object,key)!
    if(!('value'in d))throw Error('accessor graph property')
    if(tag==='array'&&key==='length')continue
    emit(['prop',id,ref(key),ref(d.value),!!d.writable,!!d.enumerable,!!d.configurable])
   }
   const metadata=options.metadata?.(object);if(metadata!==undefined)emit(['meta',id,ref(metadata)])
   emit(['seal',id,Object.isExtensible(object),tag==='array'?!!Object.getOwnPropertyDescriptor(object,'length')!.writable:true])
   pending[id]=undefined
  }
  close()
  const manifest:Manifest={schema:'closing-graph/v1',complete:true,nodes:pending.length,strings:stringCount,shards}
  const out=openSync(join(directory,'manifest.json'),'wx');try{writeAll(out,Buffer.from(JSON.stringify(manifest)+'\n'));fsyncSync(out)}finally{closeSync(out)}
  return manifest
 }finally{if(fd!==undefined){try{closeSync(fd)}catch{/* retain incomplete files, no manifest */}}}
}
