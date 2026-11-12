import {writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
export const hash=(value:string|Uint8Array)=>createHash('sha256').update(value).digest('hex')
// Bounded encoded bytes, NOT a bound on native/JS heap or serializer peak.
// Plain data only. Scalar tags are unambiguous because input $mldr keys refuse.
// Map/Set, callbacks, symbols, accessors, sparse arrays and class instances refuse.
export function encode(value:unknown,maximum:number):Buffer{
 if(!Number.isSafeInteger(maximum)||maximum<=0)throw Error('invalid record limit')
 const chunks:string[]=[],active=new Set<object>();let bytes=0
 const add=(s:string)=>{bytes+=Buffer.byteLength(s);if(bytes>=maximum)throw Error('record byte limit');chunks.push(s)}
 const tag=(kind:string,v?:string)=>{add('{"$mldr":');add(JSON.stringify(kind));if(v!==undefined){add(',"value":');add(JSON.stringify(v))}add('}')}
 const visit=(v:unknown,depth:number):void=>{
  if(depth>256)throw Error('record depth limit')
  if(v===null){add('null');return}
  if(v===undefined){tag('undefined');return}
  if(typeof v==='bigint'){tag('bigint',String(v));return}
  if(typeof v==='number'){if(!Number.isFinite(v))throw Error('unsupported nonfinite number');if(Object.is(v,-0)){tag('negative-zero');return}add(JSON.stringify(v));return}
  if(typeof v==='string'){if(Buffer.byteLength(v)>=maximum-bytes)throw Error('record byte limit');add(JSON.stringify(v));return}
  if(typeof v==='boolean'){add(String(v));return}
  if(typeof v!=='object')throw Error('unsupported record scalar: '+typeof v)
  if(v instanceof Map||v instanceof Set)throw Error('unsupported record container: '+(v instanceof Map?'Map':'Set'))
  if(active.has(v))throw Error('cyclic record')
  if(Object.getOwnPropertySymbols(v).length)throw Error('unsupported symbol-keyed record')
  active.add(v)
  if(Array.isArray(v)){
   add('[')
   for(let i=0;i<v.length;i++){const desc=Object.getOwnPropertyDescriptor(v,String(i));if(!desc||!desc.enumerable||!('value' in desc))throw Error('unsupported sparse/accessor array');if(i)add(',');visit(desc.value,depth+1)}
   for(const key of Object.getOwnPropertyNames(v))if(key!=='length'&&(!/^(0|[1-9]\d*)$/.test(key)||Number(key)>=v.length))throw Error('unsupported array property')
   add(']')
  }else{
   const proto=Object.getPrototypeOf(v);if(proto!==Object.prototype&&proto!==null)throw Error('unsupported record prototype')
   if(Object.hasOwn(v,'$mldr'))throw Error('reserved record key: $mldr')
   add('{');let first=true
   for(const key of Object.getOwnPropertyNames(v)){const desc=Object.getOwnPropertyDescriptor(v,key);if(!desc||!desc.enumerable||!('value' in desc))throw Error('unsupported nonenumerable/accessor record');if(!first)add(',');first=false;add(JSON.stringify(key));add(':');visit(desc.value,depth+1)}
   add('}')
  }
  active.delete(v)
 }
 visit(value,0);return Buffer.from(chunks.join('')+'\n')
}
export function save(path:string,value:unknown,maximum=64*1024*1024){writeFileSync(path,encode(value,maximum),{flag:'wx',mode:0o600})}
