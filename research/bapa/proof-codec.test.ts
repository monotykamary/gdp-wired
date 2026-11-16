import {expect,test} from 'bun:test'
import {mkdtempSync,readFileSync,writeFileSync,rmSync,existsSync,mkdirSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {writeGraphCapsule} from './proof-graph.ts'
import {readCertificateGraph,writeFamilyCapsule,type ReadLimits} from './proof-codec.ts'
const digest=(b:Uint8Array)=>createHash('sha256').update(b).digest('hex')
const limits={maxBytes:32*1024*1024,maxNodes:100000,maxStrings:1000,maxArrayLength:100000,maxShards:16}
function roundtrip(value:unknown,check:(actual:any,path:string,sha:string)=>void){const root=mkdtempSync(join(tmpdir(),'bapa-codec-')),dir=join(root,'graph');try{writeGraphCapsule(dir,value);const sha=digest(readFileSync(join(dir,'manifest.json')));check(readCertificateGraph(dir,sha,limits),dir,sha)}finally{rmSync(root,{recursive:true,force:true})}}
test('lossless descriptor, alias, cycle, ordered map/set, holes, IEEE and long-string data',()=>{
 const shared={value:undefined},array:any[]=[];array.length=3;array[1]=shared
 const x:any={shared,alias:shared,array,nan:NaN,negativeZero:-0,inf:Infinity,negInf:-Infinity,big:2n**90n,long:'a😀z'.repeat(10000),map:new Map(),set:new Set()};x.self=x;x.map.set(shared,x);x.set.add(shared);x.set.add(x)
 Object.defineProperty(x,'hidden',{value:shared,writable:false,enumerable:false,configurable:false});Object.preventExtensions(shared)
 roundtrip(x,(out)=>{expect(out.self).toBe(out);expect(out.alias).toBe(out.shared);expect(out.hidden).toBe(out.shared);expect(out.array[1]).toBe(out.shared);expect(0 in out.array).toBe(false);expect(out.array.length).toBe(3);expect(Number.isNaN(out.nan)).toBe(true);expect(Object.is(out.negativeZero,-0)).toBe(true);expect(out.inf).toBe(Infinity);expect(out.negInf).toBe(-Infinity);expect(out.big).toBe(x.big);expect(out.long).toBe(x.long);expect([...out.map.keys()]).toEqual([out.shared]);expect(out.map.get(out.shared)).toBe(out);expect([...out.set]).toEqual([out.shared,out]);expect(Object.isExtensible(out.shared)).toBe(false);expect(Object.getOwnPropertyDescriptor(out,'hidden')!.writable).toBe(false)})
})
test('corrupt shard, wrong manifest binding and size limits refuse before returning data',()=>{
 roundtrip({a:1},(_out,dir,sha)=>{expect(()=>readCertificateGraph(dir,'0'.repeat(64),limits)).toThrow('binding');expect(()=>readCertificateGraph(dir,sha,{...limits,maxBytes:1})).toThrow();const shard=join(dir,'shard-000000.jsonl');const bytes=readFileSync(shard);bytes[0]=bytes[0]===91?123:91;writeFileSync(shard,bytes);expect(()=>readCertificateGraph(dir,sha,limits)).toThrow()})
})
test('every required graph limit must be present before reading a valid capsule',()=>{
 roundtrip({a:1},(_out,dir,sha)=>{
  for(const key of ['maxBytes','maxNodes','maxStrings','maxArrayLength','maxShards'] as const){
   const partial:Partial<ReadLimits>={...limits};delete partial[key]
   expect(()=>readCertificateGraph(dir,sha,partial as ReadLimits)).toThrow('invalid graph limit: '+key)
  }
  expect(()=>readCertificateGraph(dir,sha,{} as ReadLimits)).toThrow('invalid graph limit: maxBytes')
 })
})
test('each graph limit must be a positive safe integer',()=>{
 roundtrip({a:1},(_out,dir,sha)=>{
  for(const key of ['maxBytes','maxNodes','maxStrings','maxArrayLength','maxShards'] as const)
   for(const value of [undefined,null,'16',0,-1,0.5,NaN,Infinity,Number.MAX_SAFE_INTEGER+1])
    expect(()=>readCertificateGraph(dir,sha,{...limits,[key]:value} as unknown as ReadLimits)).toThrow('invalid graph limit: '+key)
 })
})
test('functions and accessors never produce an outer complete marker',()=>{
 for(const bad of [{fn:()=>0},Object.defineProperty({},'x',{get(){throw Error('must not invoke getter')},enumerable:true})]){const root=mkdtempSync(join(tmpdir(),'bapa-incomplete-')),dir=join(root,'capsule');try{expect(()=>writeFamilyCapsule(dir,bad as never)).toThrow();expect(existsSync(join(dir,'CAPTURE.json'))).toBe(false)}finally{rmSync(root,{recursive:true,force:true})}}
})
test('reader rejects non-sequential nodes even when attacker supplies a matching hash',()=>{
 const root=mkdtempSync(join(tmpdir(),'bapa-negative-')),dir=join(root,'graph');try{mkdirSync(dir);const bytes=Buffer.from('["root",["r",0]]\n["node",1,"object",null]\n["seal",1,true,true]\n');writeFileSync(join(dir,'shard-000000.jsonl'),bytes);writeFileSync(join(dir,'manifest.json'),JSON.stringify({schema:'closing-graph/v1',complete:true,nodes:1,strings:0,shards:[{name:'shard-000000.jsonl',bytes:bytes.length,sha256:digest(bytes)}]}));const sha=digest(readFileSync(join(dir,'manifest.json')));expect(()=>readCertificateGraph(dir,sha,limits)).toThrow('node')}finally{rmSync(root,{recursive:true,force:true})}
})
