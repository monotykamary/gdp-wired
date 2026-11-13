import {expect,test} from 'bun:test'
import {mkdtempSync,rmSync,readFileSync,writeFileSync,unlinkSync,existsSync,openSync,closeSync,fsyncSync} from 'node:fs'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
import {writeGraphCapsule} from './graph-writer.ts'
import {readGraphCapsule} from './graph-reader.test-support.ts'
import {installClosingCapture} from './capture.ts'
import {countRecipeClosingCapture,type CountedRecipeClosingSnapshot} from '../../../core/counts.ts'
import {completeWorkProfile} from '../../../core/work-profile.ts'
import {atPoint} from '../../../kernel/prove.ts'
const fullTest=completeWorkProfile.enabled?test:test.skip
fullTest('late parent fsync failure retracts completion and records an incomplete capture',()=>{
 const out=mkdtempSync(join(tmpdir(),'closing-late-sync-')),synced:string[]=[];let markerBeforeFault=false
 const finish=installClosingCapture(out,{fixture:'late-durability'},()=>{},{syncDirectory:path=>{
  synced.push(path)
  if(path===out){markerBeforeFault=existsSync(join(out,'closing-entry-0001','CAPTURE.json'));throw Error('late parent fsync fault')}
  const fd=openSync(path,'r');try{fsyncSync(fd)}finally{closeSync(fd)}
 }})
 try{
  // Only reachAbsent is consumed before graph serialization; no replay/native claim.
  expect(atPoint.on).toBe(false)
  expect(()=>countRecipeClosingCapture.on!({reachAbsent:true} as CountedRecipeClosingSnapshot)).not.toThrow()
  expect(synced).toHaveLength(3);expect(markerBeforeFault).toBe(true)
  expect(existsSync(join(out,'closing-entry-0001','CAPTURE.json'))).toBe(false)
  expect(JSON.parse(readFileSync(join(out,'closing-capture-errors.jsonl'),'utf8'))).toMatchObject({complete:false,error:'Error: late parent fsync fault'})
  expect(finish()).toEqual({attempted:1,completed:0,failures:1,writerOnly:true})
 }finally{if(countRecipeClosingCapture.on)finish();rmSync(out,{recursive:true,force:true})}
})
fullTest('active atPoint state still refuses capture without changing that state',()=>{
 const out=mkdtempSync(join(tmpdir(),'closing-active-point-')),previous=atPoint.on
 const finish=installClosingCapture(out,{fixture:'active-point'},()=>{})
 try{
  atPoint.on=true
  countRecipeClosingCapture.on!({reachAbsent:true} as CountedRecipeClosingSnapshot)
  expect(atPoint.on).toBe(true)
  expect(finish()).toEqual({attempted:1,completed:0,failures:1,writerOnly:true})
  expect(JSON.parse(readFileSync(join(out,'closing-capture-errors.jsonl'),'utf8')).error).toBe('Error: unsupported closing runtime')
  expect(existsSync(join(out,'closing-entry-0001','CAPTURE.json'))).toBe(false)
 }finally{atPoint.on=previous;if(countRecipeClosingCapture.on)finish();rmSync(out,{recursive:true,force:true})}
})
const temporary=(run:(directory:string)=>void)=>{const directory=mkdtempSync(join(tmpdir(),'closing-graph-test-'));try{run(directory)}finally{rmSync(directory,{recursive:true,force:true})}}
test('graph capsule preserves aliases, cycles, key/Map order, holes and exact scalars',()=>temporary(dir=>{
 const nullObject=Object.create(null);nullObject.x=undefined
 const shared={nullObject,minusZero:-0,nan:NaN,inf:Infinity,big:123456789123456789n}
 const array=Array(4);array[2]=shared
 const root:any={shared,again:shared,array,map:new Map<unknown,unknown>([[shared,array],['second',nullObject]]),set:new Set([shared,array]),long:'x'.repeat(50000)+'\ud800'}
 root.self=root;Object.defineProperty(root,'hidden',{value:'retained',writable:false,enumerable:false,configurable:false})
 Object.freeze(shared)
 writeGraphCapsule(dir,root)
 const got:any=readGraphCapsule(dir)
 expect(got.self).toBe(got);expect(got.again).toBe(got.shared);expect(got.array[2]).toBe(got.shared)
 expect(Object.getPrototypeOf(got.shared.nullObject)).toBeNull();expect(Object.hasOwn(got.shared.nullObject,'x')).toBe(true)
 expect(Object.hasOwn(got.array,0)).toBe(false);expect(got.array.length).toBe(4)
 expect([...got.map.keys()]).toEqual([got.shared,'second']);expect([...got.set]).toEqual([got.shared,got.array])
 expect(Object.is(got.shared.minusZero,-0)).toBe(true);expect(Number.isNaN(got.shared.nan)).toBe(true)
 expect(got.shared.inf).toBe(Infinity);expect(got.shared.big).toBe(123456789123456789n)
 expect(got.long).toBe(root.long);expect(Object.isFrozen(got.shared)).toBe(true)
 expect(Object.getOwnPropertyDescriptor(got,'hidden')).toEqual(Object.getOwnPropertyDescriptor(root,'hidden'))
 expect(Object.keys(got)).toEqual(Object.keys(root))
}))
test('graph metadata restores subtree aliases without inventing receipt objects',()=>temporary(dir=>{
 const subtree={leaf:[]},goal={hyps:[]},mark={goal,lemmas:[]},source=new WeakMap<object,unknown>([[subtree,mark]])
 const restored=new WeakMap<object,unknown>()
 writeGraphCapsule(dir,{tree:{yes:subtree,no:subtree},goal},{metadata:object=>source.get(object)})
 const got:any=readGraphCapsule(dir,{restoreMetadata:(object,value)=>restored.set(object,value)})
 expect(got.tree.yes).toBe(got.tree.no);expect((restored.get(got.tree.yes) as any).goal).toBe(got.goal)
}))
test('graph shards are bounded independently of a large scalar',()=>temporary(dir=>{
 const text='x'.repeat(9*1024*1024),manifest=writeGraphCapsule(dir,{text})
 expect(manifest.shards.length).toBeGreaterThan(1)
 expect(manifest.shards.every(shard=>shard.bytes<=8*1024*1024)).toBe(true)
 expect((readGraphCapsule(dir) as {text:string}).text).toBe(text)
}))
test('capsule refuses accessors/functions/custom prototypes and has no completion manifest',()=>{
 for(const bad of [{get value(){throw Error('accessor executed')}},{f:()=>0},new Date()])temporary(dir=>{
  expect(()=>writeGraphCapsule(dir,bad)).toThrow();expect(()=>readFileSync(join(dir,'manifest.json'))).toThrow()
 })
})
test('capsule rejects changed or missing shard and cannot append to an existing capture',()=>temporary(dir=>{
 const manifest=writeGraphCapsule(dir,{value:'original'}),path=join(dir,manifest.shards[0]!.name)
 expect(()=>writeGraphCapsule(dir,{})).toThrow('empty directory')
 const old=readFileSync(path);writeFileSync(path,Buffer.from(old.toString().replace('original','replaced')))
 expect(()=>readGraphCapsule(dir)).toThrow()
 unlinkSync(path);expect(()=>readGraphCapsule(dir)).toThrow()
}))
