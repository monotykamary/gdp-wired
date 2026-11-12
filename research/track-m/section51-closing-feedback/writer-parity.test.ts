import {expect,test} from 'bun:test'
import {mkdtempSync,rmSync,readFileSync,readdirSync,openSync,readSync,closeSync,statSync,mkdirSync,cpSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join,dirname} from 'node:path'
import {tmpdir} from 'node:os'
import {fileURLToPath} from 'node:url'
import {spawnSync} from 'node:child_process'
import {readGraphCapsule} from './graph-reader.test-support.ts'
import {capsulePrototypes} from './capture.ts'
import {isCheckedReducedScope} from '../../../core/count-proof-scope.ts'
function compareBankStreams(a:string,b:string){
 const left=openSync(a,'r'),right=openSync(b,'r'),x=Buffer.alloc(128*1024),y=Buffer.alloc(128*1024),hash=createHash('sha256');let bytes=0
 try{for(;;){const n=readSync(left,x,0,x.length,null),m=readSync(right,y,0,y.length,null);expect(n).toBe(m);if(!n)break;expect(x.subarray(0,n).equals(y.subarray(0,m))).toBe(true);hash.update(x.subarray(0,n));bytes+=n}}
 finally{closeSync(left);closeSync(right)}
 return {bytes,sha256:hash.digest('hex')}
}
const here=dirname(fileURLToPath(import.meta.url)),flags=JSON.parse(readFileSync(join(here,'writer-flags.json'),'utf8'))
test('production native closing: writer off/on/failure has identical verdict, exact units and order',()=>{
 const root=mkdtempSync(join(tmpdir(),'closing-writer-parity-'))
 try{
  const env={...process.env};for(const key of Object.keys(env))if(key.startsWith('GDP_'))delete env[key];Object.assign(env,flags)
  const rows=new Map<string,any>()
  for(const mode of ['off','on','failed-write']){
   const out=join(root,mode),run=spawnSync(process.execPath,[join(here,'writer-control.ts'),mode,out],{env,timeout:60000,encoding:'utf8',maxBuffer:8*1024*1024})
   expect({status:run.status,signal:run.signal,error:run.error?.message,stderr:run.stderr}).toEqual({status:0,signal:null,error:undefined,stderr:''})
   const row=JSON.parse(readFileSync(join(out,'control.json'),'utf8'));rows.set(mode,row)
   expect(row.error).toBeUndefined();expect(row.outcome.checked).toBe(true)
   expect(row.meterChanged).toBe(false);expect(row.termsChanged).toBe(false);expect(row.fixtureStillChecked).toBe(true)
   expect(row.bankStream.records).toBeGreaterThan(0);expect(row.expectedNative.context.length).toBeGreaterThan(0)
  }
  const pick=(row:any)=>({outcome:row.outcome,final:row.final,privateFinal:row.privateFinal,settled:row.settled,privateSettled:row.privateSettled,events:row.events,replayEvents:row.replayEvents,bankStream:row.bankStream,expectedNative:row.expectedNative,fixtureStillChecked:row.fixtureStillChecked})
  expect(pick(rows.get('on'))).toEqual(pick(rows.get('off')))
  expect(pick(rows.get('failed-write'))).toEqual(pick(rows.get('off')))
  for(const mode of ['on','failed-write']){
   const compared=compareBankStreams(join(root,'off','bank-events.jsonl'),join(root,mode,'bank-events.jsonl'))
   expect(compared).toEqual({bytes:rows.get(mode).bankStream.bytes,sha256:rows.get(mode).bankStream.sha256})
   expect(statSync(join(root,mode,'bank-events.jsonl')).size).toBe(compared.bytes)
  }
  expect(rows.get('on').captures).toBeGreaterThan(0)
  expect(rows.get('on').writer).toMatchObject({attempted:rows.get('on').captures,completed:rows.get('on').captures,failures:0,writerOnly:true})
  expect(rows.get('failed-write').writer.completed).toBe(0);expect(rows.get('failed-write').writer.failures).toBeGreaterThan(0)
  const captures=readdirSync(join(root,'on')).filter(name=>name.startsWith('closing-entry-'))
  expect(captures).toHaveLength(rows.get('on').captures)
  for(const name of captures){
   const dir=join(root,'on',name),complete=JSON.parse(readFileSync(join(dir,'CAPTURE.json'),'utf8')),metadata=new WeakMap<object,unknown>()
   expect(complete.complete).toBe(true)
   const data:any=readGraphCapsule(join(dir,'graph'),{prototypes:capsulePrototypes,restoreMetadata:(object,value)=>metadata.set(object,value)})
   expect(data.snapshot.reachAbsent).toBe(true);expect(data.snapshot.m).toBeDefined();expect(data.snapshot.set.length).toBeGreaterThan(0)
   expect(data.checkpoint.leases).toEqual([]);expect(data.checkpoint.capacityBoundaries).toEqual([]);expect(data.checkpoint.notifying).toBe(false)
   expect(data.checkpoint.ledger).toEqual(complete.originalLedger)
   expect(data.kernel.identities).toHaveLength(data.kernel.terms.length)
   expect(data.kernel.terms.length).toBeGreaterThan(0)
   const f=data.snapshot.nativeFixture,expected=rows.get('on').expectedNative
   expect(f).toBeDefined();expect(f.expected).toEqual(expected)
   const ordinal=Number(/^⟦([0-9]+)⟧$/.exec(expected.column)![1])
   expect(data.kernel.terms[ordinal]).toBe(f.term);expect(f.termAlias).toBe(f.term)
   expect(data.kernel.identities.some((entry:[string,number])=>entry[1]===ordinal)).toBe(true)
   expect((metadata.get(f.term) as any).termId).toBe(ordinal)
   const mark=(metadata.get(f.markTree) as any)?.conditionalMark
   expect(mark).toBeDefined();expect(mark.goal).toBe(f.markGoal);expect(mark.goal.name).toBe(expected.markGoalName)
   expect(mark.lemmas).toHaveLength(1);expect(mark.lemmas[0]).toBe(f.markLemmas[0]);expect(mark.lemmas[0].tree).toBe(f.markTree)
   expect(f.markTreeAlias).toBe(f.markTree);expect(f.holder.yes).toBe(f.holder.no);expect(f.holder.yes).toBe(f.markTree)
   const contains=(tree:any):boolean=>tree===f.markTree||('split'in tree&&(contains(tree.yes)||contains(tree.no)))
   expect(Object.values(f.scoped.proof.certs).some((cert:any)=>contains(cert.tree))).toBe(true)
   const binding=(metadata.get(f.scoped.checkedReduced) as any)?.scopeBinding
   expect(binding).toBeDefined();expect(binding.context.length).toBeGreaterThan(0)
   expect(binding.token).toBe(f.scoped.checkedReduced);expect(binding.context).toEqual(expected.context)
   expect(binding.problem).toBe(expected.problem);expect(binding.scope).toBe(expected.scope)
   expect(binding.laws.map((law:any)=>law.name)).toEqual(expected.lawNames)
   expect(binding.laws.every((law:any)=>f.family.includes(law))).toBe(true)
   expect(isCheckedReducedScope(f.scoped,f.m,f.family)).toBe(false) // data is never re-minted
   expect(data.runtime.flags).toEqual(flags);expect(data.runtime.lemmaCuts).toBeNull();expect(data.runtime.fullAccounting).toBe(true)
   for(const member of data.snapshot.controller.pass.states){expect(member.recipes).toBeDefined();for(const recipe of member.recipes)expect(typeof recipe.tickets.started).toBe('number')}
  }
 }finally{
  try{if(process.env.SUPERCOMPUTER_OUTPUT_DIR){const target=join(process.env.SUPERCOMPUTER_OUTPUT_DIR,'writer-parity');mkdirSync(target,{recursive:true});cpSync(root,target,{recursive:true})}}
  finally{rmSync(root,{recursive:true,force:true})}
 }
},200000)
