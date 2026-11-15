import {expect,test} from 'bun:test'
import {mkdtempSync,readFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {projectionOf,type ProvenanceBundle} from './proof-capture.ts'
import {writeFamilyCapsule,readFamilyCapsule} from './proof-codec.ts'
const limits={maxBytes:1024*1024,maxNodes:1000,maxStrings:100,maxArrayLength:1000,maxShards:8}
function fixture():ProvenanceBundle {
 const machine={} as ProvenanceBundle['original']['machine'],laws=[{name:'law',holds:{op:'=',a:{op:'const',value:0},b:{op:'const',value:0}}}] as ProvenanceBundle['original']['laws']
 return {schema:'bapa-proof/v1',route:'plain',identity:{protocol:'fixture',invocation:'one',sourceCommit:'a'.repeat(40),sourceTree:'b'.repeat(40),driverSha256:'c'.repeat(64),inputSha256:'d'.repeat(64),runtimeSha256:'e'.repeat(64),profileSha256:'f'.repeat(64),workBudget:'1',flags:{}},original:{machine,laws},verdict:{proven:true,checked:true},terms:{terms:[],identities:[]},proof:{kind:'usual',machine,laws,proof:{instances:{},trees:{}}},projection:{kind:'same-machine',publicLawIndices:[0]}}
}
test('capsule writer refuses a forged same-machine qualification',()=>{
 const root=mkdtempSync(join(tmpdir(),'bapa-projection-'))
 try{const b=fixture();b.original={...b.original,machine:{name:'different'} as typeof b.original.machine};expect(projectionOf(b).kind).toBe('unqualified');expect(()=>writeFamilyCapsule(join(root,'bad'),b)).toThrow('qualification')}finally{rmSync(root,{recursive:true,force:true})}
})
test('fresh-process-compatible reader preserves explicit raw-only qualification',()=>{
 const root=mkdtempSync(join(tmpdir(),'bapa-projection-'))
 try{
  const b=fixture();b.original={...b.original,laws:[]};b.proof={...b.proof,kind:'derived',parents:[b.proof],context:{kind:'witness'}} as typeof b.proof;b.route='witness';b.projection=projectionOf(b)
  const dir=join(root,'raw'),written=writeFamilyCapsule(dir,b),read=readFamilyCapsule(dir,written.manifestSha256,limits)
  expect(read.manifest.projection.kind).toBe('unqualified')
  const manifestSha=createHash('sha256').update(readFileSync(join(dir,'CAPTURE.json'))).digest('hex');expect(manifestSha).toBe(written.manifestSha256)
 }finally{rmSync(root,{recursive:true,force:true})}
})
