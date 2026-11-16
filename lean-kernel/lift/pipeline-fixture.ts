// Deterministic fresh-process fixture driver. This constructs only the trivial
// constant-contradiction certificates in proof-synthetic.ts; never searches.
import {writeFileSync,readFileSync} from 'node:fs'
import {join} from 'node:path'
import {snapshotKernelTermState,snapshotKernelTermMemo} from '../../kernel/kernel.ts'
import {syntheticPlain} from './proof-synthetic.ts'
import {projectionOf,type ProvenanceBundle} from './proof-capture.ts'
import {writeFamilyCapsule} from './proof-codec.ts'
import {emitGenericLift} from './index.ts'
const [action,root,id]=process.argv.slice(2)
if(!root)throw Error('fixture root required')
if(action==='prepare'){
  const p=syntheticPlain()
  const b:ProvenanceBundle={schema:'bapa-proof/v1',route:'plain',identity:{protocol:'not_the_source_id',invocation:'fixture',sourceCommit:'a'.repeat(40),sourceTree:'b'.repeat(40),driverSha256:'c'.repeat(64),inputSha256:'d'.repeat(64),runtimeSha256:'e'.repeat(64),profileSha256:'f'.repeat(64),workBudget:'1',flags:{}},original:{machine:p.machine,laws:p.laws},verdict:{proven:true,checked:true},terms:snapshotKernelTermState(),projection:{kind:'same-machine',publicLawIndices:[0]},proof:{kind:'usual',...p}}
  b.projection=projectionOf(b)
  writeFamilyCapsule(join(root,'capture'),b,o=>{const termId=snapshotKernelTermMemo(o);return termId===undefined?undefined:{termId}})
  writeFileSync(join(root,'source.json'),JSON.stringify({schema:'gdp-lift-source/v1',id:'control',...b.original}))
} else if(action==='emit'){
  const source=JSON.parse(readFileSync(join(root,'source.json'),'utf8'))
  source.id=id??'control';writeFileSync(join(root,'source-'+source.id+'.json'),JSON.stringify(source))
  const result=emitGenericLift(join(root,'capture'),join(root,'source-'+source.id+'.json'),join(root,'out-'+source.id))
  console.log(JSON.stringify(result))
} else throw Error('unknown fixture action')
