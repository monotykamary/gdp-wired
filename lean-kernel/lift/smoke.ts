// A fresh-process, data-only real-capsule emission control; never searches or runs Lean.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {emitGenericLift,defaultReadLimits,type GenericLiftRoute} from './index.ts'
import {readFamilyCapsule} from './proof-codec.ts'
import type {NativeBundle} from './proof-capture.ts'
import {sha256} from './source.ts'
const [capture,kind,output]=process.argv.slice(2)
if(!capture||!['alpha','counted','witness'].includes(kind!)||!output)throw Error('usage: smoke.ts CAPTURE alpha|counted|witness OUTPUT')
const digest=sha256(readFileSync(join(capture,'CAPTURE.json')))
const {data}=readFamilyCapsule(capture,digest,defaultReadLimits,()=>{})
const bundle=data as NativeBundle
mkdirSync(output,{recursive:true})
const source=join(output,'source.json')
writeFileSync(source,JSON.stringify({schema:'gdp-lift-source/v1',id:'renamed_fixture_'+kind,machine:bundle.original.machine,laws:bundle.original.laws}))
const result=emitGenericLift(capture,source,join(output,'project'),{expectedManifestSha256:digest})
if(result.sourceProjection.kind!==kind as GenericLiftRoute||result.status!=='EMITTED_NOT_CHECKED'||result.leanExecuted!==false)throw Error('unexpected emission result')
if(result.requiredTheorems.some(t=>!result.files['BapaProof.lean']||!readFileSync(join(output,'project/BapaProof.lean'),'utf8').includes('#print axioms '+t)))throw Error('root theorem request missing')
console.log(JSON.stringify({status:result.status,kind,files:Object.keys(result.files).length,publicLaws:result.sourceProjection.sourceTheorems.length,requiredTheorems:result.requiredTheorems.length,capsuleSha256:digest}))
