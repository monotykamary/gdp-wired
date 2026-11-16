// Data-only native-fixture extraction. NEVER use capsule.original for special transports.
import {mkdirSync,writeFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {readFamilyCapsule} from '../../lean-kernel/lift/proof-codec.ts'
import {readLiftSource,sourceStructure} from '../../lean-kernel/lift/source.ts'
import {defaultReadLimits} from '../../lean-kernel/lift/index.ts'
import {assert,hash,hashFile,json,type Input} from './lift-regression.ts'
const id=process.argv[2],output=process.env.SUPERCOMPUTER_OUTPUT_DIR
assert(output&&process.argv.length===3,'usage (remote only): lift-regression-prepare.ts ID')
const matches=json<Input[]>('research/bapa/lift-regression-inputs.json').filter(e=>e.id===id)
assert(matches.length===1,'fixture must occur once');const e=matches[0]!
assert(e.sourceScope==='frozen-capsule-original','special fixtures must come from accepted source, not capsule.original')
const cap=resolve(e.capture.path),out=resolve(output)
mkdirSync(out,{recursive:true})
assert(hashFile(join(cap,'CAPTURE.json'))===e.capture.sha256,'CAPTURE differs')
const {data}=readFamilyCapsule(cap,e.capture.sha256,defaultReadLimits,()=>{})
const original=(data as any).original
assert(original?.machine&&Array.isArray(original.laws)&&original.laws.length,'missing encoded source')
const path=join(out,e.id+'.json')
const text=JSON.stringify({schema:'gdp-lift-source/v1',id:e.id,machine:original.machine,laws:original.laws},null,2)+'\n'
writeFileSync(path,text,{flag:'wx'})
const fixture=readLiftSource(path)
assert(sourceStructure({machine:fixture.source.machine,laws:fixture.source.laws})===sourceStructure(original),'JSON extraction lost source metadata')
assert(hashFile(join(cap,'CAPTURE.json'))===e.capture.sha256,'CAPTURE changed during extraction')
const provenance={schema:'gdp-lift-fixture/v1',id:e.id,scope:e.sourceScope,captureSha256:e.capture.sha256,sourceSha256:hash(text),encodedSourceSha256:hash(sourceStructure(original)),allSizesProven:false,independentTlaVerification:false,noSearch:true,noLean:true}
writeFileSync(join(out,e.id+'.provenance.json'),JSON.stringify(provenance,null,2)+'\n',{flag:'wx'})
console.log(JSON.stringify(provenance))
