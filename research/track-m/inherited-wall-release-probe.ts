// Nonmeasurement probe: run on the actual worker under the sealed canonical flags.
import {strict as assert} from 'node:assert'
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {clock, counted, fullRate, pastWall, withWall, wallAt} from '../../kernel/prove.ts'
import {checkWall} from '../../core/wall.ts'
import {completeWorkProfile} from '../../core/work-profile.ts'

assert.equal(completeWorkProfile.enabled, true)
let active=false, expired=false, restored=false
const descriptor=Object.getOwnPropertyDescriptor(performance,'now')
Object.defineProperty(performance,'now',{configurable:true,value:()=>{throw Error('canonical wall read')}})
try {
  counted(fullRate,()=>withWall(clock()+1000000,()=>{
    active=!pastWall();checkWall('canonical active');assert(active)
    assert(wallAt()<=clock()+1000000)
    withWall(clock()-1,()=>{expired=pastWall();assert(expired)})
    restored=!pastWall();assert(restored)
  }),true)
} finally {
  if(descriptor)Object.defineProperty(performance,'now',descriptor);else Reflect.deleteProperty(performance,'now')
}
const result={schema:'inherited-wall-release-probe/v1',profile:'canonical-full',active,expired,restored,proofCalls:0,measurement:false}
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR
if(!out)throw Error('native output directory required')
writeFileSync(join(out,'inherited-wall-probe.json'),JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify(result))
