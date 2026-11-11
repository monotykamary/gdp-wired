import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
const [id,file,source]=process.argv.slice(2)
const data=JSON.parse(gunzipSync(readFileSync(file!)).toString())
assert.equal(data.id,id);assert.equal(data.source,source);assert.equal(data.allowance,15000000);assert.equal(data.variant,'original');assert.equal(data.knobs.GDP_WORK_FULL,'1')
assert.equal(data.status,'COUNTED-PORT-PENDING-D')
assert.equal(data.knobs.GDP_WORK_STEPS,'0');assert(['proven','unknown','refuted'].includes(data.result.verdict));if(data.result.verdict==='proven')assert(data.result.proven&&data.result.checked)
const root=data.phases.filter((p:any)=>p.parentId===null);assert.equal(root.length,1)
for(const key of Object.keys(data.raw))assert.equal(root[0].raw[key],data.raw[key])
console.log('PORT_CENSUS '+JSON.stringify({id,source,verdict:data.result.verdict,why:data.result.why,units:data.searchUnits,raw:data.raw,receiptSha256:createHash('sha256').update(readFileSync(file!)).digest('hex')}))
