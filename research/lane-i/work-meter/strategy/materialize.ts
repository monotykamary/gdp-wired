import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
import {validatePhaseLedger} from '../calibration/contract.ts'
const input=resolve(process.argv[2]!),output=process.argv[3]&&resolve(process.argv[3])
const hash=(value:string|Uint8Array)=>createHash('sha256').update(value).digest('hex')
const rows=(text:string,tag:string)=>text.split('\n').filter(line=>line.startsWith(tag+' ')).map(line=>JSON.parse(line.slice(tag.length+1)))
const summary=readFileSync(join(input,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t'))
const read=(name:string)=>{assert(summary.some(([id,code])=>id===name&&code==='0'),name);return readFileSync(join(input,name+'.log'),'utf8')}
const text=read('strategy-meter-composition-check'),receipts=rows(text,'STRATEGY_METER_VALIDATED');assert.equal(receipts.length,1)
const receipt=receipts[0];assert.equal(receipt.passed,true);assert.equal(receipt.pin,'aeef60912e189573eb24e658af7e915109a971d2')
assert.equal(receipt.ledger,'ed88401af1577ac0fc4e5cbb270ec305274ee3e0')
const chunks=new Map<number,string>()
for(let part=0;part<8;part++){
 const text=read('strategy-source-part-'+part),proofs=rows(text,'STRATEGY_SOURCE_REBUILT');assert.equal(proofs.length,1)
 const proof=proofs[0];assert.equal(proof.passed,false);assert.equal(proof.part,part);assert.equal(proof.parts,8)
 for(const key of ['pin','strategy','ledger','sourceTree','patchSha256','bytes','chunks'])assert.deepEqual(proof[key],receipt[key],key)
 for(const row of rows(text,'STRATEGY_SOURCE_CHUNK')){assert.equal(row.index%8,part);assert(!chunks.has(row.index));chunks.set(row.index,row.data)}
}
assert.equal(chunks.size,receipt.chunks)
const parts=[];for(let i=0;i<receipt.chunks;i++){assert(chunks.has(i));parts.push(chunks.get(i)!)}
const patch=gunzipSync(Buffer.from(parts.join(''),'base64'));assert.equal(patch.length,receipt.bytes);assert.equal(hash(patch),receipt.patchSha256)
const packed=rows(text,'STRATEGY_PHASE_DATA');assert.equal(packed.length,1);assert.equal(packed[0].encoding,'gzip-base64')
const phaseBytes=gunzipSync(Buffer.from(packed[0].data,'base64'));assert.equal(phaseBytes.length,packed[0].bytes);assert.equal(hash(phaseBytes),packed[0].sha256)
const phase=JSON.parse(phaseBytes.toString());assert.equal(phase.sourceTree,receipt.sourceTree);assert.equal(phase.patchSha256,receipt.patchSha256)
assert.equal(phase.results.length,2);assert.equal(phase.paths.length,2)
const off=phase.results.find((row:any)=>!row.on),on=phase.results.find((row:any)=>row.on),pathOff=phase.paths.find((row:any)=>!row.on),pathOn=phase.paths.find((row:any)=>row.on)
assert(off&&on&&pathOff&&pathOn);assert.deepEqual(off.raw,on.raw);assert.deepEqual(off.result,on.result);assert(on.result.proven&&on.result.checked)
const strategyAudit=validatePhaseLedger(on.raw,on.events),pathAudit=validatePhaseLedger(pathOn.raw,pathOn.events)
assert.deepEqual(pathOff.raw,pathOn.raw);assert.deepEqual(pathOff.cases,pathOn.cases)
assert(pathOn.raw.epr>0);assert(on.raw.tableCells>0&&on.raw.checkSteps>0&&on.raw.astNodes>0)
for(const name of ['strategy.attempt','strategy.row','strategy.compose','strategy.check','strategy.goal-build'])assert(strategyAudit.phaseNames.includes(name),name)
const result={passed:true,...receipt,phaseSha256:hash(phaseBytes),strategyAudit,pathAudit,scope:'metered strategy and direct ordinary/EPR fixtures; not original MLDR, full F3, calibrated W or admission'}
if(output){mkdirSync(output,{recursive:false});writeFileSync(join(output,'candidate.patch'),patch);writeFileSync(join(output,'phase-data.json'),phaseBytes);writeFileSync(join(output,'receipt.json'),JSON.stringify(result,null,2)+'\n')}
console.log('STRATEGY_SOURCE_MATERIALIZED '+JSON.stringify(result))
