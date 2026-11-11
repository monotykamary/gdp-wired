import {strict as assert} from 'node:assert'
import {readFileSync,readdirSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const [input,baseline]=process.argv.slice(2)
if(!input||!baseline)throw Error('analyze-probes INPUT BASELINE')
const receipt=(text:string)=>JSON.parse(gunzipSync(Buffer.from(JSON.parse(text.split('\n').find(s=>s.startsWith('CANDIDATE_RECEIPT '))!.slice(18)).gzipBase64,'base64')).toString())
const rows=[]
for(const file of readdirSync(input).filter(f=>f.endsWith('.log'))){
 const text=readFileSync(join(input,file),'utf8'),r=receipt(text),old=receipt(readFileSync(join(baseline,`normal-${r.id}.log`),'utf8'))
 assert.deepEqual(r.raw,old.raw);assert.deepEqual(r.result,old.result)
 const p=JSON.parse(text.split('\n').find(s=>s.startsWith('HARD_CAP_PROBE '))!.slice(15))
 assert(p.polls>0);assert(p.firstAbove)
 rows.push({id:r.id,searchUnits:r.searchUnits,result:r.result,probe:p})
}
assert.equal(rows.length,13)
console.log('HARD_CAP_BASELINE '+JSON.stringify(rows))
