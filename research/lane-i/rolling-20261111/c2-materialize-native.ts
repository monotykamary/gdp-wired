// Byte materialization only, not a proof or a new native replay.
import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {gzipSync,gunzipSync} from 'node:zlib'
const hash=(text:string)=>createHash('sha256').update(text).digest('hex')
const pairText=readFileSync('port-input/pair.json','utf8')
assert.equal(hash(pairText),'96d60a55fe7a1330475129cec63426de743d5eaff9e2456b7379f6ecf8f570e6')
const oldText=gunzipSync(readFileSync('port-input/C2-native-proof.json.gz')).toString().trim()
assert.equal(hash(oldText),'71ce7c0325be32108eaaf0433b470a61ebc076b2769c44d8ede69765b34fc815')
const pair=JSON.parse(pairText),old=JSON.parse(oldText)
const text=JSON.stringify({machine:pair.prepared,family:pair.family,proof:old.proof}),sha256=hash(text)
assert.equal(sha256,'0a6085119df0808857d5d95bcfe956c8619bcd4f6a6a9739e9ea4faf4df30c82')
const base64=gzipSync(Buffer.from(text)).toString('base64'),count=Math.ceil(base64.length/4000)
for(let index=0;index<count;index++)console.log('C2_ARTIFACT '+JSON.stringify({label:'closed-family',sha256,index,count,base64:base64.slice(index*4000,(index+1)*4000)}))
console.log('C2_MATERIALIZED_IDENTICAL '+JSON.stringify({sha256,bytes:Buffer.byteLength(text),source:'cd7d6d20cf2b34e41bdcfb05117eca6549c71073',nativeReplayed:false,exactPriorNativeBytes:true,leanClearance:false}))
