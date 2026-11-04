// Resolve input alpha/permutation bookkeeping only. No proof search or transport.
import {readFileSync,writeFileSync} from 'node:fs'
import {gunzipSync,gzipSync} from 'node:zlib'
import {contextBindings,type AlphaContext} from '../context-bindings.ts'
import {frozenStart,sha} from './start-context.ts'
const canonical=frozenStart('safety').input,dir='research/egraph/historical/inputs/m2/positives'
const manifest=JSON.parse(readFileSync(dir+'/manifest.json','utf8')) as {artifacts:{id:string,file:string,gzipSha256:string,rawSha256:string,expected:{focus:string}}[]}
const mappings=[]
for(const a of manifest.artifacts){
  const compressed=readFileSync(dir+'/'+a.file),bytes=gunzipSync(compressed)
  if(sha(compressed)!==a.gzipSha256||sha(bytes)!==a.rawSha256)throw Error('positive input drift')
  const input=JSON.parse(bytes.toString()) as AlphaContext&{proof:{certs:Record<string,unknown>}}
  mappings.push({id:a.id,inputSha256:a.rawSha256,focus:a.expected.focus,...contextBindings(input,canonical),certificates:Object.fromEntries(Object.entries(input.proof.certs).map(([name,cert])=>[name,sha(JSON.stringify(cert))]))})
}
const p3=frozenStart('p3').input
mappings.push({id:'P3',focus:p3.law.name,inputSha256:frozenStart('p3').inputSha256,...contextBindings(p3,canonical),certificates:{step:sha(readFileSync('research/egraph/historical/proofs/p3-bridge-step.json')),start:sha(readFileSync('new-p3-start.json'))}})
const packet=JSON.stringify({canonicalMachineSha256:sha(JSON.stringify(canonical.m)),canonicalLawsSha256:sha(JSON.stringify(canonical.laws)),canonicalOrder:canonical.laws.map(l=>l.name),mappings,safety:{step:sha(readFileSync('research/egraph/historical/proofs/safety-direct-step.json')),start:sha(readFileSync('new-safety-start.json'))},transportPerformed:false,fullConjunctionChecked:false})
writeFileSync('conjunction-bookkeeping.json',packet)
console.log('BOOKKEEPING',JSON.stringify({contexts:mappings.length,alphaMatched:true,transportPerformed:false,fullConjunctionChecked:false,sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}))
