// Stronger flat-renaming audit of the already frozen packet. No transport or proof search.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {contextBindings,type AlphaContext} from '../context-bindings.ts'
import {frozenStart,sha} from './start-context.ts'
const path='research/egraph/historical/proofs/canonical-six-law.json',bytes=readFileSync(path)
if(sha(bytes)!=='212fa129969cfbd315fac23d6aeebb3e1df1450b943b7c0309c31b0b9d50a8f9')throw Error('frozen packet pin')
const p=JSON.parse(bytes.toString()) as {sourceArtifacts:Record<string,string>,bindings:({id:string}&ReturnType<typeof contextBindings>)[]},canonical=frozenStart('safety').input
const manifest=JSON.parse(readFileSync('research/egraph/historical/inputs/m2/positives/manifest.json','utf8')) as {artifacts:{id:string,file:string}[]}
const inputs=manifest.artifacts.map(a=>{const file='research/egraph/historical/inputs/m2/positives/'+a.file,b=readFileSync(file);if(sha(b)!==p.sourceArtifacts[file])throw Error('source pin');return {id:a.id,input:JSON.parse(gunzipSync(b).toString()) as AlphaContext}})
inputs.push({id:'safety',input:canonical},{id:'P3',input:frozenStart('p3').input})
for(const {id,input}of inputs){const got=contextBindings(input,canonical),old=p.bindings.find(b=>b.id===id);if(!old||JSON.stringify({id,...got})!==JSON.stringify(old))throw Error('binding map changed: '+id)}
if(sha(readFileSync(path))!==sha(bytes))throw Error('packet changed')
console.log('BINDINGS_AUDIT',JSON.stringify({contexts:inputs.length,sourceAndTargetFreeCaptureRejected:true,mapsUnchanged:true,proofSha256:sha(bytes),proofSearchQueries:0}))
