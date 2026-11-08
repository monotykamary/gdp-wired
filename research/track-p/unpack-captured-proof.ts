// Format conversion only. Authentication is checkMC(raw.hyps, decls, proof).
import {readFileSync,mkdirSync,writeFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
const [proofLog,failureLog,dest,index,variant]=process.argv.slice(2),text=readFileSync(proofLog!,'utf8'),parts=[...text.matchAll(/^CERT_GZIP (\S+)/gm)]
const p=parts[Number(variant??0)]?.[1];if(!p)throw Error('missing certified variant')
const pack=JSON.parse(gunzipSync(Buffer.from(p,'base64')).toString()),source=readFileSync(failureLog!,'utf8').match(/^FAILURES_GZIP (\S+)/m)?.[1]
if(!source)throw Error('missing source packet')
const rows=JSON.parse(gunzipSync(Buffer.from(source,'base64')).toString()),snap=rows.find((r:any)=>r.index===Number(index))?.first
if(JSON.stringify(snap?.raw)!==JSON.stringify(pack.goal.raw))throw Error('source mismatch')
mkdirSync(dest!,{recursive:true})
writeFileSync(dest+'/goal.json',JSON.stringify({scope:'CAPTURED_STEP_REPLAY',...pack.goal,gg:{name:snap.raw.name,hyps:snap.hyps}})+'\n')
writeFileSync(dest+'/proof.json',JSON.stringify(pack.proof)+'\n')
writeFileSync(dest+'/source.json',JSON.stringify({proofLog,failureLog,index:Number(index),variant:Number(variant),instances:snap.instances})+'\n')
console.log(JSON.stringify({dest,index:Number(index),variant:Number(variant),rawHyps:snap.raw.hyps.length,encodedHyps:snap.hyps.length}))
