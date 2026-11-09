// Research input provenance only, not a proof or suite-acceptance checker.
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync} from 'node:fs'
import {brotliDecompressSync} from 'node:zlib'
export type Family={machine:unknown,laws:unknown[]}
const sha=(text:string|Buffer)=>createHash('sha256').update(text).digest('hex')
function stable(value:unknown):unknown{
 if(Array.isArray(value))return value.map(stable)
 if(value&&typeof value==='object')return Object.fromEntries(Object.entries(value).sort(([a],[b])=>a.localeCompare(b)).map(([key,item])=>[key,stable(item)]))
 return value
}
export function identity(value:unknown){return sha(JSON.stringify(stable(value)))}
export function capturedFamily(log:string){
 const rows=log.split('\n').filter(line=>line.startsWith('{')).map(line=>JSON.parse(line) as Record<string,unknown>).filter(row=>row.artifact==='mldr-incl-production-capture')
 if(rows.length!==1)throw Error('expected one complete production capture')
 const row=rows[0]!
 if(typeof row.data!=='string'||typeof row.sha256!=='string'||row.omitted!==0)throw Error('invalid capture metadata')
 const bytes=Buffer.from(row.data,'base64');if(sha(bytes)!==row.sha256)throw Error('capture hash mismatch')
 const files=JSON.parse(brotliDecompressSync(bytes).toString()) as Record<string,unknown>,text=files['family-source.json']
 if(typeof text!=='string')throw Error('missing exact family')
 const family=JSON.parse(text) as Family
 if(!family.machine||!Array.isArray(family.laws))throw Error('invalid family')
 return {text,family,archiveSha256:row.sha256}
}
if(import.meta.main){
 const [log,prior,out]=process.argv.slice(2),next=capturedFamily(readFileSync(log!,'utf8')),old=JSON.parse(readFileSync(prior!,'utf8')) as Family
 if(!old.machine||!Array.isArray(old.laws))throw Error('invalid prior family')
 writeFileSync(out!,next.text)
 console.log(JSON.stringify({diagnostic:true,familyComparison:true,archiveSha256:next.archiveSha256,familySha256:sha(next.text),sameMachine:identity(next.family.machine)===identity(old.machine),sameLaws:identity(next.family.laws)===identity(old.laws),laws:next.family.laws.length,priorLaws:old.laws.length}))
}
