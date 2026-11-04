// Materialize bounded, hash-checked artifacts without overwriting divergent files.
import {readFileSync, writeFileSync, mkdirSync, existsSync} from 'node:fs'
import {resolve, dirname, sep} from 'node:path'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
const [logFile,dest]=process.argv.slice(2)
if(!logFile||!dest)throw Error('usage: materialize.ts LOG DEST')
const log=readFileSync(logFile),root=resolve(dest),rows:object[]=[]
const hash=(b:Buffer)=>createHash('sha256').update(b).digest('hex')
for(const line of log.toString().split('\n')){
  if(!line.startsWith('ARTIFACT '))continue
  const a=JSON.parse(line.slice(9)) as {name:string,sha256:string,gzipBase64:string}
  const target=resolve(root,a.name)
  if(!target.startsWith(root+sep))throw Error('artifact path escapes destination')
  const bytes=gunzipSync(Buffer.from(a.gzipBase64,'base64'),{maxOutputLength:16*1024*1024})
  if(hash(bytes)!==a.sha256)throw Error(`artifact hash mismatch: ${a.name}`)
  mkdirSync(dirname(target),{recursive:true})
  if(existsSync(target)){if(hash(readFileSync(target))!==a.sha256)throw Error(`refuse divergent overwrite: ${target}`)}
  else writeFileSync(target,bytes,{flag:'wx'})
  rows.push({name:a.name,sha256:a.sha256,bytes:bytes.length})
}
if(!rows.length)throw Error('no artifacts')
const output=Buffer.from(JSON.stringify({originLog:logFile,originLogSha256:hash(log),artifacts:rows},null,2)+'\n')
mkdirSync(root,{recursive:true})
const manifest=resolve(root,'materialized-manifest.json')
if(existsSync(manifest)){if(hash(readFileSync(manifest))!==hash(output))throw Error('refuse manifest overwrite')}
else writeFileSync(manifest,output,{flag:'wx'})
console.log(JSON.stringify({artifacts:rows.length,manifest,sha256:hash(output)}))
