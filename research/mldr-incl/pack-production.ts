// Lossless diagnostic archive, not a proof verifier or a suite gate.
import {createHash} from 'node:crypto'
import {existsSync,readFileSync} from 'node:fs'
import {join} from 'node:path'
import {brotliCompressSync,constants} from 'node:zlib'

export function packProduction(dir:string,maxBytes=240000){
 if(!Number.isInteger(maxBytes)||maxBytes<1||maxBytes>240000)throw Error('invalid capture limit')
 const names=['family-source.json'],proofNames=['production-proof.json','final-proof-0.json','final-proof-1.json']
 const present=proofNames.filter(name=>existsSync(join(dir,name)))
 if(present.length&&present.length!==proofNames.length)throw Error('incomplete production proof archive')
 names.push(...present)
 const files=Object.fromEntries(names.map(name=>{const text=readFileSync(join(dir,name),'utf8');JSON.parse(text);return [name,text]}))
 const bytes=brotliCompressSync(Buffer.from(JSON.stringify(files)),{params:{[constants.BROTLI_PARAM_QUALITY]:4}})
 if(bytes.length>maxBytes)throw Error('complete production archive exceeds log allowance; refusing to omit required files')
 return {artifact:'mldr-incl-production-capture',diagnostic:true,conditional:true,files:names.length,filenames:names,omitted:0,sha256:createHash('sha256').update(bytes).digest('hex'),data:bytes.toString('base64')}
}
if(import.meta.main)console.log(JSON.stringify(packProduction(process.argv[2]!)))
