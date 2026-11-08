// Persist large diagnostic receipts on the same VM and fetch bounded chunks.
import {readFileSync,writeFileSync,mkdtempSync} from 'node:fs'
import {basename,join} from 'node:path'
import {homedir} from 'node:os'
import {createHash} from 'node:crypto'
import {brotliCompressSync,constants} from 'node:zlib'
const files=Object.fromEntries(process.argv.slice(2).map(p=>[basename(p),readFileSync(p,'utf8')])),bytes=brotliCompressSync(Buffer.from(JSON.stringify(files)),{params:{[constants.BROTLI_PARAM_QUALITY]:9}}),dir=mkdtempSync(join(homedir(),'track-m-s10-receipts-')),encoded=bytes.toString('base64'),size=200000
let parts=0;for(let i=0;i<encoded.length;i+=size)writeFileSync(join(dir,`${parts++}.txt`),encoded.slice(i,i+size))
const manifest={artifact:'section10-chunk-manifest',dir,parts,bytes:bytes.length,sha256:createHash('sha256').update(bytes).digest('hex'),files:Object.keys(files)};writeFileSync(join(dir,'manifest.json'),JSON.stringify(manifest));console.log(JSON.stringify(manifest))
