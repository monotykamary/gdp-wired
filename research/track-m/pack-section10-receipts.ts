// One compressed bundle avoids the remote 400 KB tail dropping early repeats.
import {readFileSync} from 'node:fs'
import {basename} from 'node:path'
import {brotliCompressSync,constants} from 'node:zlib'
const files=Object.fromEntries(process.argv.slice(2).map(file=>[basename(file),readFileSync(file,'utf8')]))
const compressed=brotliCompressSync(Buffer.from(JSON.stringify(files)),{params:{[constants.BROTLI_PARAM_QUALITY]:9}})
console.log(JSON.stringify({artifact:'section10-receipts.br',encoding:'brotli-base64',bytes:compressed.length,data:compressed.toString('base64')}))
