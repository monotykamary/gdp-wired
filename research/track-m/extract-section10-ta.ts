import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {basename,join} from 'node:path'
import {brotliDecompressSync,gunzipSync} from 'node:zlib'
const dir=process.argv[2];if(!dir)throw new Error('DIR required')
for(const line of readFileSync(join(dir,'t10a.log'),'utf8').split('\n')){if(!line.startsWith('{'))continue;const r=JSON.parse(line);if(r.encoding==='brotli-base64'){const raw=brotliDecompressSync(Buffer.from(r.data,'base64'));writeFileSync(join(dir,'receipts.br'),Buffer.from(r.data,'base64'));for(const [name,text]of Object.entries(JSON.parse(raw.toString()) as Record<string,string>)){if(name!==basename(name))throw new Error('unsafe artifact path');writeFileSync(join(dir,name),text)}}else if(r.encoding==='gzip-base64'&&r.artifact===basename(r.artifact))writeFileSync(join(dir,r.artifact),gunzipSync(Buffer.from(r.data,'base64')));else if(r.event)console.log(JSON.stringify(r))}
if(existsSync(join(dir,'summary.json')))console.log(readFileSync(join(dir,'summary.json'),'utf8'))
