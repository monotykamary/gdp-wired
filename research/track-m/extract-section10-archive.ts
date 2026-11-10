import {readFileSync,writeFileSync,readdirSync} from 'node:fs'
import {join,basename} from 'node:path'
import {createHash} from 'node:crypto'
import {brotliDecompressSync} from 'node:zlib'
const dir=process.argv[2],parts=process.argv[3];if(!dir)throw new Error('DIR [PARTS] required')
const manifest=readFileSync(join(dir,'diagnostic.log'),'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)).find(r=>r.artifact==='section10-chunk-manifest');if(!manifest)throw new Error('manifest missing')
const chunks=new Map<number,string>();if(parts)for(const file of readdirSync(parts).filter(n=>n.endsWith('.log')))for(const line of readFileSync(join(parts,file),'utf8').split('\n')){if(!line.startsWith('{'))continue;const r=JSON.parse(line);if(Number.isInteger(r.part)&&typeof r.data==='string')chunks.set(r.part,r.data)}
if(parts&&chunks.size!==manifest.parts)throw new Error('chunks missing');const bytes=parts?Buffer.from(Array.from({length:manifest.parts},(_,i)=>{const s=chunks.get(i);if(!s)throw new Error('part missing');return s}).join(''),'base64'):readFileSync(join(dir,'receipts.br'));if(createHash('sha256').update(bytes).digest('hex')!==manifest.sha256)throw new Error('archive hash mismatch')
const files=JSON.parse(brotliDecompressSync(bytes).toString()) as Record<string,string>;for(const [name,text]of Object.entries(files)){if(name!==basename(name))throw new Error('unsafe artifact name');writeFileSync(join(dir,name),text)}writeFileSync(join(dir,'receipts.br'),bytes);writeFileSync(join(dir,'archive-manifest.json'),JSON.stringify(manifest,null,2)+'\n');console.log(JSON.stringify({verified:true,files:Object.keys(files),bytes:bytes.length}))
