import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
const out='runs/track-gen-final',lines=(f:string)=>readFileSync(f,'utf8').trim().split('\n').filter(Boolean)
const paths=[...new Set([...lines(`${out}/staged-files.txt`),...lines(`${out}/source-files.txt`),'kernel/prove.ts','kernel/kernel.ts',`${out}/source-files.txt`,`${out}/staged-files.txt`,'runs/track-gen-hash-final.ts'])].filter(p=>p!==`${out}/SHA256SUMS`).sort()
writeFileSync(`${out}/SHA256SUMS`,paths.map(p=>`${createHash('sha256').update(readFileSync(p)).digest('hex')}  ${p}\n`).join(''))
console.log(JSON.stringify({files:paths.length,manifest:`${out}/SHA256SUMS`}))
