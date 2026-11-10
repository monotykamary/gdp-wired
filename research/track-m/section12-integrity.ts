import {readFileSync,readdirSync,statSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
const files=(p:string):string[]=>readdirSync(p).sort().flatMap(n=>statSync(join(p,n)).isDirectory()?files(join(p,n)):[join(p,n)])
const hashes=Object.fromEntries(['core','kernel'].flatMap(files).map(p=>[p,createHash('sha256').update(readFileSync(p)).digest('hex')]))
const [mode,file]=process.argv.slice(2);if(!file)throw new Error('MODE FILE required')
if(mode==='before')writeFileSync(file,JSON.stringify(hashes)+'\n')
else if(mode==='after'){
 const before=JSON.parse(readFileSync(file,'utf8')),changed=Object.keys(hashes).filter(p=>before[p]!==hashes[p])
 const allowed=['core/count-cases.ts','core/count-recovery/derivability-closure.ts',...(process.env.TRACK_M_SHARDS==='1'?['core/count-focus-proof.ts']:[])]
 if(Object.keys(before).length!==Object.keys(hashes).length||changed.some(p=>!allowed.includes(p)))throw new Error('unexpected production or kernel mutation')
 console.log(JSON.stringify({revision:'5974b9165d6860f1157f3bed3cd66a7e1514e904',kernelIdentical:true,changedForInstrumentation:changed,checksums:hashes}))
}else throw new Error('unknown mode')
