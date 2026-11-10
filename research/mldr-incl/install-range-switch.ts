// Disposable boat-checkout experiment; never imported by the production prover.
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync} from 'node:fs'
const path='core/counts.ts',source=readFileSync(path,'utf8'),before='      if (!pass) return c',after='      if (!pass || process.env.MLDR_INCL_SKIP_INITIAL_RANGES === "1") return c'
if(source.split(before).length!==2)throw Error('non-unique initial-range anchor')
const result=source.replace(before,after);writeFileSync(path,result)
const hash=(text:string)=>createHash('sha256').update(text).digest('hex')
console.log(JSON.stringify({diagnostic:true,rangeSwitch:true,before:hash(source),after:hash(result)}))
