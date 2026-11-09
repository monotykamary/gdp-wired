import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
const digest=(text:string)=>createHash('sha256').update(text).digest('hex')
const identity=JSON.parse(readFileSync('integ-input/identity.json','utf8'))
const before=readFileSync('integ-input/type-before-counts.source','utf8'),after=readFileSync('core/counts.ts','utf8')
if(digest(before)!==identity.runtimeReferenceSha256||digest(after)!==identity.counts.candidate)throw Error('count-source identity mismatch')
const transpiler=new Bun.Transpiler({loader:'ts'}),left=transpiler.transformSync(before),right=transpiler.transformSync(after)
if(left!==right||digest(right)!==identity.runtimeSha256)throw Error('type-only change altered emitted runtime')
console.log('COUNT_RUNTIME_IDENTICAL '+digest(right))
