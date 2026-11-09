// Disposable observation only: no selection, proof, budget or scheduling change.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.env.LAB_DISPOSABLE!=='1')throw Error('LAB_DISPOSABLE=1 required')
const file='core/counts.ts',source=readFileSync(file,'utf8')
const before='certificateRequest: b.c, hyps: b.gg?.hyps, witness, seedCount})'
const after='certificateRequest: b.c, hyps: b.gg?.hyps, witness, seedCount, runtimeSelection: {supported, wide, lazyMode, pool: b.pool ? {keys: b.pool.keys, active: [...(b.pool.chosen ?? chosen)], cap: b.pool.cap ?? null} : null}})'
if(source.split(before).length!==2)throw Error('non-unique observation anchor')
writeFileSync(file,source.replace(before,after))
console.log(JSON.stringify({observationOnly:true,changedSelection:false,changedBudget:false}))
