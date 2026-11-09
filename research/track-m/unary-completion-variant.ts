// Disposable scheduling-only follow-up to the early-completion / flags-first pair.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.env.LAB_DISPOSABLE!=='1')throw Error('LAB_DISPOSABLE=1 required')
const path='core/counts.ts',source=readFileSync(path,'utf8')
const before='if (pass && reads(law.holds, isCount).size) completeCounts()'
if(source.split(before).length!==2)throw Error('non-unique early-completion anchor')
writeFileSync(path,source.replace(before,'if (pass && !law.keys?.length && reads(law.holds, isCount).size) completeCounts()'))
console.log(JSON.stringify({variant:'unary-early-completion',deferMultiKey:true,edits:1}))
