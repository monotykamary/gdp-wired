// Observation only; stop after the original harness supplies its admission family.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux copy required')
const path='core/counts.ts',before=readFileSync(path,'utf8'),anchor='  const context=countSupportContext(m,caller,set,support)'
if(before.split(anchor).length!==2)throw Error('original-family observation anchor changed')
writeFileSync(path,before.replace(anchor,anchor+"\n  countsDump.on?.({phase:'original-family',machine:m,laws:context.laws,caller,support:[...context.support],candidateLaws:set})"))
