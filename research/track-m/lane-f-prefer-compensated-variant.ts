// Disposable optional-proposal filtering; no goal hypothesis is removed.
import {readFileSync,writeFileSync,renameSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const file='core/count-recovery/derivability-closure.ts',source=readFileSync(file,'utf8')
const before='const pool=cert.insts.flatMap((q,index)=>q.terms.length<=5?[index]:[]).sort((a,b)=>rank(a)-rank(b))'
const after=`const shadowed=shadowedTransportIndices(cert)
 trace.push({stage:'closure-compensated-preference',excluded:[...shadowed].map(index=>({index,terms:cert.insts[index]!.terms}))})
 const pool=cert.insts.flatMap((q,index)=>q.terms.length<=5&&!shadowed.has(index)?[index]:[]).sort((a,b)=>rank(a)-rank(b))`
if(source.split(before).length!==2)throw Error('proposal pool anchor changed')
writeFileSync(file+'.tmp',"import {shadowedTransportIndices} from '../../research/track-m/prefer-compensated.ts'\n"+source.replace(before,after));renameSync(file+'.tmp',file)
