// T-F1: defer only the pre-transport case certificate check, in a snapshot.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux snapshot required')
const file='core/count-cases.ts',before=readFileSync(file,'utf8')
const marker='return result&&checkMC(packet.goal.hyps,packet.decls,result)?{instances:at,cert:result}:undefined'
if(before.split(marker).length!==2)throw new Error('missing F1 boundary')
const after=before.replace(marker,'void checkMC; return result?{instances:at,cert:result}:undefined')
writeFileSync(file,after)
console.log(JSON.stringify({installed:'T-F1',deferred:'pre-transport proveCountCases checkMC',finalCheck:'unchanged run-phase-census checkMC',harnessChanged:false,kernelChanged:false}))
