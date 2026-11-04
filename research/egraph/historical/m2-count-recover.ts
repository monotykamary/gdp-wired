// Existing count-row recovery, no prover and no accepted M2 proof.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {Law,Machine} from '../../../core/machine.ts'
import {countedObligations,mcGoal,type Goal,type Instances,type MapRead} from '../../../kernel/kernel.ts'
import {recoverCounts} from '../recover-counts.ts'
import {stableKey} from '../recover-instances.ts'
import {Meter} from '../match.ts'
const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
const sourcePaths=['research/egraph/recover-counts.ts','research/egraph/historical/m2-count-recover.ts','kernel/kernel.ts'],source=Object.fromEntries(sourcePaths.map(p=>[p,sha(readFileSync(p))]))
if(source['kernel/kernel.ts']!=='596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2')throw Error('kernel drift')
const metadata=readFileSync('research/egraph/historical/recovery/v7.json')
if(sha(metadata)!=='d420ce6fb3b0bab0bd6dfed6379fca6d088a3f73431e9713cdd8ec5f2b1d179f')throw Error('metadata pin')
const records=(JSON.parse(metadata.toString()) as {records:{name:string,goalSha256:string,compressedSha256:string,instances:Instances,reads:MapRead[]}[]}).records
console.log('SOURCE',JSON.stringify({source,metadataSha256:sha(metadata)}))
for(const r of records){
  const path=`research/egraph/historical/inputs/m2/${r.name}.json.gz`,bytes=readFileSync(path),input=JSON.parse(gunzipSync(bytes).toString()) as {m:Machine,laws:Law[],law:Law,failure:{goal:Goal}},goal=input.failure.goal
  if(sha(bytes)!==r.compressedSha256||sha(JSON.stringify(goal))!==r.goalSha256)throw Error('input pin')
  const meter=new Meter(100000,performance.now()+1000)
  try{
    const base=countedObligations(input.m,input.laws,{[input.law.name]:r.instances},input.laws.findIndex(l=>l.name===input.law.name)).find(x=>x.goal.name.endsWith('@step'))!
    const recovered=recoverCounts(goal,base.decls,r.reads,meter),original=new Set(recovered.originalKeys)
    if(base.goal.hyps.some(c=>!original.has(stableKey(c,meter))))throw Error('base has a row absent from original')
    const rebuilt=mcGoal(base.goal.hyps,base.decls,recovered);if(!rebuilt)throw Error('count reconstruction refused')
    const rebuiltKeys=rebuilt.hyps.map(c=>stableKey(c,meter)),rebuiltSet=new Set(rebuiltKeys)
    const missing=recovered.originalKeys.flatMap((key,i)=>rebuiltSet.has(key)?[]:[i]),extra=rebuiltKeys.flatMap((key,i)=>original.has(key)?[]:[i])
    console.log('COUNT_RECOVERY',JSON.stringify({name:r.name,goalSha256:r.goalSha256,units:meter.used,originalHypotheses:goal.hyps.length,baseHypotheses:base.goal.hyps.length,reads:recovered.reads.length,instances:recovered.insts.length,picks:recovered.picks.length,rebuiltHypotheses:rebuilt.hyps.length,missingOriginalRows:missing,extraRebuiltRows:extra,sameOrderedRows:rebuiltKeys.length===recovered.originalKeys.length&&rebuiltKeys.every((key,i)=>key===recovered.originalKeys[i]),metadata:{instances:r.instances,reads:recovered.reads,insts:recovered.insts,picks:recovered.picks},checked:false,noProverInvoked:true}))
  }catch(error){console.log('COUNT_RECOVERY_REFUSED',JSON.stringify({name:r.name,units:meter.used,error:String(error),checked:false}))}
  if(sha(readFileSync(path))!==sha(bytes))throw Error('input drift')
}
for(const p of sourcePaths)if(sha(readFileSync(p))!==source[p])throw Error('source drift')
console.log('POSTFLIGHT',JSON.stringify({unchanged:true,checked:false,m2Flip:false,noProverInvoked:true}))
