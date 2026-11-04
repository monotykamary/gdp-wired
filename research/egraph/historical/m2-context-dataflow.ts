// Existing count-row recovery, no prover and no accepted M2 proof.
import {readFileSync,writeFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {gunzipSync,gzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {Law,Machine} from '../../../core/machine.ts'
import {type Goal,type Instances,type MapRead} from '../../../kernel/kernel.ts'
import {recoverCounts} from '../recover-counts.ts'
import {recoverFlags} from '../recover-flags.ts'
import {stableKey} from '../recover-instances.ts'
import {Meter} from '../match.ts'
const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
const sourcePaths=['research/egraph/recover-counts.ts','research/egraph/recover-flags.ts','research/egraph/historical/context-cold-check.ts','research/egraph/historical/m2-context-dataflow.ts','kernel/kernel.ts'],source=Object.fromEntries(sourcePaths.map(p=>[p,sha(readFileSync(p))]))
if(source['kernel/kernel.ts']!=='596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2')throw Error('kernel drift')
const metadata=readFileSync('research/egraph/historical/recovery/v7.json')
if(sha(metadata)!=='d420ce6fb3b0bab0bd6dfed6379fca6d088a3f73431e9713cdd8ec5f2b1d179f')throw Error('metadata pin')
const records=(JSON.parse(metadata.toString()) as {records:{name:string,goalSha256:string,compressedSha256:string,instances:Instances,reads:MapRead[]}[]}).records
console.log('SOURCE',JSON.stringify({source,metadataSha256:sha(metadata)}))
for(const r of records.filter(r=>r.name==='one-value-decided')){
  const path=`research/egraph/historical/inputs/m2/${r.name}.json.gz`,bytes=readFileSync(path),input=JSON.parse(gunzipSync(bytes).toString()) as {m:Machine,laws:Law[],law:Law,failure:{goal:Goal}},goal=input.failure.goal
  if(sha(bytes)!==r.compressedSha256||sha(JSON.stringify(goal))!==r.goalSha256)throw Error('input pin')
  const meter=new Meter(100000,performance.now()+1000);let phase='flags'
  try{
    const flags=recoverFlags(goal,input.m,input.laws,input.law.name,r.instances,meter),base=flags.base;phase='counts'
    const recovered=recoverCounts(goal,base.decls,r.reads,meter),original=new Set(recovered.originalKeys)
    const baseKeys=base.goal.hyps.map(c=>stableKey(c,meter))
    if(baseKeys.some(key=>!original.has(key)))throw Error('base has a row absent from original')
    phase='compare';const rebuiltKeys=[...baseKeys,...recovered.countRowKeys],rebuiltSet=new Set(rebuiltKeys)
    const missing=recovered.originalKeys.flatMap((key,i)=>rebuiltSet.has(key)?[]:[i]),extra=rebuiltKeys.flatMap((key,i)=>original.has(key)?[]:[i])
    const packet={name:r.name,goalSha256:r.goalSha256,metadata:{instances:flags.instances,reads:recovered.reads,insts:recovered.insts,picks:recovered.picks}}
    let coldMatched=false
    if(!missing.length&&!extra.length&&rebuiltKeys.length===recovered.originalKeys.length&&rebuiltKeys.every((key,i)=>key===recovered.originalKeys[i])){
      const bytes=JSON.stringify(packet),file=`context-${r.name}.json`;writeFileSync(file,bytes)
      const cold=spawnSync('bun',['--no-install','research/egraph/historical/context-cold-check.ts',file],{encoding:'utf8',timeout:5000})
      coldMatched=cold.status===0&&!cold.signal&&!cold.error;console.log(cold.stdout.trim());if(cold.stderr)console.error(cold.stderr)
      if(coldMatched)console.log('ARTIFACT',JSON.stringify({path:file,sha256:sha(bytes),gzipBase64:gzipSync(bytes).toString('base64')}))
    }
    console.log('COUNT_RECOVERY',JSON.stringify({name:r.name,goalSha256:r.goalSha256,units:meter.used,originalHypotheses:goal.hyps.length,baseHypotheses:base.goal.hyps.length,reads:recovered.reads.length,instances:recovered.insts.length,picks:recovered.picks.length,rebuiltHypotheses:rebuiltKeys.length,coldMatched,missingOriginalRows:missing,extraRebuiltRows:extra,sameOrderedRows:rebuiltKeys.length===recovered.originalKeys.length&&rebuiltKeys.every((key,i)=>key===recovered.originalKeys[i]),flagRecords:flags.records.length,metadata:{instances:flags.instances,reads:recovered.reads,insts:recovered.insts,picks:recovered.picks},checked:false,noProverInvoked:true}))
  }catch(error){console.log('COUNT_RECOVERY_REFUSED',JSON.stringify({name:r.name,units:meter.used,phase,error:String(error),checked:false}))}
  if(sha(readFileSync(path))!==sha(bytes))throw Error('input drift')
}
for(const p of sourcePaths)if(sha(readFileSync(p))!==source[p])throw Error('source drift')
console.log('POSTFLIGHT',JSON.stringify({unchanged:true,checked:false,m2Flip:false,noProverInvoked:true}))
