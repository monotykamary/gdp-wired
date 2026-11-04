// Recover provenance only; never promote an approximate context to the exact M2 goal.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {E,Law,Machine} from '../../../core/machine.ts'
import {countedObligations,type Goal,type MapRead} from '../../../kernel/kernel.ts'
import {Meter} from '../match.ts'
import {recoverInstances,stableKey} from '../recover-instances.ts'
const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
const sources=['research/egraph/recover-instances.ts','research/egraph/historical/m2-recover.ts','kernel/kernel.ts'],before=Object.fromEntries(sources.map(p=>[p,sha(readFileSync(p))]))
if(before['kernel/kernel.ts']!=='596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2')throw Error('kernel drift')
console.log('SOURCE',JSON.stringify(before))
for(const [name,pin]of [['one-value-decided','58496db30029729c33954d6cc01f61673dbe5bc0c52c4f64b1b4126c0dcc20ca'],['decision-quorum','a7cee3dd679c5c19df5fd6110c24a723158e8644299c98243df8c0513bd57357']]){
  const path=`research/egraph/historical/inputs/m2/${name}.json.gz`,bytes=readFileSync(path),input=JSON.parse(gunzipSync(bytes).toString()) as {m:Machine,laws:Law[],law:Law,failure:{goal:Goal}},goal=input.failure.goal
  if(sha(JSON.stringify(goal))!==pin)throw Error('goal drift')
  const meter=new Meter(100000,performance.now()+1000),progress={visitedRows:0,attemptedPairs:0,reconstructed:0}
  try{
    const recovery=recoverInstances(goal,input.laws,meter,512,progress)
    const base=countedObligations(input.m,input.laws,{[input.law.name]:recovery.instances},input.laws.findIndex(l=>l.name===input.law.name)).find(p=>p.goal.name.endsWith('@step'))
    if(!base)throw Error('no reconstructed step')
    const originalKeys=goal.hyps.map(c=>stableKey(c,meter)),baseKeys=base.goal.hyps.map(c=>stableKey(c,meter)),originalSet=new Set(originalKeys),baseSet=new Set(baseKeys)
    const uncovered=originalKeys.flatMap((key,i)=>baseSet.has(key)?[]:[i]),extra=baseKeys.flatMap((key,i)=>originalSet.has(key)?[]:[i])
    const maps=new Set(base.decls.map(d=>d.map)),reads=new Map<string,MapRead>(),witnesses=new Set<string>()
    const walk=(o:unknown):void=>{
      meter.tick();if(!o||typeof o!=='object')return
      const q=o as Record<string,unknown>
      if(q.op==='var'&&typeof q.name==='string'&&q.name.startsWith('w$'))witnesses.add(q.name)
      if(q.op==='='){
        const a=q.a as E,b=q.b as E
        if(a.op==='var'&&a.name.startsWith('r$')&&b.op==='get'&&maps.has(b.map))reads.set(stableKey([a.name,b.map,b.key],meter),[a.name,b.map,b.key])
      }
      for(const v of Object.values(q))if(v&&typeof v==='object')walk(v)
    };walk(goal.hyps)
    console.log('RECOVERY',JSON.stringify({name,goalSha256:pin,compressedSha256:sha(bytes),originalHypotheses:goal.hyps.length,units:meter.used,progress,recoveredInstances:recovery.instances,records:recovery.records,baseHypotheses:base.goal.hyps.length,uncoveredOriginalRows:uncovered,extraBaseRows:extra,exactOriginalMatch:JSON.stringify(base.goal)===JSON.stringify(goal),declarations:base.decls,candidateReadMetadata:[...reads.values()],candidateWitnessNames:[...witnesses],checked:false,scope:'existing-row provenance only; count/flag rows must be reconstructed and checked before any M2 proof admission'}))
  }catch(error){console.log('RECOVERY_REFUSED',JSON.stringify({name,units:meter.used,progress,error:String(error),checked:false}))}
  if(sha(readFileSync(path))!==sha(bytes))throw Error('input changed')
}
for(const p of sources)if(sha(readFileSync(p))!==before[p])throw Error('source changed')
console.log('POSTFLIGHT',JSON.stringify({unchanged:true,checked:false,m2Flip:false,noProverInvoked:true}))
