// Exact saved M2 inputs; index ablation only. Candidate generation is not a proof.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {E,Law} from '../../../core/machine.ts'
import type {Goal} from '../../../kernel/kernel.ts'
import {Meter} from '../match.ts'
import {IndexedEGraph} from '../indexed-match.ts'
import {TriggerIndex} from '../trigger-index.ts'
const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
const sources=['research/egraph/match.ts','research/egraph/ite.ts','research/egraph/indexed-match.ts','research/egraph/trigger-index.ts','research/egraph/historical/m2-trigger.ts','kernel/kernel.ts','kernel/cyclic.ts','kernel/prove.ts','core/counts.ts']
const before=Object.fromEntries(sources.map(p=>[p,sha(readFileSync(p))]))
console.log('SOURCE',JSON.stringify(before))
const fixtures=[['one-value-decided','58496db30029729c33954d6cc01f61673dbe5bc0c52c4f64b1b4126c0dcc20ca'],['decision-quorum','a7cee3dd679c5c19df5fd6110c24a723158e8644299c98243df8c0513bd57357']]
for(const [name,pin]of fixtures){
  const path=`research/egraph/historical/inputs/m2/${name}.json.gz`,bytes=readFileSync(path),json=gunzipSync(bytes).toString(),input=JSON.parse(json) as {laws:Law[],failure:{goal:Goal}}
  const goal=input.failure.goal,goalSha256=sha(JSON.stringify(goal));if(goalSha256!==pin)throw Error('historical goal drift')
  const law=input.laws.find(l=>l.name==='P2 vote proposed');if(!law?.forall)throw Error('original P2 absent')
  const keys=[law.forall,...law.keys??[]],reads:E[]=[]
  const visit=(o:unknown):void=>{if(!o||typeof o!=='object')return;const r=o as Record<string,unknown>;if(r.op==='get'&&r.map==='Vote')reads.push(o as E);for(const v of Object.values(r))if(v&&typeof v==='object')visit(v)}
  visit(law.holds);const pattern=reads[0];if(!pattern)throw Error('original Vote trigger absent')
  console.log('INPUT',JSON.stringify({name,compressedSha256:sha(bytes),inputSha256:sha(json),goalSha256,hypotheses:goal.hyps.length,lawNames:input.laws.map(l=>l.name),trigger:pattern,keys,caps:{units:100000,nodes:512,wallMs:1000,maxMatches:32}}))
  for(const materialization of ['full','trigger'] as const){
    const meter=new Meter(100000,performance.now()+1000),graph=materialization==='trigger'?new TriggerIndex(meter,[pattern]):new IndexedEGraph(meter,512,true),raw=graph instanceof TriggerIndex?graph.graph:graph
    let seeded=false,seedUnits:number|undefined
    try{
      graph.seed(goal.hyps);seeded=true;seedUnits=meter.used
      const matches=graph.match([pattern],keys)
      console.log('RESULT',JSON.stringify({name,materialization,seeded,seedUnits,status:'matched',matchingUnits:meter.used,matches,checked:false,reason:'candidate index only; no counted-certificate bridge',stats:{nodes:raw.size,...raw.stats,scan:graph instanceof TriggerIndex?graph.stats:undefined}}))
    }catch(error){console.log('RESULT',JSON.stringify({name,materialization,seeded,seedUnits,status:'unsupported-or-exhausted',matchingUnits:meter.used,reason:String(error),checked:false,stats:{nodes:raw.size,...raw.stats,scan:graph instanceof TriggerIndex?graph.stats:undefined}}))}
  }
  if(sha(readFileSync(path))!==sha(bytes))throw Error('fixture mutated')
}
for(const p of sources)if(sha(readFileSync(p))!==before[p])throw Error('source changed '+p)
console.log('POSTFLIGHT',JSON.stringify({unchanged:true,checked:false,m2Flip:false}))
