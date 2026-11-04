// Admission/provenance diagnostic only. Does not run a prover or accept an M2 proof.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {C,E,Law,Machine} from '../../../core/machine.ts'
import {assumed,countedObligations,type Goal} from '../../../kernel/kernel.ts'
import {brokenOf} from '../../../kernel/prove.ts'
import {TriggerIndex} from '../trigger-index.ts'
import {Meter} from '../match.ts'
const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
const sources=['research/egraph/indexed-match.ts','research/egraph/trigger-index.ts','research/egraph/historical/m2-admission.ts','kernel/kernel.ts','kernel/prove.ts']
const before=Object.fromEntries(sources.map(p=>[p,sha(readFileSync(p))]))
if(before['kernel/kernel.ts']!=='596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2'||before['kernel/prove.ts']!=='5e4232da2abe25c1153edf790af4b339d2be8482c5630b0740315c79f60ce708')throw Error('historical checker/prover pin drift')
console.log('SOURCE',JSON.stringify(before))
for(const [name,pin] of [['one-value-decided','58496db30029729c33954d6cc01f61673dbe5bc0c52c4f64b1b4126c0dcc20ca'],['decision-quorum','a7cee3dd679c5c19df5fd6110c24a723158e8644299c98243df8c0513bd57357']]){
  try {
  const path=`research/egraph/historical/inputs/m2/${name}.json.gz`,bytes=readFileSync(path),input=JSON.parse(gunzipSync(bytes).toString()) as {m:Machine,laws:Law[],law:Law,pass:number,proof?:unknown,failure:{goal:Goal,witness?:Record<string,number>}}
  const goal=input.failure.goal;if(sha(JSON.stringify(goal))!==pin)throw Error('goal pin')
  const law=input.laws.find(l=>l.name==='P2 vote proposed');if(!law?.forall)throw Error('P2 missing')
  const keys=[law.forall,...law.keys??[]],reads:E[]=[]
  const visit=(o:unknown):void=>{if(!o||typeof o!=='object')return;const q=o as Record<string,unknown>;if(q.op==='get'&&q.map==='Vote')reads.push(o as E);for(const v of Object.values(q))if(v&&typeof v==='object')visit(v)}
  visit(law.holds);const pattern=reads[0];if(!pattern)throw Error('Vote trigger missing')
  const meter=new Meter(100000,performance.now()+1000),graph=new TriggerIndex(meter,[pattern]);graph.seed(goal.hyps);const matches=graph.match([pattern],keys),matchingUnits=meter.used
  // A canonical key builder charges every serialization child as well as every node.
  const key=(o:unknown):string=>{meter.tick();if(Array.isArray(o))return '['+o.map(key).join(',')+']';if(o&&typeof o==='object')return '{'+Object.keys(o).sort().map(k=>JSON.stringify(k)+':'+key((o as Record<string,unknown>)[k])).join(',')+'}';return JSON.stringify(o)??'undefined'}
  const known=new Set<string>(),remember=(c:C):void=>{known.add(key(c));if(c.op==='and')c.xs.forEach(remember)}
  goal.hyps.forEach(remember)
  const rows=matches.map(binding=>{
    if(keys.some(k=>!binding[k])||Object.keys(binding).some(k=>!keys.includes(k)))throw Error('invalid binding keys')
    const at=keys.map(k=>binding[k]!),instantiated=assumed([law],{[law.name]:at});if(instantiated.length!==1)throw Error('instance arity')
    const row=instantiated[0]!;return {binding,row,exactDuplicate:known.has(key(row))}
  })
  const auditUnits=meter.used,rawWitness=input.failure.witness,originalBroken=rawWitness?brokenOf(goal)(rawWitness):undefined
  const instanceBroken=rawWitness?brokenOf({name:'saved CTI instance check only',hyps:rows.map(r=>r.row)})(rawWitness):undefined
  // With no retained successful proof, this reconstructs only the empty-instance
  // counted baseline. Differences are recorded, never patched with assumed rows.
  const base=countedObligations(input.m,input.laws,{},input.laws.findIndex(l=>l.name===input.law.name)).find(p=>p.goal.name.endsWith('@step'))
  console.log('ADMISSION',JSON.stringify({name,goalSha256:pin,compressedSha256:sha(bytes),hypotheses:goal.hyps.length,law:law.name,keys,matches:rows.length,matchingUnits,auditUnits,graphNodes:graph.graph.size,fullScan:graph.stats,exactDuplicates:rows.filter(r=>r.exactDuplicate).length,originalBroken,instanceBroken,savedWitnessPresent:!!rawWitness,attemptKeys:Object.keys(input),failureKeys:Object.keys(input.failure),retainedProofPresent:!!input.proof,pass:input.pass,emptyInstanceCountedGoal:base&&{sha256:sha(JSON.stringify(base.goal)),hypotheses:base.goal.hyps.length,declarations:base.decls.length,exactOriginalMatch:JSON.stringify(base.goal)===JSON.stringify(goal)},rows,checked:false,noProverInvoked:true,scope:'kernel-instantiated rows / saved CTI diagnostic only; missing original counted certificate provenance is not reconstructed by assumption'}))
  if(sha(readFileSync(path))!==sha(bytes))throw Error('input mutated')
  } catch(error) {console.log('AUDIT_REFUSED',JSON.stringify({name,error:String(error),checked:false}));process.exitCode=1}
}
for(const p of sources)if(sha(readFileSync(p))!==before[p])throw Error('source drift')
console.log('POSTFLIGHT',JSON.stringify({unchanged:true,checked:false,m2Flip:false,noProverInvoked:true}))
