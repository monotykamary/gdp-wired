// Focus-law candidate novelty, not an M2 proof or reconstructed count certificate.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {C,E,Law} from '../../../core/machine.ts'
import {assumed,type Goal} from '../../../kernel/kernel.ts'
import {brokenOf} from '../../../kernel/prove.ts'
import {TriggerIndex} from '../trigger-index.ts'
import {Meter} from '../match.ts'
const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
const sources=['research/egraph/indexed-match.ts','research/egraph/trigger-index.ts','research/egraph/historical/m2-novelty.ts','kernel/kernel.ts','kernel/prove.ts']
const before=Object.fromEntries(sources.map(p=>[p,sha(readFileSync(p))]));console.log('SOURCE',JSON.stringify(before))
if(before['kernel/kernel.ts']!=='596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2'||before['kernel/prove.ts']!=='5e4232da2abe25c1153edf790af4b339d2be8482c5630b0740315c79f60ce708')throw Error('historical kernel drift')
for(const [name,pin]of [['one-value-decided','58496db30029729c33954d6cc01f61673dbe5bc0c52c4f64b1b4126c0dcc20ca'],['decision-quorum','a7cee3dd679c5c19df5fd6110c24a723158e8644299c98243df8c0513bd57357']]){
  const path=`research/egraph/historical/inputs/m2/${name}.json.gz`,bytes=readFileSync(path),input=JSON.parse(gunzipSync(bytes).toString()) as {laws:Law[],law:Law,failure:{goal:Goal,witness?:Record<string,number>}},goal=input.failure.goal
  if(sha(JSON.stringify(goal))!==pin)throw Error('goal pin')
  const law=input.law;if(!law.forall)throw Error('focus law not quantified')
  const keys=[law.forall,...law.keys??[]]
  for(const novelOnly of [false,true]){
    const meter=new Meter(100000,performance.now()+1000);let enumerated=0,rejectedDuplicates=0
    try{
      const key=(o:unknown):string=>{meter.tick();if(Array.isArray(o))return '['+o.map(key).join(',')+']';if(o&&typeof o==='object')return '{'+Object.keys(o).sort().map(k=>JSON.stringify(k)+':'+key((o as Record<string,unknown>)[k])).join(',')+'}';return JSON.stringify(o)??'undefined'}
      const walk=(o:unknown,visit:(q:Record<string,unknown>)=>void):void=>{meter.tick();if(!o||typeof o!=='object')return;visit(o as Record<string,unknown>);for(const v of Object.values(o))if(v&&typeof v==='object')walk(v,visit)}
      const reads:E[]=[];walk(law.holds,q=>{if(q.op==='get')reads.push(q as E)})
      const candidates=reads.map(read=>{const covered=new Set<string>();walk(read,q=>{if(q.op==='var'&&keys.includes(String(q.name)))covered.add(String(q.name))});return {read,covered}})
      const missing=new Set(keys),patterns:E[]=[]
      while(missing.size){
        let best:typeof candidates[number]|undefined,score=0
        for(const candidate of candidates){meter.tick();let n=0;for(const k of candidate.covered){meter.tick();if(missing.has(k))n++}if(n>score){score=n;best=candidate}}
        if(!best)throw Error('read patterns do not bind all focus keys')
        patterns.push(best.read);for(const k of best.covered)missing.delete(k)
      }
      const known=new Set<string>(),remember=(c:C):void=>{known.add(key(c));if(c.op==='and')c.xs.forEach(remember)};goal.hyps.forEach(remember)
      const graph=new TriggerIndex(meter,patterns);graph.seed(goal.hyps)
      const rows:{binding:Record<string,E>,row:C,duplicate:boolean,sha256:string}[]=[]
      const matches=graph.match(patterns,keys,32,binding=>{
        enumerated++;key(law.holds) // charge the complete instantiation traversal as well as serialization
        const row=assumed([law],{[law.name]:keys.map(k=>binding[k]!)})[0];if(!row)throw Error('bad instantiation')
        const encoded=key(row),duplicate=known.has(encoded)
        if(novelOnly&&duplicate){rejectedDuplicates++;return false}
        rows.push({binding,row,duplicate,sha256:sha(encoded)});return true
      })
      const witness=input.failure.witness,instanceBroken=witness?brokenOf({name:'focus candidate CTI diagnostic',hyps:rows.map(r=>r.row)})(witness):undefined
      console.log('NOVELTY',JSON.stringify({name,novelOnly,goalSha256:pin,compressedSha256:sha(bytes),hypotheses:goal.hyps.length,law:law.name,lawSha256:sha(JSON.stringify(law)),keys,patterns,caps:{units:100000,nodes:512,wallMs:1000,maxMatches:32},units:meter.used,nodes:graph.graph.size,fullScan:graph.stats,enumerated,rejectedDuplicates,returned:matches.length,duplicatesReturned:rows.filter(r=>r.duplicate).length,instanceBroken,savedWitnessPresent:!!witness,candidates:rows.map(({binding,duplicate,sha256})=>({binding,duplicate,sha256})),checked:false,noProverInvoked:true,countedReconstructionPending:true}))
    }catch(error){console.log('NOVELTY_REFUSED',JSON.stringify({name,novelOnly,units:meter.used,enumerated,rejectedDuplicates,error:String(error),checked:false}))}
  }
  if(sha(readFileSync(path))!==sha(bytes))throw Error('input mutation')
}
for(const p of sources)if(sha(readFileSync(p))!==before[p])throw Error('source mutation')
console.log('POSTFLIGHT',JSON.stringify({unchanged:true,m2Flip:false,checked:false,noProverInvoked:true}))
