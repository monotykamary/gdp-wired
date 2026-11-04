// Saved-model diagnostic, NOT a whole-context milestone-2 proof.
import {readFileSync} from 'node:fs'
import {gunzipSync,gzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {type C,type E,type Law,n,x,get,same,not} from '../../../core/machine.ts'
import {type Goal,check,linear,substE} from '../../../kernel/kernel.ts'
import {type Fact,refuseCyclic,falseC} from '../../../kernel/cyclic.ts'
import {brokenOf,grow,withWall} from '../../../kernel/prove.ts'
import {EGraph,Meter} from '../match.ts'
import {certify,type Spec} from '../certify.ts'
const hash=(b:string|Buffer)=>createHash('sha256').update(b).digest('hex')
const path='research/egraph/historical/inputs/gdp-wired-laneQ3/core/fixtures/published-ground/paxos-P5-19.json'
const bytes=readFileSync(path),wrapper=JSON.parse(bytes.toString()) as {data:string}
const json=gunzipSync(Buffer.from(wrapper.data,'base64')).toString()
const p=JSON.parse(json) as {laws:Law[],gg:Goal,witness:Record<string,number>}
const law=p.laws.find(l=>l.name==='P2 vote proposed')!
if(!law?.forall)throw Error('missing historical clause')
const keys=[law.forall,...law.keys??[]],reads:E[]=[]
const visit=(o:unknown):void=>{if(!o||typeof o!=='object')return;const q=o as Record<string,unknown>;if(q.op==='get'&&q.map==='Vote')reads.push(o as E);Object.values(q).forEach(v=>{if(v&&typeof v==='object')visit(v)})}
visit(law.holds)
const pattern=reads[0];if(!pattern||pattern.op!=='get')throw Error('missing Vote read')
const coefficients=linear(pattern.key,new Map());if(!coefficients)throw Error('non-affine historical packed key')
// Exact audited historical cell; decode its affine radix from the clause, not a new law.
const cell=4544,value=p.witness[`Vote[1:${cell}]`]
if(value!==1)throw Error('historical selected vote absent')
const ordered=keys.map(k=>[k,coefficients[k]??0] as const).sort((a,b)=>b[1]-a[1])
let remaining=cell-(coefficients['1']??0);const vars:Record<string,E>={}
for(const [key,coefficient]of ordered){if(!Number.isSafeInteger(coefficient)||coefficient<=0)throw Error('unsupported packed coefficient');const v=Math.floor(remaining/coefficient);remaining-=v*coefficient;vars[key]=n(v)}
if(remaining!==0)throw Error('not an exact packed key')
const reified=substE(pattern.key,{vars,maps:{},flags:{}})
const equality:Goal={name:'historical packed-key reification',hyps:[not(same(reified,n(cell)))]}
const arithmetic=withWall(performance.now()+1000,()=>grow(equality))
if(!('tree'in arithmetic)||!check(equality,arithmetic.tree))throw Error('unverified reification')
const meter=new Meter(100000,performance.now()+1000),graph=new EGraph(meter)
graph.seed([same(get('Vote',reified),n(value))])
const matches=graph.match([pattern],keys)
const fact:Fact={name:law.name,keys,holds:law.holds}
const modelPoints:C[]=[same(x('size'),n(p.witness.size!)),same(get('Vote',n(cell)),n(value)),same(get('Proposal',n(448)),n(p.witness['Proposal[1:448]']!))]
const base:Spec={name:'paxos-P5-19 model refutation (not M2)',hyps:[...p.gg.hyps,...modelPoints],concl:falseC,rank:[n(0)],insts:[],uses:[]}
const initiallyBroken=brokenOf(p.gg)(p.witness)
console.log('Q3_INPUT',JSON.stringify({id:'paxos-P5-19',wrapperSha256:hash(bytes),payloadSha256:hash(json),goalSha256:hash(JSON.stringify(p.gg)),fullHistoricalHypotheses:p.gg.hyps.length,initiallyBroken,coefficients,decoded:vars,actualModelPoints:modelPoints,matches,matchingUnits:meter.used,scope:'one saved model, not a protocol or M2 proof'}))
if(initiallyBroken.length)throw Error('original model does not satisfy dumped ground rows')
for(const mode of ['disabled','enabled','wrong-ballot'] as const){
  const insts=mode==='disabled'?[]:matches.map(binding=>({fact:0,at:keys.map((k,i)=>mode==='wrong-ballot'&&i===1?n(8):binding[k]!)}))
  const result=certify([fact],[{...base,insts}],meter.used)
  const proof=result.proof,serialized=proof&&JSON.stringify(proof)
  let removal:string|undefined
  if(result.checked&&proof){const bad=structuredClone(proof);bad.nodes[0]!.insts=[];removal=refuseCyclic(bad);if(!removal)throw Error('nonessential clause instance')}
  console.log('Q3_RESULT',JSON.stringify({mode,checked:result.checked,reason:result.reason,proofSha256:serialized&&hash(serialized),removal,scope:'saved-model refutation only'}))
  if(serialized)console.log('ARTIFACT',JSON.stringify({name:`q3-${mode}.json`,sha256:hash(serialized),gzipBase64:gzipSync(serialized).toString('base64')}))
}
if(hash(readFileSync(path))!==hash(bytes))throw Error('fixture mutated')
