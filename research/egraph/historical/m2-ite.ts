import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {Law} from '../../../core/machine.ts'
import type {Goal} from '../../../kernel/kernel.ts'
import {EGraph,Meter} from '../match.ts'
import {IteEGraph} from '../ite.ts'
const sha=(s:string|Buffer)=>createHash('sha256').update(s).digest('hex')
const inventory=(root:unknown)=>{
  const ops:Record<string,number>={},guards:Record<string,number>={}
  const visit=(o:unknown):void=>{if(!o||typeof o!=='object')return;const r=o as Record<string,unknown>;if(typeof r.op==='string'){ops[r.op]=(ops[r.op]??0)+1;if(r.op==='if'){const key=String((r.c as {op:string}).op);guards[key]=(guards[key]??0)+1}}for(const v of Object.values(r))if(v&&typeof v==='object')visit(v)}
  visit(root);return {ops,guards}
}
for(const name of ['one-value-decided','decision-quorum']){
  const bytes=readFileSync(`research/egraph/historical/inputs/m2/${name}.json.gz`),json=gunzipSync(bytes).toString(),e=JSON.parse(json) as {laws:Law[],failure:{goal:Goal}}
  console.log('INVENTORY',JSON.stringify({name,inputSha256:sha(json),goalSha256:sha(JSON.stringify(e.failure.goal)),...inventory(e.failure.goal)}))
  for(const adapter of ['original','ite'] as const)for(const enabled of [false,true]){
    const meter=new Meter(100000,performance.now()+1000),graph=adapter==='ite'?new IteEGraph(meter):new EGraph(meter)
    try{graph.seed(e.failure.goal.hyps);console.log('RESULT',JSON.stringify({name,adapter,enabled,status:'seeded',matchingUnits:meter.used,checked:false,reason:'no counted-certificate bridge; no M2 flip'}))}
    catch(error){console.log('RESULT',JSON.stringify({name,adapter,enabled,status:'unsupported-or-exhausted',matchingUnits:meter.used,reason:String(error),checked:false}))}
  }
  if(sha(readFileSync(`research/egraph/historical/inputs/m2/${name}.json.gz`))!==sha(bytes))throw Error('fixture mutated')
}
const wrapper=JSON.parse(readFileSync('research/egraph/historical/inputs/gdp-wired-laneQ3/core/fixtures/published-ground/paxos-P5-19.json','utf8')) as {data:string}
const json=gunzipSync(Buffer.from(wrapper.data,'base64')).toString(),p=JSON.parse(json) as Record<string,unknown>
console.log('Q3_FIXTURE',JSON.stringify({id:'paxos-P5-19',sha256:sha(json),keys:Object.fromEntries(Object.entries(p).map(([k,v])=>[k,Array.isArray(v)?{length:v.length}:v&&typeof v==='object'?{keys:Object.keys(v)}:v])),inventory:inventory(p)}))
