// Pure transport of retained certificates; no prover imports and no fallback search.
import {readFileSync,writeFileSync} from 'node:fs'
import {gunzipSync,gzipSync} from 'node:zlib'
import {spawnSync} from 'node:child_process'
import type {E,Machine,Law} from '../../../core/machine.ts'
import {countedObligations,mcGoal,checkMC,checkCountedLaws,substC,substE,type CountCert,type Instances} from '../../../kernel/kernel.ts'
import {contextBindings} from '../context-bindings.ts'
import {transportTree} from '../transport.ts'
import {stableKey} from '../recover-instances.ts'
import {Meter} from '../match.ts'
import {frozenStart,sha} from './start-context.ts'
import {p3Context} from './p3-context.ts'
type Input={m:Machine,laws:Law[],law:Law}
type Item={instances:Instances,cert:CountCert}
type Entry={id:string,input:Input,start:Item,step:Item}
const meter=new Meter(2000000,performance.now()+25000),canonical=frozenStart('safety').input,entries:Entry[]=[],pins:Record<string,string>={}
const load=<T>(path:string,expected?:string):T=>{const bytes=readFileSync(path),hash=sha(bytes);if(expected&&hash!==expected)throw Error('artifact pin '+path);pins[path]=hash;return JSON.parse(bytes.toString()) as T}
const canonicalMachineSha256=sha(JSON.stringify(canonical.m)),canonicalLawsSha256=sha(JSON.stringify(canonical.laws))
for(const path of ['research/egraph/historical/inputs/m2/one-value-decided.json.gz','research/egraph/historical/inputs/m2/decision-quorum.json.gz','research/egraph/historical/recovery/p3-v9.json','kernel/kernel.ts','kernel/cyclic.ts','core/check.ts','core/solver.ts'])pins[path]=sha(readFileSync(path))
const manifest=load<{artifacts:{id:string,file:string,gzipSha256:string,rawSha256:string}[]}>('research/egraph/historical/inputs/m2/positives/manifest.json')
for(const a of manifest.artifacts){
  const path='research/egraph/historical/inputs/m2/positives/'+a.file,compressed=readFileSync(path),bytes=gunzipSync(compressed)
  if(sha(compressed)!==a.gzipSha256||sha(bytes)!==a.rawSha256)throw Error('positive pin');pins[path]=sha(compressed)
  const e=JSON.parse(bytes.toString()) as Input&{proof:{instances:Instances,certs:Record<string,CountCert>}}
  entries.push({id:a.id,input:e,start:{instances:e.proof.instances,cert:e.proof.certs[e.law.name+' @start']!},step:{instances:e.proof.instances,cert:e.proof.certs[e.law.name+' @step']!}})
}
const safety=load<{instances:Instances,cert:CountCert}>('research/egraph/historical/proofs/safety-direct-step.json','24313e871cc918c83ac3508f295fe19d810d6ec886abf91924a0fadab005b7c3')
const ss=load<{cert:CountCert}>('research/egraph/historical/proofs/safety-start.json','0764d08c7f0fe01222bb77666337b51b88ffa62ca3715295afbfc30ac3836336')
entries.push({id:'safety',input:canonical,start:{instances:{},cert:ss.cert},step:safety})
const p3=p3Context(),ps=load<{cert:CountCert}>('research/egraph/historical/proofs/p3-start.json','3560a3b55b7dd9e0fca4da96201e0f569f4a419cf268b33f130a45b7ceafdc51'),pt=load<{cert:CountCert}>('research/egraph/historical/proofs/p3-bridge-step.json','d72bcca7891d1273cceb9f4db1bed0dc02e9f66cb65c56e51184b676d131499b')
entries.push({id:'P3',input:p3.input,start:{instances:{},cert:ps.cert},step:{instances:p3.metadata.instances,cert:pt.cert}})
const mapped=entries.map(e=>({e,binding:contextBindings(e.input,canonical)}))
const varsOf=(names:Record<string,string>)=>Object.fromEntries(Object.entries(names).map(([a,b])=>[a,{op:'var',name:b} as E]))
const instances:Record<string,Instances>={}
for(const {e,binding}of mapped){const sub={vars:varsOf(binding.renamings),maps:{},flags:{}};instances[e.input.law.name]=Object.fromEntries(Object.entries(e.step.instances).map(([name,args])=>[name,args.map(x=>substE(x,sub))]))}
const targetGoals=countedObligations(canonical.m,canonical.laws,instances),expectedNames=canonical.laws.flatMap(l=>[l.name+' @start',l.name+' @step'])
if(targetGoals.length!==12||new Set(targetGoals.map(g=>g.goal.name)).size!==12||JSON.stringify(targetGoals.map(g=>g.goal.name))!==JSON.stringify(expectedNames))throw Error('default canonical obligation set differs')
const certs:Record<string,CountCert>={},records=[]
for(const {e,binding}of mapped){
  const sub={vars:varsOf(binding.renamings),maps:{},flags:{}}
  for(const phase of ['start','step'] as const){
    const name=e.input.law.name+' @'+phase,item=e[phase],source=countedObligations(e.input.m,e.input.laws,{[e.input.law.name]:item.instances}).find(g=>g.goal.name===name)!
    const target=targetGoals.find(g=>g.goal.name===name)!
    const cert:CountCert={...item.cert,reads:item.cert.reads.map(([name,map,key])=>[name,map,substE(key,sub)]),insts:item.cert.insts.map(i=>({...i,below:substE(i.below,sub)})),picks:item.cert.picks?.map(([name,keys])=>[name,keys.map(k=>substE(k,sub))])}
    const before=mcGoal(source.goal.hyps,source.decls,item.cert)!,after=mcGoal(target.goal.hyps,target.decls,cert)!
    const available=new Map<string,number>();for(const row of after.hyps){const k=stableKey(row,meter);available.set(k,(available.get(k)??0)+1)}
    for(const row of before.hyps){const k=stableKey(substC(row,sub),meter),n=available.get(k)??0;if(!n)throw Error(e.id+' '+phase+': source hypothesis absent after renaming');available.set(k,n-1)}
    const unchanged=JSON.stringify(before.hyps)===JSON.stringify(after.hyps)
    cert.tree=unchanged?item.cert.tree:transportTree(before,after,item.cert.tree,binding.renamings,meter)
    const checked=checkMC(target.goal.hyps,target.decls,cert);if(!checked)throw Error(e.id+' '+phase+': transported certificate rejected')
    certs[target.goal.name]=cert
    const record={id:e.id,phase,name:target.goal.name,sourceCertificateSha256:sha(JSON.stringify(item.cert)),transformedCertificateSha256:sha(JSON.stringify(cert)),canonicalObligationSha256:sha(JSON.stringify(target)),sourceGoalSha256:sha(JSON.stringify(before)),canonicalGoalSha256:sha(JSON.stringify(after)),sourceRows:before.hyps.length,canonicalRows:after.hyps.length,unchanged,checked,transportUnits:meter.used}
    records.push(record);console.log('TRANSPORT',JSON.stringify(record))
  }
}
if(records.length!==12||!checkCountedLaws(canonical.m,canonical.laws,{instances,certs}))throw Error('canonical conjunction rejected')
const packet=JSON.stringify({canonicalInputSha256:frozenStart('safety').inputSha256,canonicalMachineSha256,canonicalLawsSha256,canonicalGoalOrder:expectedNames,sourceArtifacts:pins,bindings:mapped.map(({e,binding})=>({id:e.id,...binding})),instances,certs,records,proofSearchQueries:0})
writeFileSync('canonical-six-law.json',packet)
const cold=spawnSync('bun',['--no-install','research/egraph/historical/canonical-cold.ts','canonical-six-law.json'],{encoding:'utf8',timeout:5000})
console.log(cold.stdout.trim());if(cold.stderr)console.error(cold.stderr)
if(cold.status!==0||cold.error||cold.signal)throw Error('cold conjunction rejection')
for(const [path,hash]of Object.entries(pins))if(sha(readFileSync(path))!==hash)throw Error('frozen source changed')
if(sha(JSON.stringify(canonical.m))!==canonicalMachineSha256||sha(JSON.stringify(canonical.laws))!==canonicalLawsSha256)throw Error('canonical source mutated')
console.log('CANONICAL_ARTIFACT',JSON.stringify({path:'canonical-six-law.json',sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}))
console.log('POSTFLIGHT',JSON.stringify({unchanged:true,canonicalObligations:12,checked:true,coldChecked:true,proofSearchQueries:0,transportUnits:meter.used,nativeAdmission:false}))
