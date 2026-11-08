// Isolated complete-law emission measurement. Calls the same untrusted emitter
// as counts.ts:finish, but does not claim a checked proof of the other laws.
import {readFileSync} from 'node:fs'
import {type Law,type Machine} from '../../core/machine.ts'
import {certFor} from '../../core/counts.ts'
import {proveFocusedCounts} from '../../core/count-focus-proof.ts'
import {proofOrigins,proposeLemmaCuts} from '../../core/lemma-cuts.ts'
import {type CountCert,countedObligations,checkMC,mcGoal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {costMeter,costSpan} from './cost-meter.ts'
const {m,laws}=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {m:Machine,laws:Law[]}
const index=laws.findIndex(l=>l.name.startsWith('Inv1758')),law=laws[index]!
if(!law)throw new Error('missing law')
const enabled=process.env.GDP_COUNT_LEMMA_CUTS==='1',start=performance.now(),end=start+60000,work=fullWork()
proofOrigins.enabled=enabled
const emissions:Record<string,unknown>[]=[],trace:Record<string,unknown>[]=[]
let proofMs=0,emissionMs=0,checkMs=0,proposerCalls=0,acceptedCuts=0,fallback=false
const result=withWall(end,()=>counted(fullRate,()=>{
 const before=performance.now(),proof=proveFocusedCounts(m,laws,law,{},clock()+5000,(goal,decls)=>certFor(goal,decls,true,1000),e=>trace.push(e))
 proofMs=performance.now()-before
 if(!proof)return {proven:false,checked:false}
 const packets=countedObligations(m,laws,{[law.name]:proof.instances},index),proposed:Record<string,CountCert>={...proof.certs}
 const emissionStart=performance.now()
 if(enabled)for(const {goal,decls}of packets){
  if(performance.now()>=end)break
  const cert=proof.certs[goal.name],expanded=cert&&mcGoal(goal.hyps,decls,cert)
  if(!cert||cert.lemmas?.length||!expanded)continue
  proposerCalls++
  const shared=costSpan('construction','lemma-emission',()=>proposeLemmaCuts(expanded,cert.tree,{until:end}))
  emissions.push({goal:goal.name,proposed:!!shared,...(shared?{stats:shared.stats}:{})})
  if(shared)proposed[goal.name]={...cert,tree:shared.tree,lemmas:shared.lemmas}
 }
 emissionMs=performance.now()-emissionStart
 const verify=(certs:Record<string,CountCert>)=>packets.every(p=>!!certs[p.goal.name]&&checkMC(p.goal.hyps,p.decls,certs[p.goal.name]!))
 const checkStart=performance.now()
 let checked=verify(proposed)
 if(!checked&&enabled){fallback=true;checked=verify(proof.certs)}
 if(checked&&!fallback)acceptedCuts=Object.values(proposed).reduce((n,c)=>n+(c.lemmas?.length??0),0)
 checkMs=performance.now()-checkStart
 return {proven:true,checked}
},true))
console.log(JSON.stringify({law:law.name,enabled,...result,wallMs:performance.now()-start,countedMs:(fullWork()-work)/fullRate,proofMs,emissionMs,checkMs,proposerCalls,acceptedCuts,fallback,emissions,phases:costMeter.snapshot().phases,sites:costMeter.snapshot().sites,tail:trace.slice(-8)}))
if(!result.proven||!result.checked)process.exitCode=1
