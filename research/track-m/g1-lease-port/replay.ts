// Fresh-process native replay of one joint generated-law family certificate.
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {type Law,type Machine} from '../../../core/machine.ts'
import {type Instances,checkCountedLaws,checkMC,countedObligations} from '../../../kernel/kernel.ts'
import {type PortableCountCert,restoreCountCert} from '../../lane-i/rolling-20261111/portable-count-cert.ts'
import {workAmount} from '../../../core/work-amount.ts'
import {workLedger,workAdmissionSnapshot} from '../../../core/work-admission.ts'
// A separate validation grant, not a production budget or a same-root retry.
workLedger.withBudget(workAmount(3_000_000_000n),()=>{
const file=process.argv[2];if(!file)throw Error('expected a closed-family proof file')
const text=readFileSync(file,'utf8').trim(),data=JSON.parse(text) as {machine:Machine,family:Law[],proof:{instances:Record<string,Instances>,certs:Record<string,PortableCountCert>}}
const certs=Object.fromEntries(Object.entries(data.proof.certs).map(([name,cert])=>[name,restoreCountCert(cert)])),packets=countedObligations(data.machine,data.family,data.proof.instances)
if(data.family.length!==19||packets.length!==38)throw Error('incomplete family goal coverage')
const familyOnly=process.argv.includes('--family-only'),rejected=familyOnly?[]:packets.filter(packet=>!certs[packet.goal.name]||!checkMC(packet.goal.hyps,packet.decls,certs[packet.goal.name]!)).map(packet=>packet.goal.name)
const sha256=createHash('sha256').update(text).digest('hex');if(sha256!=='95321d6ef8303cdef66dbb376e1ba9639cbf9c8b2f7768324570ab2133968a8e')throw Error('unexpected paired family hash');const familyChecked=checkCountedLaws(data.machine,data.family,{instances:data.proof.instances,certs})
console.log('CLOSED_FAMILY_REPLAY '+JSON.stringify({checked:!familyOnly&&!rejected.length,laws:data.family.length,goals:packets.length,sha256,rejected,skippedPackets:familyOnly}))
console.log('CLOSED_FAMILY_NATIVE '+JSON.stringify({checked:familyChecked,checker:'checkCountedLaws',laws:data.family.length,goals:packets.length,sha256}))
if(rejected.length||!familyChecked)process.exitCode=1
if(!rejected.length&&familyChecked&&process.argv.includes('--mutations')){
 const step=packets.filter(packet=>packet.goal.name.endsWith('@step'))
 const refuses=(kind:'empty'|'witnesses'|'cuts')=>{
  let tested=0
  for(const packet of step){const cert=certs[packet.goal.name]!
   if(kind==='witnesses'&&!cert.insts.length||kind==='cuts'&&![cert.frames,cert.monos,cert.lins,cert.lemmas].some(list=>list?.length))continue
   tested++
   const mutant=kind==='empty'?{...cert,tree:{leaf:[]}}:kind==='witnesses'?{...cert,insts:[]}:{...cert,frames:[],monos:[],lins:[],lemmas:[]}
   if(!checkMC(packet.goal.hyps,packet.decls,mutant))return {rejected:true,tested,goal:packet.goal.name}
  }
  return {rejected:false,tested}
 }
 const first=packets.find(packet=>certs[packet.goal.name]!.insts.length),collision=data.machine.params[0]??data.machine.inputs[0]??Object.keys(data.machine.state)[0]
 const freshness=!!first&&!!collision&&!checkCountedLaws(data.machine,data.family,{instances:data.proof.instances,certs:{...certs,[first.goal.name]:{...certs[first.goal.name]!,insts:certs[first.goal.name]!.insts.map((inst,index)=>index?inst:{...inst,wit:collision})}}})
 const mutations={emptyTree:refuses('empty'),missingWitnesses:refuses('witnesses'),missingCuts:refuses('cuts'),witnessFreshness:{rejected:freshness,tested:first&&collision?1:0}}
 console.log('CLOSED_FAMILY_MUTATIONS '+JSON.stringify(mutations))
 if(!Object.values(mutations).every(result=>result.rejected))process.exitCode=1
}

console.log('NATIVE_LEASE '+JSON.stringify(workAdmissionSnapshot()))
})
