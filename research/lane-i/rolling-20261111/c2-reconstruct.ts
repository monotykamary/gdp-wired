// Full, unrestricted composition from fresh admission. No operation is excluded.
import {createHash} from 'node:crypto'
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {protocols} from '../../protocols/ic3syn/models.ts'
import {countsDump,guardLaws,certFor} from '../../../core/counts.ts'
import {proveRule} from '../../../core/dsl.ts'
import {type Law,type Machine,all,n,same,x} from '../../../core/machine.ts'
import {discoverLiftedCountGuard,discoverLiftedCountOperations} from '../../../core/count-lifted-shape.ts'
import {discoverLiftedCountPrerequisites} from '../../../core/count-lifted-prerequisite.ts'
import {proveLiftedCountFrame,proveLiftedCountInitial} from '../../../core/count-lifted-strategy.ts'
import {proveLiftedCountLoad} from '../../../core/count-lifted-load.ts'
import {proveLiftedCountCopy} from '../../../core/count-lifted-copy.ts'
import {proveLiftedCountIncrement} from '../../../core/count-lifted-increment.ts'
import {proveLiftedCountReplacement} from '../../../core/count-lifted-replacement.ts'
import {composeCountOperationProofs,type FixedOperationProof} from '../../../core/count-case-compose.ts'
import {recordCountStrategyPremises} from '../../../core/count-strategy-premises.ts'
import {checkMC,countedObligations,mcGoal} from '../../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../../kernel/prove.ts'
import {captureCountCert} from './portable-count-cert.ts'
import {certificateSize,mainLeafRows} from './c2-certificate-size.ts'
import {type ClosedFamily,bindClosedFamily,substituteClosedFamily} from './c2-closed-family.ts'
import {proposeRecapturedFamily} from './c2-recapture.ts'
const processStart=performance.now(),closed:ClosedFamily|undefined=process.env.F17_CLOSED_FAMILY?JSON.parse(gunzipSync(readFileSync(process.env.F17_CLOSED_FAMILY)).toString()):undefined
const audits:{label:string,cert:Parameters<typeof certificateSize>[0],packet:ReturnType<typeof countedObligations>[number],instances:Record<string,unknown[]>,family:Law[]}[]=[]
let captured=0
for(const protocol of protocols){
 const rule=protocol.make(),seed=guardLaws(rule.machine),extended={...rule.machine,counts:{...rule.machine.counts,...seed.counts}}
 if(!seed.laws.some(law=>discoverLiftedCountGuard(extended,law,seed.laws)))continue
 const previous=countsDump.on,stop={}
 countsDump.on=(event:object)=>{
  const value=event as {phase?:string,machine:Machine,laws:Law[]};if(value.phase!=='candidates')return
  withWall(performance.now()+600000,()=>counted(fullRate,()=>{
   if(closed&&process.env.F17_RECAPTURE==='1'){
    if(!process.argv[2])throw Error('recapture output required')
    const proposal=proposeRecapturedFamily(value.machine,value.laws,closed)
    mkdirSync(process.argv[2],{recursive:true});writeFileSync(process.argv[2]+'/recapture-candidate.json',JSON.stringify(proposal)+'\n')
    console.log('C2_RECAPTURE_CANDIDATE '+JSON.stringify({laws:proposal.family.length,sha256:createHash('sha256').update(JSON.stringify(proposal)).digest('hex'),nativeChecked:false,leanClearance:false}))
    return
   }
   if(closed){const bound=bindClosedFamily(value.machine,value.laws,closed);value.machine=closed.machine;value.laws=bound}
   const strategyStart=performance.now(),family=value.laws,law=family.find(law=>discoverLiftedCountPrerequisites(value.machine,law,family).length)
   if(!law)throw Error('no eligible target')
   const shape=discoverLiftedCountGuard(value.machine,law,family)!,plan=discoverLiftedCountOperations(value.machine,shape)!,cases:FixedOperationProof[]=[],events:Record<string,unknown>[]=[],index=family.indexOf(law),start=fullWork(),until=clock()+12000
   const request:Parameters<typeof proveLiftedCountReplacement>[4]=(goal,decls)=>certFor(goal,decls,false,0,()=>true)
   // Fail early at the new case; do not repeat six known cases on every failed prototype.
   const rank=(kind:string)=>kind==='threshold-replace'?0:kind==='frame-or-phase'?1:kind==='load'?2:kind==='copy'?3:4
   for(const operation of [...plan].sort((a,b)=>rank(a.kind)-rank(b.kind)||a.value-b.value)){
    const fixed={...value.machine,assume:all(...(value.machine.assume?[value.machine.assume]:[]),same(x(operation.name),n(operation.value)))},before=fullWork(),caseWall=performance.now(),observed:Record<string,unknown>[]=[]
    const emit=operation.kind==='threshold-replace'?proveLiftedCountReplacement:operation.kind==='load'?proveLiftedCountLoad:operation.kind==='copy'?proveLiftedCountCopy:proveLiftedCountIncrement
    const proof=operation.kind==='frame-or-phase'?proveLiftedCountFrame(fixed,family,law,Math.min(until,clock()+500),request,event=>observed.push(event)):emit(fixed,family,law,Math.min(until,clock()+2000),request,event=>observed.push(event),{deferToComposition:true,deferIntermediateChecks:process.env.GDP_COUNT_DEFER_CHECKS==='1',slicedLemmas:process.env.GDP_COUNT_C2_LEMMAS==='1'})
    const units=(fullWork()-before)/fullRate,wallMs=performance.now()-caseWall
    events.push({stage:'case',value:operation.value,kind:operation.kind,checked:!!proof,units,wallMs,events:operation.kind==='threshold-replace'?observed:undefined});console.log('LIFTED_FULL_PROGRESS '+JSON.stringify({value:operation.value,kind:operation.kind,proposed:!!proof,unchecked:proof?.status==='unchecked',units,wallMs}))
    if(!proof||units>2000){console.log('LIFTED_FULL_COMPOSITION '+JSON.stringify({lawCount:family.length,events,composed:false,checkedFull:false,units:(fullWork()-start)/fullRate}));process.exitCode=1;return}
    const packet=countedObligations(fixed,family,{[law.name]:proof.instances},index).at(-1)!
    audits.push({label:'operation-'+operation.value,cert:proof.certs[packet.goal.name]!,packet,instances:proof.instances,family})
    cases.push({value:operation.value,proof})
   }
   const initialWork=fullWork(),initialWall=performance.now(),initial=proveLiftedCountInitial(value.machine,family,law,cases[0]!.proof.instances,until,request)
   events.push({stage:'initial',units:(fullWork()-initialWork)/fullRate,wallMs:performance.now()-initialWall})
   const composeWork=fullWork(),composeWall=performance.now(),composed=initial&&composeCountOperationProofs({original:value.machine,machine:value.machine,shape:shape.countShape,restrictions:[],inputCounts:{}},family,law,cases,until,request,(stage,value)=>{events.push({stage,value});console.log('LIFTED_FULL_PROGRESS '+JSON.stringify({stage,value}))},{initial,trace:event=>events.push(event),slicedLemmas:process.env.GDP_COUNT_C2_LEMMAS==='1'})
   events.push({stage:'composition',units:(fullWork()-composeWork)/fullRate,wallMs:performance.now()-composeWall})
   const proof=composed&&recordCountStrategyPremises(family,composed),strategyWallMs=performance.now()-strategyStart
   if(proof?.status)throw Error('unchecked composition escaped its final checker')
   const packets=proof&&countedObligations(value.machine,family,{[law.name]:proof.instances},index),checkedFull=!!proof&&!!packets&&packets.every(packet=>!!proof.certs[packet.goal.name]) // composeCountOperationProofs performs the full native INIT/STEP checks
   if(checkedFull)for(const packet of packets!)audits.push({label:packet.goal.name.endsWith('@step')?'composed-step':'composed-initial',cert:proof!.certs[packet.goal.name]!,packet,instances:proof!.instances,family})
   const emptyRejected=checkedFull&&packets!.every(packet=>!checkMC(packet.goal.hyps,packet.decls,{...proof!.certs[packet.goal.name]!,tree:{leaf:[]}}))
   const portable=proof&&Object.fromEntries(Object.entries(proof.certs).map(([name,cert])=>[name,captureCountCert(cert)]))
   const receipt={format:'unrestricted-lifted-composition-v1',machine:value.machine,family,target:index,instances:proof?.instances,premises:proof?.premises,certificates:portable}
   if(process.argv[2]&&checkedFull){
    mkdirSync(process.argv[2],{recursive:true});writeFileSync(process.argv[2]+'/proof.json',JSON.stringify(receipt)+'\n')
    if(closed)writeFileSync(process.argv[2]+'/closed-family.json',JSON.stringify(substituteClosedFamily(closed,law,proof!))+'\n')
   }
   console.log('LIFTED_FULL_COMPOSITION '+JSON.stringify({lawCount:family.length,strategyWallMs,events,initial:!!initial,composed:!!proof,checkedFull,emptyRejected,premises:proof?.premises,units:(fullWork()-start)/fullRate,receiptSha256:portable?createHash('sha256').update(JSON.stringify(receipt)).digest('hex'):null,operationCap:2000,leafCap:500,calibratedW:false}))
   if(!checkedFull||!emptyRejected)process.exitCode=1
  },true))
  captured++;throw stop
 }
 try{proveRule(rule,protocol.laws(rule),{search:{ms:600000}})}catch(error){if(error!==stop)throw error}finally{countsDump.on=previous}
}
if(captured!==1)throw Error('missing full admission')

for(const audit of audits){const wall=performance.now(),size=certificateSize(audit.cert),instances=Object.fromEntries(Object.entries(audit.instances).map(([name,terms])=>{const law=audit.family.find(l=>l.name===name),arity=law?.forall?1+(law.keys?.length??0):0;return [name,{terms:terms.length,arity,tuples:arity?terms.length/arity:0}]}));console.log('F17_CERT '+JSON.stringify({label:audit.label,...size,instances,sourceHypotheses:audit.packet.goal.hyps.length,countedHypotheses:mcGoal(audit.packet.goal.hyps,audit.packet.decls,audit.cert)?.hyps.length,...(process.env.F17_CONTEXTS==='1'?{mainLeafRows:mainLeafRows(audit.cert,audit.packet)}:{}),auditWallMs:performance.now()-wall}))}
console.log('F17_PROCESS '+JSON.stringify({wallMs:performance.now()-processStart}))
