// Production proveRule only. Never import the direct-emitter research reconstruction harness.
import type {Manifest,MeterBinding,CaseAttempt,LeaseEvent,Snapshot,Verdict} from './contract.ts'
import {assertManifest,assertRoster,assertSnapshot,TraceAudit,digest,halfCap} from './assertions.ts'
export async function runProductionQualification(manifest:Manifest,meter:MeterBinding,traceSink?:(event:LeaseEvent)=>void){
 assertManifest(manifest)
 const [{protocols},{proveRule},{countsDump},{withCountOperationObservation},native,{withLiftedWorkSliceObservation}]=await Promise.all([
  import('../../protocols/ic3syn/models.ts'),import('../../../core/dsl.ts'),import('../../../core/counts.ts'),import('../../../core/count-operation-observation.ts'),import('../../../kernel/kernel.ts'),import('../../../core/count-lifted-budget.ts')])
 const protocol=protocols.find(p=>p.id===manifest.protocolId);if(!protocol)throw Error('protocol identity not found')
 const audit=new TraceAudit(manifest.workKeys,manifest.weightsSha256),cases:CaseAttempt[]=[],events:Record<string,unknown>[]=[],checks:{goal:string,entry:Snapshot,exit?:Snapshot,checked?:boolean,error?:string}[]=[]
 let traceSinkFailed=false
 let active:CaseAttempt|undefined,closed:Record<string,any>|undefined,caller:Record<string,any>|undefined,problemHash:string|undefined,error:string|undefined,nativeAccepted=false
 let generated:readonly {name:string}[]|undefined
 const previous=countsDump.on
 const fail=(reason:string):Verdict=>({status:'FAIL',reason})
 try{
  meter.withWorkAdmissionTrace(event=>{audit.observe(event);if(traceSink)try{traceSink(event)}catch(e){traceSinkFailed=true;throw e}if(active){const ids=new Set(active.start.activeEndpoints.map(e=>e.id));if(!active.events.some(e=>e.kind==='scope-enter')){if(event.kind==='scope-enter'&&event.activeEndpoints.some(e=>e.kind==='scope'&&!ids.has(e.id)))active.events.push(event);else if(event.kind==='start'&&!active.events.some(e=>e.kind==='start'))active.events.push(event)}}},()=>meter.workLedger.withBudget({num:BigInt(manifest.rootGrant.numerator),den:BigInt(manifest.rootGrant.denominator)},()=>{
   countsDump.on=(event:object)=>{const e=event as Record<string,any>;events.push(e);if(e.phase==='candidates'){generated=e.laws;assertRoster(e.laws,manifest.candidateRoster)}if(e.phase==='closed-family'){if(closed)throw Error('multiple native family closures');closed=e}previous?.(event)}
   withLiftedWorkSliceObservation(slice=>{if(active&&slice.kind==='case'){if(active.slice)throw Error('multiple case slices');active.slice={kind:'case',key:slice.key,scopeId:slice.scopeId,rootEpoch:slice.rootEpoch,allocation:{numerator:String(slice.allocation.num),denominator:String(slice.allocation.den)}}}},()=>withCountOperationObservation(event=>{
    if(event.owner!==manifest.halfLaw.name)return
    if(event.phase==='begin'){if(active)throw Error('nested operation identity');active={identity:event,start:meter.workAdmissionSnapshot(),events:[]};cases.push(active)}
    else{if(!active||active.identity.value!==event.value)throw Error('operation end identity mismatch');active.end=meter.workAdmissionSnapshot();active.returned=event.returned;active=undefined}
   },()=>{
    const rule=protocol.make();problemHash=digest(rule.machine);if(problemHash!==manifest.originalMachineSha256)throw Error('original problem changed')
    const work=Number(manifest.searchWorkRaw);if(!Number.isSafeInteger(work)||work<0)throw Error('unsafe original search grant')
    caller=proveRule(rule,protocol.laws(rule),{search:{ms:manifest.wallMs,work}})
    if(!caller.proven||!caller.checked||!closed)return
    assertRoster(closed.laws,manifest.closedRoster)
    const proof=closed.proof as Parameters<typeof native.checkCountedLaws>[2],machine=closed.machine as Parameters<typeof native.checkCountedLaws>[0],laws=closed.laws as Parameters<typeof native.checkCountedLaws>[1]
    const packets=native.countedObligations(machine,laws,proof.instances),names=packets.map(p=>p.goal.name)
    if(packets.length!==2*laws.length||JSON.stringify(Object.keys(proof.certs).sort())!==JSON.stringify([...names].sort()))throw Error('incomplete or extra native packet roster')
    for(const packet of packets){const check={goal:packet.goal.name,entry:meter.workAdmissionSnapshot()} as typeof checks[number];checks.push(check);try{check.checked=native.checkMC(packet.goal.hyps,packet.decls,proof.certs[packet.goal.name]!)}catch(e){check.error=String(e);throw e}finally{check.exit=meter.workAdmissionSnapshot()}if(!check.checked)throw Error('native packet refused: '+packet.goal.name)}
    const check={goal:'checkCountedLaws',entry:meter.workAdmissionSnapshot()} as typeof checks[number];checks.push(check);try{check.checked=native.checkCountedLaws(machine,laws,proof);nativeAccepted=check.checked}catch(e){check.error=String(e);throw e}finally{check.exit=meter.workAdmissionSnapshot()}
   }))
  }))
 }catch(e){error=String(e)}finally{countsDump.on=previous}
 let prefix:Verdict
 try{audit.finish();for(const c of checks){assertSnapshot(c.entry,manifest.workKeys,manifest.weightsSha256);if(!c.entry.rootBaseline)throw Error('native check outside root');if(c.exit)assertSnapshot(c.exit,manifest.workKeys,manifest.weightsSha256)}prefix={status:'PASS',reason:'exact trace F/R/E and counter-vector checks'}}catch(e){prefix=fail(String(e))}
 const c2Emitter=events.some(e=>e.law===manifest.halfLaw.name&&e.stage==='replacement-profile'),c2Composer=events.some(e=>e.law===manifest.halfLaw.name&&typeof e.stage==='string'&&e.stage.startsWith('lemma-transport:'))
 const c2Payload=Boolean(closed?.proof?.certs?.[manifest.halfLaw.name+' @step']?.lemmas?.length)
 let closure:Verdict=error?{status:'UNKNOWN',reason:error}:!caller?.proven||!caller.checked||!closed?{status:'UNKNOWN',reason:'production path did not close'}:!nativeAccepted?fail('independent native family check refused'):!generated?fail('missing production admission roster'):!c2Emitter||!c2Composer||!c2Payload?fail('C2 emitter/composer/accepted-payload evidence missing'):{status:'PASS',reason:'exact production roster, all INIT/STEP packets and checkCountedLaws accepted'}
 for(const op of manifest.operations)if(!cases.some(c=>c.identity.value===op.value&&c.identity.kind===op.kind&&c.returned))closure=fail('required operation missing or incomplete: '+op.value)
 if(prefix.status!=='PASS')closure=prefix
 const half=closure.status==='PASS'?halfCap(cases):{status:closure.status,reason:'no accepted composed family: '+closure.reason} as Verdict
 // Wire-format capture is artifact I/O, outside the production/native-check work window.
 const {captureCountCert}=await import('../../lane-i/rolling-20261111/portable-count-cert.ts')
 const payload=closed&&nativeAccepted?{manifestSha256:digest(manifest),machine:closed.machine,family:closed.laws,proof:{instances:closed.proof.instances,certs:Object.fromEntries(Object.entries(closed.proof.certs).map(([name,cert])=>[name,captureCountCert(cert as Parameters<typeof captureCountCert>[0])]))}}:null
 return{version:'c2-production-gates-v1',manifestSha256:digest(manifest),candidate:manifest.candidate,flags:manifest.flags,problemHash,closure,half,prefix,mechanicalCoverage:{status:'NOT_RUN',reason:'bank trace is not independent M1-M5 physical coverage'},caller:caller?{proven:caller.proven,checked:caller.checked,why:caller.why}:null,error,c2Emitter,c2Composer,c2Payload,generatedRoster:generated?.map(l=>l.name),closedRoster:closed?.laws?.map((l:{name:string})=>l.name),preparedMachineSha256:closed?digest(closed.machine):null,payloadSha256:payload?digest(payload):null,payload,observations:events.map(({phase,stage,law,goal,pass,checked,proposed,status,retained,reason,value})=>({phase,stage,law,goal,pass,checked,proposed,status,retained,reason,value})),artifactSerializationOutsideWindow:true,freshProcessReplay:{status:'NOT_RUN',reason:'prepare-only; native replay must use the landed meter pin'},checks,cases,trace:{...audit.receipt(),completeRawArchive:Boolean(traceSink)&&!traceSinkFailed}}
}
