// Observation only: capture AND final encoding/save are inside observed wall,
// but are not charged proof units. This is not a timing-neutral measurement.
import {createHash} from 'node:crypto'
import type {ReplayDiagnosticEvent} from '../../../core/count-replay-diagnostic.ts'
import {encode} from './io.ts'
export const REPLAY_DIAGNOSTIC_LIMITS={events:16,recordBytes:16384,nodes:2048,depth:24,stringChars:2048,history:64,summaryBytes:4096,identityBytes:4096,memberChars:256,aggregateBytes:2097152} as const
const sha=(s:string)=>createHash('sha256').update(s).digest('hex')
type Limits=Readonly<{recordBytes:number,nodes:number,depth:number,stringChars:number}>
export function boundedReplayJSON(value:unknown,limits:Limits=REPLAY_DIAGNOSTIC_LIMITS,omitRootKeys:readonly string[]=[]){
 const chunks:string[]=[],active=new WeakSet<object>();let bytes=0,work=0,stopped=false,changed=false
 const tick=():boolean=>{if(work>=limits.nodes){changed=true;stopped=true;return false}work++;return true}
 const put=(s:string):boolean=>{const size=Buffer.byteLength(s);if(stopped||bytes+size>limits.recordBytes){stopped=true;return false}chunks.push(s);bytes+=size;return true}
 const text=(s:string):boolean=>{if(s.length>limits.stringChars){changed=true;s=s.slice(0,limits.stringChars)}return put(JSON.stringify(s))}
 const visit=(v:unknown,depth:number):boolean=>{
  if(stopped||!tick())return false
  if(depth>limits.depth){changed=true;stopped=true;return false}
  if(v===null)return put('null')
  if(typeof v==='string')return text(v)
  if(typeof v==='number'){if(!Number.isFinite(v)){changed=true;return text('[NonFinite]')}return put(String(v))}
  if(typeof v==='boolean')return put(String(v))
  if(typeof v!=='object'){changed=true;return text('[Unavailable:'+typeof v+']')}
  if(active.has(v)){changed=true;return text('[Circular]')}
  active.add(v)
  try{
   if(v instanceof Map){
    if(!put('{"$map":['))return false;let first=true
    for(const [key,item]of Map.prototype.entries.call(v)){if(!tick())return false;if(!first&&!put(','))return false;first=false;if(!visit([key,item],depth+1))return false}
    return put(']}')
   }
   if(Array.isArray(v)){
    if(!put('['))return false
    for(let i=0;i<v.length;i++){if(!tick())return false;if(i&&!put(','))return false;const d=Object.getOwnPropertyDescriptor(v,String(i));if(!d||!('value'in d)){changed=true;if(!text('[Unavailable]'))return false}else if(!visit(d.value,depth+1))return false}
    return put(']')
   }
   const proto=Object.getPrototypeOf(v);if(proto!==Object.prototype&&proto!==null){changed=true;return text('[Nonordinary]')}
   if(!put('{'))return false;let first=true
   for(const key in v){
    // Every iteration consumes work, BEFORE any omission (including inherited,
    // undefined and explicitly omitted keys). No unbounded skip-only scan.
    if(!tick())return false
    if(!Object.prototype.hasOwnProperty.call(v,key))continue
    const d=Object.getOwnPropertyDescriptor(v,key)
    if(depth===0&&omitRootKeys.includes(key)||d&&'value'in d&&d.value===undefined)continue
    if(!first&&!put(','))return false;first=false
    if(!text(key)||!put(':'))return false
    if(!d||!('value'in d)){changed=true;if(!text('[Accessor]'))return false}else if(!visit(d.value,depth+1))return false
   }
   return put('}')
  }finally{active.delete(v)}
 }
 try{visit(value,0)}catch{changed=true;stopped=true}
 const serialisation=chunks.join(''),complete=!stopped&&!changed,digest=sha(serialisation)
 return {format:complete?'json':'bounded-json-prefix',serialisation,bytes,nodesVisited:work,workSteps:work,complete,truncated:!complete,replayable:complete,sha256:digest,hashScope:complete?'complete-serialization':'serialized-prefix-only',fullValueSha256:complete?digest:null}
}
const short=(value:unknown,cap=256)=>typeof value==='string'?value.slice(0,cap):null
const integer=(value:unknown)=>typeof value==='number'&&Number.isSafeInteger(value)&&value>=0?value:null
export function replayDiagnosticCollector(identity:unknown){
 // Never retain raw caller identity: even the non-ring section is byte/work
 // bounded. A partial identity is unavailable, not a fabricated source binding.
 const identityCapture=boundedReplayJSON(identity,{...REPLAY_DIAGNOSTIC_LIMITS,recordBytes:REPLAY_DIAGNOSTIC_LIMITS.identityBytes,nodes:512})
 const identityValue=identityCapture.complete?JSON.parse(identityCapture.serialisation):null
 const events:any[]=[],history:any[]=[],members=new Map<string,any>();let observed=0,dropped=0,historyDropped=0,membersDropped=0,captureFailures=0,truncatedValues=0
 const capture=(event:ReplayDiagnosticEvent)=>{
  observed++
  try{
   const context=event.context??{},member=context.member,passId=integer(context.passId)
   const memberIdentityComplete=typeof member==='string'&&member.length<=REPLAY_DIAGNOSTIC_LIMITS.memberChars&&(context.passId===undefined||passId!==null)
   // Long names do NOT join on a shared prefix, and hashing unbounded names is
   // not hidden work. Their exact member identity is explicitly unavailable.
   const key=memberIdentityComplete?JSON.stringify([passId,member]):null
   const brief={kind:short(event.kind),passId,member:short(member),memberIdentityComplete,obligation:short(context.obligation),closingAttempt:integer(context.closingAttempt),route:short(context.route)}
   if(event.kind==='resolver-start'||event.kind==='resolver-result'||event.kind==='fallback-claimed'){
    const snapshot=boundedReplayJSON(event,{...REPLAY_DIAGNOSTIC_LIMITS,recordBytes:4096,nodes:512})
    if(!snapshot.complete)truncatedValues++
    if(history.length===REPLAY_DIAGNOSTIC_LIMITS.history){history.shift();historyDropped++}history.push({...brief,...snapshot})
    if(event.kind!=='fallback-claimed'&&key!==null){
     // Effective controller premises are the UNION, not the returned payload's
     // narrower proposal. Observe only capped prefixes; never scan arbitrary tails.
     const before=Array.isArray(event.premisesBefore)?event.premisesBefore:[]
     const after=Array.isArray(event.effectivePremisesAfter)?event.effectivePremisesAfter:[]
     const left=before.slice(0,64),right=after.slice(0,64)
     const delta=event.result==='repaired'?right.filter(name=>!left.includes(name)):null
     const namesComplete=before.length<=64&&after.length<=64&&[...left,...right].every(x=>typeof x==='string'&&x.length<=256)
     const candidate={...brief,ran:true,lastKind:event.kind,result:short(event.result),premisesAfterMeaning:'controller-effective-union',supplierDelta:delta?.map(name=>short(name))??null,supplierDeltaStatus:delta===null?'not-returned':namesComplete?'complete':'partial-prefix'}
     const summary=boundedReplayJSON(candidate,{...REPLAY_DIAGNOSTIC_LIMITS,recordBytes:REPLAY_DIAGNOSTIC_LIMITS.summaryBytes,nodes:1024,stringChars:256})
     if(!summary.complete)truncatedValues++
     const bounded=summary.complete?JSON.parse(summary.serialisation):{...brief,ran:true,lastKind:event.kind,result:short(event.result),supplierDelta:null,supplierDeltaStatus:'unavailable-byte-bound',boundedDetail:summary}
     if(members.size<REPLAY_DIAGNOSTIC_LIMITS.history||members.has(key))members.set(key,bounded);else membersDropped++
    }
   }
   if(event.kind==='certificate-decline'||event.kind==='scope-decline'||event.kind==='closing-result'){
    // Omit the certificate during the bounded walk, not by spreading every
    // property of a possibly large event before its work limit is applied.
    const snapshot=boundedReplayJSON(event,REPLAY_DIAGNOSTIC_LIMITS,['certificate'])
    const certificate=event.certificate===undefined?null:boundedReplayJSON(event.certificate)
    if(!snapshot.complete||certificate&&!certificate.complete)truncatedValues++
    const cuts=event.cutCounts as Record<string,unknown>|undefined,prefix=event.prefix as Record<string,unknown>|undefined
    if(events.length===REPLAY_DIAGNOSTIC_LIMITS.events){events.shift();dropped++}
    events.push({sequence:observed,...brief,certificateId:integer(event.certificateId),cutCounts:cuts?{frames:integer(cuts.frames),lemmas:integer(cuts.lemmas),monos:integer(cuts.monos),lins:integer(cuts.lins)}:null,prefix:prefix?{source:short(prefix.source,32),target:short(prefix.target,32)}:null,certificate,details:snapshot})
   }
  }catch{captureFailures++}
 }
 const finish=(observerFailures=0)=>{
  const historyComplete=historyDropped===0&&membersDropped===0&&captureFailures===0&&observerFailures===0
  for(const event of events)if(event.member!==null){
   const key=event.memberIdentityComplete?JSON.stringify([event.passId,event.member]):null,known=key===null?undefined:members.get(key)
   event.memberRepair=known??{ran:key!==null&&historyComplete?false:null,status:key===null?'unavailable-member-identity':historyComplete?'not-invoked':'unavailable-history'}
  }
  const result={schema:'count-replay-diagnostic/v1',identity:identityValue,identityCapture,limits:REPLAY_DIAGNOSTIC_LIMITS,observedEvents:observed,droppedEvents:dropped,droppedHistory:historyDropped,droppedMemberSummaries:membersDropped,truncatedValues,captureFailures,observerFailures,complete:identityCapture.complete&&dropped===0&&historyComplete&&truncatedValues===0,aggregateTruncated:false,events,repairHistory:history,memberRepairSummary:[...members.values()],repairAbsenceMeaning:historyComplete?'No matching resolver-start for an EXACT bounded member identity means not invoked during the observed run':'UNKNOWN: observation history incomplete',accounting:{kind:'BOUNDED_OBSERVER_OVERHEAD',chargedToProofUnits:false,includedInObservedWall:true,timingNeutralClaim:false,scopeDeclarationStamping:'Declaration references are retained lazily; receiptStamp eagerly traverses and charges them when minting/validating a checked receipt.'},proofAuthority:false}
  // Check the ACTUAL writer, including escaping, tags and the trailing newline.
  // If the total is too large, discard every optional section, not just rings.
  // All retained pieces above are separately bounded; the fallback is <32KiB.
  try{encode(result,REPLAY_DIAGNOSTIC_LIMITS.aggregateBytes)}catch{
   result.complete=false;result.aggregateTruncated=true
   result.droppedEvents+=events.length;result.droppedHistory+=history.length;result.droppedMemberSummaries+=members.size
   result.events=[];result.repairHistory=[];result.memberRepairSummary=[]
   result.repairAbsenceMeaning='UNKNOWN: aggregate byte bound removed observation records'
   encode(result,REPLAY_DIAGNOSTIC_LIMITS.aggregateBytes)
  }
  return result
 }
 return {capture,finish}
}
