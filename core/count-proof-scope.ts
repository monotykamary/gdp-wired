// Untrusted premise scopes for counted induction. No verdict is cached: every
// reuse reindexes without search and checks the current machine/family's goals.
import {type C,type Law,type Machine} from './machine.ts'
import {type CountCert,type Goal,type Instances,type CountDecl,assumed,checkMC,countedObligations,mcGoal} from '../kernel/kernel.ts'
import {clock,wallAt,withDeadline} from '../kernel/prove.ts'
import {countedCertificateHyps,replayCountCertificate} from './count-cert-transport.ts'
import {countedScopeHyps} from './count-scope-hyps.ts'
import {strategyLawKey} from './strategy-premises.ts'
import {checkWall} from './wall.ts'
import {startWork,workLedger} from './work-admission.ts'
import {type WorkAmount,workSub} from './work-amount.ts'
import {workEntries,workJoin,workJSON,workMap,workStrings} from './work-collections.ts'
import {finalCountStepDeferralEnabled} from './count-final-step.ts'
import {countsForReads} from './count-facts.ts'
import {countReplayDiagnostic,emitReplayDiagnostic,replayCertificateId,withReplayDiagnosticContext,type ReplayDiagnosticContext} from './count-replay-diagnostic.ts'

export type CountLawProof = {status?: 'unchecked', instances:Instances,certs:Record<string,CountCert>,premises?:readonly string[]}
export type CountFamilyProof = {instances:Record<string,Instances>,certs:Record<string,CountCert>,premises?:Record<string,readonly string[]>}
type Premise = Readonly<{name:string,key:string}>
export type CheckedReducedContext=Readonly<{kind:'checked-reduced'}>
type CheckedBinding={token:CheckedReducedContext,problem:string,scope:string,context:readonly Premise[],laws:readonly Law[]}
const checkedProofs=new WeakMap<CountLawProof,CheckedBinding>(),checkedTokens=new WeakMap<CheckedReducedContext,CheckedBinding>()
// Detached diagnostic containers, not a view of authoritative bookkeeping.
// Public token/law graph associations remain references; the private binding,
// context entries and law collection are never exposed or frozen by observing.
export const snapshotCountScopeBinding = (object:object):Readonly<CheckedBinding>|undefined => {
 const binding=checkedProofs.get(object as CountLawProof)??checkedTokens.get(object as CheckedReducedContext)
 if(!binding)return undefined
 return Object.freeze({token:binding.token,problem:binding.problem,scope:binding.scope,
  context:Object.freeze(binding.context.map(p=>Object.freeze({name:p.name,key:p.key}))),
  laws:Object.freeze(binding.laws.slice())})
}
let scopeIdentityObserver:((work:WorkAmount)=>void)|undefined
export function withCountScopeIdentityObservation<T>(observe:(work:WorkAmount)=>void,run:()=>T):T{
 const previous=scopeIdentityObserver;scopeIdentityObserver=observe
 try{return run()}finally{scopeIdentityObserver=previous}
}
// Ordinary owned data only. All recursive reads and string materialization are
// funded before work, and the stamp changes on certificate/context mutation.
function receiptStamp(value:unknown):string{
 const active=new WeakSet<object>()
 const visit=(v:unknown):string=>{
  checkWall('checked reduced scope identity');startWork('ticks',1,'checked reduced scope identity')
  if(v===undefined)return 'u'
  if(v===null||typeof v==='string'||typeof v==='boolean'||typeof v==='number'){if(typeof v==='number'&&!Number.isFinite(v))throw new TypeError('nonfinite scope identity');return workJSON(v,'checked-scope:scalar')!}
  if(typeof v!=='object'||active.has(v))throw new TypeError('nonordinary scope identity')
  const prototype=Object.getPrototypeOf(v);if(prototype!==Object.prototype&&prototype!==null&&!Array.isArray(v))throw new TypeError('nonordinary scope identity')
  active.add(v);const fields=new Map<string,unknown>(),keys:string[]=[],parts:string[]=[]
  for(const [key,value]of workEntries(v,'checked-scope:fields')){startWork('ticks',1,'checked-scope:copy-field');fields.set(key,value);keys.push(key)}
  workStrings(keys,'checked-scope:keys')
  if(Array.isArray(v))parts.push(workJSON(v.length,'checked-scope:array-length')!)
  for(const key of keys){startWork('ticks',1,'checked-scope:field');parts.push(workJoin([workJSON(key,'checked-scope:key')!,visit(fields.get(key))],':','checked-scope:pair'))}
  active.delete(v);return workJoin([Array.isArray(v)?'array[':'object{',workJoin(parts,',','checked-scope:members'),Array.isArray(v)?']':'}'],'','checked-scope:object')
 }
 const before=scopeIdentityObserver&&workLedger.actual()
 try{return visit(value)}finally{if(before)scopeIdentityObserver?.(workSub(workLedger.actual(),before))}
}
const proofStamp=(owner:Premise,premises:readonly Premise[],proof:CountLawProof,sources:readonly Goal[],sourceDecls?:readonly CountDecl[][])=>receiptStamp({owner,premises,instances:proof.instances,certs:proof.certs,sources,sourceDecls})
// A metered ordinary-data key, not a receipt or authority to accept a proof.
// Scalar workJSON deliberately refuses objects in FULL mode; reuse the exact
// recursive encoder instead of bypassing its start-before-work accounting.
export const countScopeContextKey=(machine:Machine,laws:readonly Law[]):string=>receiptStamp({machine,laws})
export type ScopedCountProof = Readonly<{
 owner:Premise,
 premises:readonly Premise[],
 proof:CountLawProof,
 sources:readonly Goal[],
 // Original obligation declarations, retained without recomputation. Cut counts
 // are reconstructed lazily only when a cut-bearing payload is replayed. These
 // references ARE traversed eagerly by the metered receipt stamp at mint/check;
 // retaining references does not claim zero hashing or accounting overhead.
 sourceDecls?:readonly CountDecl[][],
 unused:readonly string[],
 // Dependency metadata only. Unresolved captures retain the original instances;
 // resolved means a native reduced receipt or one full supplier reconstruction.
 suppliers?:'unresolved'|'resolved',
 // Observed checking/replay cost in clock units; scheduling only, never authority.
 checkWork?:number,
 // Opaque provenance, not a serializable or caller-asserted checked flag.
 checkedReduced?:CheckedReducedContext,
}>
export function isCheckedReducedScope(scoped:ScopedCountProof,machine:Machine,currentLaws?:readonly Law[]):boolean{
 const binding=scoped.checkedReduced&&checkedTokens.get(scoped.checkedReduced)
 if(!binding||scoped.proof.status==='unchecked')return false
 const names=new Map<string,string>();for(const list of [[scoped.owner],scoped.premises])for(const p of list){startWork('ticks',1,'checked-scope:context');const old=names.get(p.name);if(old!==undefined&&old!==p.key)return false;names.set(p.name,p.key)}
 if(names.size!==binding.context.length)return false
 for(const p of binding.context){startWork('ticks',1,'checked-scope:context');if(names.get(p.name)!==p.key)return false}
 try{
  for(let i=0;i<binding.laws.length;i++){startWork('ticks',1,'checked-scope:current-law');if(identity(binding.laws[i]!).key!==binding.context[i]!.key)return false}
  if(currentLaws){const now=new Map<string,string>();for(const law of currentLaws){startWork('ticks',1,'checked-scope:provided-law');if(now.has(law.name))return false;now.set(law.name,identity(law).key)}for(const p of binding.context){startWork('ticks',1,'checked-scope:provided-context');if(now.get(p.name)!==p.key)return false}}
  return receiptStamp(machine)===binding.problem&&proofStamp(scoped.owner,scoped.premises,scoped.proof,scoped.sources,scoped.sourceDecls)===binding.scope
 }catch(error){if(error instanceof TypeError)return false;throw error}
}
const live=(until:number):boolean=>{checkWall('counted premise replay');return clock()<until}
const identity=(law:Law):Premise=>({name:law.name,key:JSON.stringify([law.forall,law.keys,strategyLawKey(law)])})
// Canonical object ordering matters: substitution reconstructs AST objects.
const formulaKey=(holds:C):string=>strategyLawKey({name:'',holds})

// This is proposal metadata, not an authorization. The exact referenced base
// hypotheses (including every independent cut's source slice) identify the
// family premises, exactly as at 9eb. Generated suppliers are resolved only
// after an actual closing transport decline. Duplicate formulas name every owner.
// Explicit strategy scopes may be supplied, but may not omit referenced laws.
export function scopeCountProof(m:Machine,owner:Law,family:Law[],proof:CountLawProof,until:number):ScopedCountProof|undefined{
 return captureScope(m,owner,family,proof,until,countedCertificateHyps)
}
// Offered and inferred scopes share one scan; the inferred proof still omits
// the offered status/declaration and receives no borrowed checked receipt.
export function scopeCountProofPair(m:Machine,owner:Law,family:Law[],proof:CountLawProof,until:number):{offered?:ScopedCountProof,inferred?:ScopedCountProof}{
 let inferred:ScopedCountProof|undefined
 const offered=captureScope(m,owner,family,proof,until,countedCertificateHyps,scope=>{inferred=scope})
 return {offered,inferred}
}
function captureScope(m:Machine,owner:Law,family:Law[],proof:CountLawProof,until:number,refsOf:typeof countedCertificateHyps,onInferred?:(scope:ScopedCountProof)=>void):ScopedCountProof|undefined{
 if(!live(until)||!family.includes(owner)||new Set(family.map(l=>l.name)).size!==family.length)return undefined
 const sources:Goal[]=[],sourceDecls:CountDecl[][]=[],used=new Set<string>()
 for(const {goal,decls}of countedObligations(m,family,{[owner.name]:proof.instances},family.indexOf(owner))){
  if(!live(until))return undefined
  const cert=proof.certs[goal.name],expanded=cert&&mcGoal(goal.hyps,decls,cert)
  const refs=expanded&&refsOf(expanded,cert!)
  if(!expanded||!refs)return undefined
  sources.push(expanded);sourceDecls.push(decls)
  for(const index of refs){
   if(!Number.isSafeInteger(index)||index<0||index>=expanded.hyps.length)return undefined
   if(index<goal.hyps.length)used.add(formulaKey(goal.hyps[index]!))
  }
 }
 const actual=family.filter(l=>assumed([l],proof.instances).some(h=>used.has(formulaKey(h))))
 const declared=proof.premises===undefined?actual.map(l=>l.name):[...proof.premises]
 const names=new Set(declared),available=new Set(family.map(l=>l.name))
 if(names.size!==declared.length||declared.some(name=>!available.has(name))||actual.some(l=>!names.has(l.name)))return undefined
 const premises=family.filter(l=>names.has(l.name)).map(identity)
 if(!live(until))return undefined
 const result:ScopedCountProof={owner:identity(owner),premises,proof:{...proof,premises:premises.map(p=>p.name)},sources,sourceDecls,unused:family.filter(l=>!names.has(l.name)).map(l=>l.name),suppliers:'unresolved'}
 if(onInferred)onInferred({...result,premises:actual.map(identity),proof:{instances:proof.instances,certs:proof.certs,premises:actual.map(l=>l.name)},unused:family.filter(l=>!actual.includes(l)).map(l=>l.name)})
 const binding=checkedProofs.get(proof)
 return binding&&isCheckedReducedScope({...result,checkedReduced:binding.token},m)?{...result,checkedReduced:binding.token,suppliers:'resolved'}:result
}

// Cold path only: preserve every old premise and every original instance, add
// the complete generalized supplier closure, and remove no source certificate.
// Resolution is metadata, never a checked-reduced/native-success receipt.
export function resolveCountScopeSuppliers(m:Machine,family:Law[],scoped:ScopedCountProof,until:number):ScopedCountProof|undefined{
 if(scoped.suppliers==='resolved'||!live(until))return undefined
 const owner=family.find(l=>l.name===scoped.owner.name)
 if(!owner||identity(owner).key!==scoped.owner.key)return undefined
 for(const premise of scoped.premises){
  startWork('ticks',1,'count supplier old premise')
  const law=family.find(l=>l.name===premise.name)
  if(!law||identity(law).key!==premise.key)return undefined
 }
 const inferred=captureScope(m,owner,family,{instances:scoped.proof.instances,certs:scoped.proof.certs},until,countedScopeHyps)
 if(!inferred||inferred.sources.length!==scoped.sources.length)return undefined
 // A changed source context cannot reattribute rows of the retained proof.
 for(let i=0;i<scoped.sources.length;i++){
  if(!live(until)||receiptStamp(inferred.sources[i])!==receiptStamp(scoped.sources[i]))return undefined
 }
 const names=new Set([...scoped.premises,...inferred.premises].map(p=>p.name)),premises=family.filter(l=>names.has(l.name)).map(identity)
 const {checkedReduced,...rest}=scoped;void checkedReduced
 return {...rest,premises,proof:{...scoped.proof,status:'unchecked',premises:premises.map(p=>p.name)},unused:family.filter(l=>!names.has(l.name)).map(l=>l.name),suppliers:'resolved'}
}

// A changed premise is missing even if its label survives. Unused instantiated
// laws do not pin the proof: remove those tuples before reconstructing the
// target goals. Flag/fact instances outside the candidate family are retained.
export type CountReplayDecline=Readonly<{
 case:1|2|3|4|5|6|7,
 reason:string,
 member:string,
 obligation?:string,
 premise?:string,
 expected?:number,
 actual?:number,
}>
export function replayScopedCountProof(m:Machine,family:Law[],scoped:ScopedCountProof,until:number,options:{deferToClosing?:boolean,onDecline?:(decline:CountReplayDecline)=>void,onTransportDecline?:(obligation:string)=>void,diagnostic?:ReplayDiagnosticContext}={}):CountLawProof|undefined{
 const decline=(which:CountReplayDecline['case'],reason:string,detail:Partial<Pick<CountReplayDecline,'obligation'|'premise'|'expected'|'actual'>>={}):undefined=>{
  options.onDecline?.({case:which,reason,member:scoped.owner.name,...detail})
  if(countReplayDiagnostic.on){const certificate=detail.obligation?scoped.proof.certs[detail.obligation]:undefined;emitReplayDiagnostic({kind:'scope-decline',context:{...options.diagnostic,member:scoped.owner.name,obligation:detail.obligation},case:which,reason,certificateId:certificate&&replayCertificateId(certificate),certificate,owner:scoped.owner,premises:scoped.premises,suppliers:scoped.suppliers,targetFamily:family.map(law=>law.name)})}
  return undefined
 }
 return withReplayDiagnosticContext({...options.diagnostic,member:scoped.owner.name},()=>withDeadline(until,()=>{
  if(!live(until))return decline(7,'deadline')
  if(new Set(family.map(l=>l.name)).size!==family.length)return decline(1,'duplicate-family-name')
  const byName=new Map(family.map(l=>[l.name,l]))
  for(const premise of [scoped.owner,...scoped.premises]){
   const law=byName.get(premise.name)
   if(!law)return decline(2,'missing-premise',{premise:premise.name})
   if(identity(law).key!==premise.key)return decline(2,'premise-identity-changed',{premise:premise.name})
  }
  const owner=byName.get(scoped.owner.name)!,names=new Set(scoped.premises.map(p=>p.name))
  const deferred=options.deferToClosing===true&&finalCountStepDeferralEnabled()&&scoped.proof.status==='unchecked'
  // Preserve the original source-context pruning and the native checker.
  const instances={...scoped.proof.instances}
  for(const name of scoped.unused)delete instances[name]
  const problem=deferred?undefined:receiptStamp(m),context=workMap(family,identity,'checked-scope:context-identity')
  const goals=countedObligations(m,family,{[owner.name]:instances},family.indexOf(owner)),certs:Record<string,CountCert>={},sources:Goal[]=[]
  if(goals.length!==scoped.sources.length)return decline(3,'obligation-count-mismatch',{expected:scoped.sources.length,actual:goals.length})
  for(let i=0;i<goals.length;i++){
   const {goal,decls}=goals[i]!,obligation=goal.name
   if(!live(until))return decline(7,'deadline',{obligation})
   const cert=scoped.proof.certs[obligation]
   if(!cert)return decline(4,'missing-certificate',{obligation})
   const to=mcGoal(goal.hyps,decls,cert),from=scoped.sources[i]!
   if(!to)return decline(4,'goal-expansion-declined',{obligation})
   const cutBearing=!!(cert.frames?.length||cert.monos?.length||cert.lins?.length)
   const fromCounts=cutBearing&&scoped.sourceDecls?.[i]?countsForReads(scoped.sourceDecls[i]!,cert.reads):undefined
   const toCounts=cutBearing?countsForReads(decls,cert.reads):undefined
   const native=cutBearing&&fromCounts&&toCounts?{from:{counts:fromCounts},to:{counts:toCounts}}:undefined
   const next=replayCountCertificate(from,to,cert,wallAt(),{rethrowBudgetExpired:true,native,diagnostic:{...options.diagnostic,member:scoped.owner.name,obligation}})
   if(!next){
    // Only an actual transport refusal can request K's lazy supplier repair.
    // Missing expansions and original hard stops retain their distinct paths.
    if(live(until))options.onTransportDecline?.(obligation)
    return decline(5,'certificate-transport-declined',{obligation})
   }
   if(!deferred){receiptStamp(next);if(!workLedger.withCapacityRefusalBoundary(()=>checkMC(goal.hyps,decls,next)))return decline(6,'native-check-failed',{obligation})}
   if(!live(until))return decline(7,'deadline',{obligation})
   certs[obligation]=next;sources.push(to)
  }
  const result:CountLawProof={instances,certs,premises:[...names],...(deferred?{status:'unchecked' as const}:{})}
  const used=new Set([owner.name,...names])
  if(!deferred&&used.size===context.length&&context.every(p=>used.has(p.name))){
   if(receiptStamp(m)!==problem)return decline(2,'machine-identity-changed')
   const token=Object.freeze({kind:'checked-reduced' as const}),binding:CheckedBinding={token,problem:problem!,context,laws:workMap(family,law=>law,'checked-scope:retain-laws'),scope:proofStamp(identity(owner),scoped.premises,result,sources,goals.map(({decls})=>decls))}
   checkedTokens.set(token,binding);checkedProofs.set(result,binding)
  }
  return result
 }))
}
