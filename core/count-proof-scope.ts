// Untrusted premise scopes for counted induction. No verdict is cached: every
// reuse reindexes without search and checks the current machine/family's goals.
import {type C,type Law,type Machine} from './machine.ts'
import {type CountCert,type Goal,type Instances,assumed,checkMC,countedObligations,mcGoal} from '../kernel/kernel.ts'
import {clock,wallAt,withDeadline} from '../kernel/prove.ts'
import {replayCountCertificate} from './count-cert-transport.ts'
import {countedScopeHyps} from './count-scope-hyps.ts'
import {strategyLawKey} from './strategy-premises.ts'
import {checkWall} from './wall.ts'
import {startWork,workLedger} from './work-admission.ts'
import {type WorkAmount,workSub} from './work-amount.ts'
import {workEntries,workJoin,workJSON,workMap,workStrings} from './work-collections.ts'
import {finalCountStepDeferralEnabled} from './count-final-step.ts'

export type CountLawProof = {status?: 'unchecked', instances:Instances,certs:Record<string,CountCert>,premises?:readonly string[]}
export type CountFamilyProof = {instances:Record<string,Instances>,certs:Record<string,CountCert>,premises?:Record<string,readonly string[]>}
type Premise = Readonly<{name:string,key:string}>
export type CheckedReducedContext=Readonly<{kind:'checked-reduced'}>
type CheckedBinding={token:CheckedReducedContext,problem:string,scope:string,context:readonly Premise[],laws:readonly Law[]}
const checkedProofs=new WeakMap<CountLawProof,CheckedBinding>(),checkedTokens=new WeakMap<CheckedReducedContext,CheckedBinding>()
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
const proofStamp=(owner:Premise,premises:readonly Premise[],proof:CountLawProof,sources:readonly Goal[])=>receiptStamp({owner,premises,instances:proof.instances,certs:proof.certs,sources})
// A metered ordinary-data key, not a receipt or authority to accept a proof.
// Scalar workJSON deliberately refuses objects in FULL mode; reuse the exact
// recursive encoder instead of bypassing its start-before-work accounting.
export const countScopeContextKey=(machine:Machine,laws:readonly Law[]):string=>receiptStamp({machine,laws})
export type ScopedCountProof = Readonly<{
 owner:Premise,
 premises:readonly Premise[],
 proof:CountLawProof,
 sources:readonly Goal[],
 unused:readonly string[],
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
  return receiptStamp(machine)===binding.problem&&proofStamp(scoped.owner,scoped.premises,scoped.proof,scoped.sources)===binding.scope
 }catch(error){if(error instanceof TypeError)return false;throw error}
}
const live=(until:number):boolean=>{checkWall('counted premise replay');return clock()<until}
const identity=(law:Law):Premise=>({name:law.name,key:JSON.stringify([law.forall,law.keys,strategyLawKey(law)])})
// Canonical object ordering matters: substitution reconstructs AST objects.
const formulaKey=(holds:C):string=>strategyLawKey({name:'',holds})

// This is proposal metadata, not an authorization. The exact referenced base
// hypotheses (including independent cut slices and the fact rows supplying
// cells to used equal-key rows) identify the family premises. Duplicate
// formulas and duplicate cell suppliers conservatively name every owner.
// Explicit strategy scopes may be supplied, but may not omit referenced laws.
export function scopeCountProof(m:Machine,owner:Law,family:Law[],proof:CountLawProof,until:number):ScopedCountProof|undefined{
 if(!live(until)||!family.includes(owner)||new Set(family.map(l=>l.name)).size!==family.length)return undefined
 const sources:Goal[]=[],used=new Set<string>()
 for(const {goal,decls}of countedObligations(m,family,{[owner.name]:proof.instances},family.indexOf(owner))){
  if(!live(until))return undefined
  const cert=proof.certs[goal.name],expanded=cert&&mcGoal(goal.hyps,decls,cert)
  const refs=expanded&&countedScopeHyps(expanded,cert!)
  if(!expanded||!refs)return undefined
  sources.push(expanded)
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
 const result:ScopedCountProof={owner:identity(owner),premises,proof:{...proof,premises:premises.map(p=>p.name)},sources,unused:family.filter(l=>!names.has(l.name)).map(l=>l.name)}
 const binding=checkedProofs.get(proof)
 return binding&&isCheckedReducedScope({...result,checkedReduced:binding.token},m)?{...result,checkedReduced:binding.token}:result
}

// A changed premise is missing even if its label survives. Unused instantiated
// laws do not pin the proof: remove those tuples before reconstructing the
// target goals. Flag/fact instances outside the candidate family are retained.
export function replayScopedCountProof(m:Machine,family:Law[],scoped:ScopedCountProof,until:number,options:{deferToClosing?:boolean}={}):CountLawProof|undefined{
 return withDeadline(until,()=>{
  if(!live(until)||new Set(family.map(l=>l.name)).size!==family.length)return undefined
  const byName=new Map(family.map(l=>[l.name,l]))
  for(const premise of [scoped.owner,...scoped.premises]){
   const law=byName.get(premise.name)
   if(!law||identity(law).key!==premise.key)return undefined
  }
  const owner=byName.get(scoped.owner.name)!,names=new Set(scoped.premises.map(p=>p.name))
  const deferred=options.deferToClosing===true&&finalCountStepDeferralEnabled()&&scoped.proof.status==='unchecked'
  // The original family names are the source of pruning, not the new family:
  // dropped unused instances must disappear too, while unrelated facts stay.
  const instances={...scoped.proof.instances}
  for(const name of scoped.unused)delete instances[name]
  const problem=deferred?undefined:receiptStamp(m),context=workMap(family,identity,'checked-scope:context-identity')
  const goals=countedObligations(m,family,{[owner.name]:instances},family.indexOf(owner)),certs:Record<string,CountCert>={},sources:Goal[]=[]
  if(goals.length!==scoped.sources.length)return undefined
  for(let i=0;i<goals.length;i++){
   if(!live(until))return undefined
   const {goal,decls}=goals[i]!,cert=scoped.proof.certs[goal.name]
   const to=cert&&mcGoal(goal.hyps,decls,cert),from=scoped.sources[i]!
   const next=to&&replayCountCertificate(from,to,cert!,wallAt())
   if(!next)return undefined
   if(!deferred){receiptStamp(next);if(!checkMC(goal.hyps,decls,next))return undefined}
   if(!live(until))return undefined
   certs[goal.name]=next;sources.push(to!)
  }
  const result:CountLawProof={instances,certs,premises:[...names],...(deferred?{status:'unchecked' as const}:{})}
  const used=new Set([owner.name,...names])
  if(!deferred&&used.size===context.length&&context.every(p=>used.has(p.name))){
   if(receiptStamp(m)!==problem)return undefined
   const token=Object.freeze({kind:'checked-reduced' as const}),binding:CheckedBinding={token,problem:problem!,context,laws:workMap(family,law=>law,'checked-scope:retain-laws'),scope:proofStamp(identity(owner),scoped.premises,result,sources)}
   checkedTokens.set(token,binding);checkedProofs.set(result,binding)
  }
  return result
 })
}
