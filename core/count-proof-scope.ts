// Untrusted premise scopes for counted induction. No verdict is cached: every
// reuse reindexes without search and checks the current machine/family's goals.
import {type C,type Law,type Machine} from './machine.ts'
import {type CountCert,type Goal,type Instances,assumed,checkMC,countedObligations,mcGoal} from '../kernel/kernel.ts'
import {clock,wallAt,withDeadline} from '../kernel/prove.ts'
import {countedCertificateHyps,replayCountCertificate} from './count-cert-transport.ts'
import {strategyLawKey} from './strategy-premises.ts'
import {checkWall} from './wall.ts'
import {finalCountStepDeferralEnabled} from './count-final-step.ts'

export type CountLawProof = {status?: 'unchecked', instances:Instances,certs:Record<string,CountCert>,premises?:readonly string[]}
export type CountFamilyProof = {instances:Record<string,Instances>,certs:Record<string,CountCert>,premises?:Record<string,readonly string[]>}
type Premise = Readonly<{name:string,key:string}>
export type ScopedCountProof = Readonly<{
 owner:Premise,
 premises:readonly Premise[],
 proof:CountLawProof,
 sources:readonly Goal[],
 unused:readonly string[],
}>
const live=(until:number):boolean=>{checkWall('counted premise replay');return clock()<until}
const identity=(law:Law):Premise=>({name:law.name,key:JSON.stringify([law.forall,law.keys,strategyLawKey(law)])})
// Canonical object ordering matters: substitution reconstructs AST objects.
const formulaKey=(holds:C):string=>strategyLawKey({name:'',holds})

// This is proposal metadata, not an authorization. The exact referenced base
// hypotheses (including every independent cut's source slice) identify the
// family premises. Duplicate formulas conservatively name every owner.
// Explicit strategy scopes may be supplied, but may not omit referenced laws.
export function scopeCountProof(m:Machine,owner:Law,family:Law[],proof:CountLawProof,until:number):ScopedCountProof|undefined{
 if(!live(until)||!family.includes(owner)||new Set(family.map(l=>l.name)).size!==family.length)return undefined
 const sources:Goal[]=[],used=new Set<string>()
 for(const {goal,decls}of countedObligations(m,family,{[owner.name]:proof.instances},family.indexOf(owner))){
  if(!live(until))return undefined
  const cert=proof.certs[goal.name],expanded=cert&&mcGoal(goal.hyps,decls,cert)
  const refs=expanded&&countedCertificateHyps(expanded,cert!)
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
 return {owner:identity(owner),premises,proof:{...proof,premises:premises.map(p=>p.name)},sources,unused:family.filter(l=>!names.has(l.name)).map(l=>l.name)}
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
  const goals=countedObligations(m,family,{[owner.name]:instances},family.indexOf(owner)),certs:Record<string,CountCert>={}
  if(goals.length!==scoped.sources.length)return undefined
  for(let i=0;i<goals.length;i++){
   if(!live(until))return undefined
   const {goal,decls}=goals[i]!,cert=scoped.proof.certs[goal.name]
   const to=cert&&mcGoal(goal.hyps,decls,cert),from=scoped.sources[i]!
   const next=to&&replayCountCertificate(from,to,cert!,wallAt())
   if(!next||(!deferred&&!checkMC(goal.hyps,decls,next))||!live(until))return undefined
   certs[goal.name]=next
  }
  return {instances,certs,premises:[...names],...(deferred?{status:'unchecked' as const}:{})}
 })
}
