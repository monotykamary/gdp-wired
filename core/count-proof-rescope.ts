// A proposal's declared scope is an offer, not evidence of a dependency.
// Remove it only by transporting the same certificate and checking the new
// INIT/STEP goals. No search and no weakening of replay's normal scope guard.
import {type Law,type Machine} from './machine.ts'
import {type CountLawProof,type ScopedCountProof,scopeCountProof,replayScopedCountProof} from './count-proof-scope.ts'
import {checkMC,countedObligations} from '../kernel/kernel.ts'
import {clock,withDeadline} from '../kernel/prove.ts'
import {checkWall} from './wall.ts'
export type CountRescopeEvent=Readonly<{stage:'original'|'canonical'|'drop',premise?:string,checked:boolean,units:number}>
export function rescopeCountProof(m:Machine,owner:Law,family:Law[],proof:CountLawProof,held:ReadonlySet<string>,until:number,observe?:(event:CountRescopeEvent)=>void):ScopedCountProof|undefined{
 return withDeadline(until,()=>{
  checkWall('counted checked rescope')
  const offered=scopeCountProof(m,owner,family,proof,until)
  if(!offered)return undefined
  const start=clock()
  for(const {goal,decls}of countedObligations(m,family,{[owner.name]:proof.instances},family.indexOf(owner))){
   if(clock()>=until||!proof.certs[goal.name]||!checkMC(goal.hyps,decls,proof.certs[goal.name]!)){
    observe?.({stage:'original',checked:false,units:clock()-start});return undefined
   }
  }
  let checkWork=Math.max(0,clock()-start)
  observe?.({stage:'original',checked:true,units:checkWork})
  // The native check above is compulsory even for a deferred STEP proposal.
  // Inferred references may be smaller than the explicit offered superset.
  let current=scopeCountProof(m,owner,family,{instances:proof.instances,certs:proof.certs},until)
  if(!current||clock()>=until)return undefined
  let context=family
  const attempt=(next:Law[],candidate:ScopedCountProof,stage:'canonical'|'drop',premise?:string):boolean=>{
   const before=clock(),checked=replayScopedCountProof(m,next,candidate,until)
   const units=Math.max(0,clock()-before)
   observe?.({stage,premise,checked:!!checked,units})
   if(!checked)return false
   const scoped=scopeCountProof(m,owner,next,checked,until)
   if(!scoped)return false
   current=scoped;context=next;checkWork=Math.max(checkWork,units)
   return true
  }
  const keep=new Set([owner.name,...current.premises.map(p=>p.name),...held])
  const compact=family.filter(l=>keep.has(l.name))
  if(compact.length<family.length)attempt(compact,current,'canonical')
  // A failed transport is not a claim of logical necessity. Retain that
  // premise in this checked certificate; the family checker remains final.
  for(const premise of [...current.premises]){
   if(premise.name===owner.name||held.has(premise.name))continue
   if(clock()>=until)return undefined
   const candidate={...current,premises:current.premises.filter(p=>p.name!==premise.name),unused:[...current.unused,premise.name]}
   attempt(context.filter(l=>l.name!==premise.name),candidate,'drop',premise.name)
  }
  checkWall('counted checked rescope')
  return clock()<until?{...current,checkWork}:undefined
 })
}
