// Read cited rows, then replay/check exactly owner + cited premises once. The
// original context is a fallback only after refusal and explicit permission
// to use an existing funded scope. A hard stop is never caught here.
import {type Law,type Machine} from './machine.ts'
import {type CountLawProof,type ScopedCountProof,scopeCountProof,scopeCountProofPair,replayScopedCountProof,isCheckedReducedScope} from './count-proof-scope.ts'
import {checkMC,countedObligations} from '../kernel/kernel.ts'
import {clock,withDeadline} from '../kernel/prove.ts'
import {checkWall} from './wall.ts'
import {startWork} from './work-admission.ts'
import {workFilter,workMap} from './work-collections.ts'
export type CountRescopeEvent=Readonly<{stage:'original'|'canonical'|'drop',premise?:string,checked:boolean,units:number,reason?:string}>
export type CountRescopeOptions=Readonly<{
 allowFullFallback?:(offered:ScopedCountProof|undefined)=>boolean,
 retainUncheckedOffer?:boolean
}>
function uncheckedOffer(offered:ScopedCountProof,checkWork:number):ScopedCountProof{
 // Reuse the already captured full-scope payload. In particular, do not run
 // scope capture, identity hashing, or checked-reduced stamping a second time.
 const {checkedReduced,...scope}=offered;void checkedReduced
 return {...scope,proof:{...offered.proof,status:'unchecked'},suppliers:'unresolved',checkWork}
}
export function rescopeCountProof(m:Machine,owner:Law,family:Law[],proof:CountLawProof,_held:ReadonlySet<string>,until:number,observe?:(event:CountRescopeEvent)=>void,options:CountRescopeOptions={}):ScopedCountProof|undefined{
 return withDeadline(until,()=>{
  checkWall('counted checked rescope');startWork('ticks',1,'counted checked rescope')
  // Validate the offered declaration and infer the minimal legacy scope from
  // the same row scan. Both keep the old proof/status/receipt behavior.
  const start=clock(),{offered,inferred}=scopeCountProofPair(m,owner,family,proof,until)
  if(inferred&&clock()<until){
   const keep=new Set([owner.name]);for(const premise of inferred.premises){startWork('ticks',1,'reduced context premise');keep.add(premise.name)}
   const context=workFilter(family,l=>keep.has(l.name),'reduced context family')
   const checked=replayScopedCountProof(m,context,inferred,until)
   const scoped=checked&&scopeCountProof(m,owner,context,checked,until)
   if(scoped&&isCheckedReducedScope(scoped,m,context)){
    const units=Math.max(0,clock()-start);observe?.({stage:'canonical',checked:true,units})
    return {...scoped,checkWork:units}
   }
  }
  observe?.({stage:'canonical',checked:false,units:Math.max(0,clock()-start),...(!offered?{reason:'scope-refused'}:{})})
  checkWall('counted checked rescope fallback')
  if(clock()>=until)return undefined
  const permitted=options.allowFullFallback?.(offered)??false
  checkWall('counted checked rescope permission')
  if(clock()>=until)return undefined
  if(!permitted){
   if(!options.retainUncheckedOffer||!offered)return undefined
   observe?.({stage:'original',checked:false,units:0,reason:'unfunded-unchecked-offer'})
   return uncheckedOffer(offered,Math.max(0,clock()-start))
  }
  const before=clock()
  // This is at most one pass over the original INIT/STEP goals; no drop loop,
  // fresh lease, reduced-context retry or fallback on an exception exists.
  for(const {goal,decls}of countedObligations(m,family,{[owner.name]:proof.instances},family.indexOf(owner))){
   startWork('ticks',1,'full fallback obligation');const cert=proof.certs[goal.name]
   if(clock()>=until||!cert||!checkMC(goal.hyps,decls,cert)){
    observe?.({stage:'original',checked:false,units:Math.max(0,clock()-before)});return undefined
   }
  }
  observe?.({stage:'original',checked:true,units:Math.max(0,clock()-before)})
  // A full-only acceptance has no reduced receipt and cannot erase recipe
  // requirements. The caller must conservatively union those requirements.
  if(clock()>=until)return undefined
  if(offered)return uncheckedOffer(offered,Math.max(0,clock()-start))
  const fallback=scopeCountProof(m,owner,family,{...proof,status:'unchecked',premises:workMap(family,l=>l.name,'full fallback context')},until)
  return fallback&&clock()<until?{...fallback,checkWork:Math.max(0,clock()-start)}:undefined
 })
}
