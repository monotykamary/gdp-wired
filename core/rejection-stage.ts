// Untrusted candidate policy. Only original-interpreter replay justifies a drop;
// none of this ledger is proof admission.
import {type Law,type Machine,type Request,type State,interpret} from './machine.ts'
import {finiteEvaluator} from './finite-houdini.ts'
import {finiteModelChecker} from './finite-model.ts'
import {BudgetExpired,budgetEnd,checkBudget,fullRate,fullWork,remainingWork,withBudget} from '../kernel/prove.ts'
import {WallExpired} from './wall.ts'
type Params=Record<string,number>
export type RejectionEvidence={kind:'reachable',law:Law,params:Params,requests:Request[],post:State}|{kind:'relative',law:Law,params:Params,pre:State,request:Request,post:State}
export type RejectionOutcome={status:'ignored'|'rejected'|'broken'|'weak',rejected:Law[],safety:Law[]}
const none=():RejectionOutcome=>({status:'ignored',rejected:[],safety:[]})
const declarations=(m:Machine):Law[]=>[...(m.pre?[{name:'rejection parameter precondition',holds:m.pre}]:[]),...m.facts??[]]
export function createRejectionStage(source:Machine,m:Machine,caller:readonly Law[],candidates:readonly Law[],allowance:number){
 if(!Number.isFinite(allowance)||allowance<0||!Number.isFinite(allowance*fullRate))throw new RangeError('rejection allowance must be finite and nonnegative')
 const all=[...new Set([...caller,...candidates])],protectedLaws=new Set(caller),records=new Map<Law,RejectionEvidence>(),restored=new Set<Law>(),start=fullWork(),limit=allowance*fullRate
 let safetyStatus:'broken'|'weak'|undefined
 const evaluate=finiteEvaluator(m),sourceEvaluate=finiteEvaluator(source),facts=declarations(m),sourceFacts=declarations(source),run=interpret(source),complete=finiteModelChecker(m)
 let charged=fullWork()-start,activeAt:number|undefined,exhausted=false,revision=0
 let commits:(()=>void)[]=[]
 const active=()=>all.filter(l=>!records.has(l)),spent=()=>charged+(activeAt===undefined?0:fullWork()-activeAt)
 function bounded<T>(fallback:T,body:()=>T):T{
  // Even an exhausted local stage must not hide cancellation of its parent.
  checkBudget('rejection parent')
  if(exhausted||spent()>=limit)return fallback
  if(activeAt!==undefined){checkBudget('nested rejection entry');const out=body();checkBudget('nested rejection completion');return out}
  // A nonrestricting scope exposes the effective inherited endpoint, including
  // withWork's otherwise private cap. This also disambiguates an exact tie:
  // a refusal shared with the parent must propagate, not become local expiry.
  const parentEnd=withBudget(Number.MAX_VALUE,()=>budgetEnd())
  const before=fullWork(),localEnd=(before+Math.max(0,limit-charged))/fullRate
  let localRefusal=false,installedEnd:number|undefined
  activeAt=before;commits=[]
  try{
   const out=withBudget(Math.max(0,limit-charged),()=>{
    installedEnd=budgetEnd()
    try{checkBudget('rejection evidence');return body()}
    catch(error){
     // Admission can refuse an expensive primitive BEFORE charging it. Read
     // the actual installed endpoint and refusal marker while still inside I.
     if(error instanceof BudgetExpired&&budgetEnd()===localEnd&&localEnd<parentEnd&&remainingWork()===0)localRefusal=true
     throw error
    }
   })
   // withBudget's completion check has succeeded. Publication itself cannot
   // evaluate a law, replay a step, clone user data, or incur a budget charge.
   for(const commit of commits)commit()
   return out
  }catch(error){
   checkBudget('rejection parent completion')
   if(error instanceof BudgetExpired&&(localRefusal||(installedEnd===localEnd&&localEnd<parentEnd&&spent()>=limit))){exhausted=true;return fallback}
   throw error
  }finally{commits=[];charged+=fullWork()-before;activeAt=undefined}
 }
 function enabled(params:Params,pre:State,request:Request):State|undefined{
  try{return run.step(params,pre,request)}catch(error){if(error instanceof BudgetExpired||error instanceof WallExpired)throw error;return undefined}
 }
 const declared=(params:Params,pre:State)=>sourceFacts.every(l=>sourceEvaluate(l,params,pre)===true)&&facts.every(l=>evaluate(l,params,pre)===true)
 function publish(out:RejectionOutcome,evidence:Map<Law,RejectionEvidence>,version:number):void{
  const status=out.status
  commits.push(()=>{
   if(status==='broken')safetyStatus='broken'
   else if(status==='weak')safetyStatus ??= 'weak'
   // An enclosing callback may expand the family before it returns. Never
   // publish a relative witness validated against that obsolete family.
   for(const [law,witness] of evidence)if(witness.kind==='reachable'||version===revision)records.set(law,witness)
  })
 }
 function reachable(params0:Params,requests0:readonly Request[]):RejectionOutcome{
  return bounded(none(),()=>{
   const out=none(),evidence=new Map<Law,RejectionEvidence>(),params=structuredClone(params0),requests=structuredClone([...requests0]);let post:State
   try{post=run.init(params)}catch(error){if(error instanceof BudgetExpired||error instanceof WallExpired)throw error;return out}
   if(!declared(params,post))return out
   for(const request of requests){const next=enabled(params,post,request);if(!next||!declared(params,next))return out;post=next}
   out.safety=caller.filter(l=>evaluate(l,params,post)===false)
   if(out.safety.length)out.status='broken'
   else for(const law of all){
    if(protectedLaws.has(law)||evaluate(law,params,post)!==false)continue
    evidence.set(law,structuredClone({kind:'reachable',law,params,requests,post}));out.rejected.push(law);out.status='rejected'
   }
   publish(out,evidence,revision)
   return out
  })
 }
 function relative(params0:Params,pre0:State,request0:Request):RejectionOutcome{
  return bounded(none(),()=>{
   const out=none(),evidence=new Map<Law,RejectionEvidence>(),params=structuredClone(params0),pre=structuredClone(pre0),request=structuredClone(request0),family=active(),version=revision
   if(!declared(params,pre)||!family.every(l=>evaluate(l,params,pre)===true))return out
   const post=enabled(params,pre,request);if(!post)return out
   out.safety=caller.filter(l=>evaluate(l,params,post)===false)
   if(out.safety.length)out.status='weak'
   else for(const law of family){
    if(protectedLaws.has(law)||evaluate(law,params,post)!==false)continue
    evidence.set(law,structuredClone({kind:'relative',law,params,pre,request,post}));out.rejected.push(law);out.status='rejected'
   }
   publish(out,evidence,version)
   return out
  })
 }
 function addCandidates(laws:readonly Law[]):Law[]{
  const added=[...new Set(laws)].filter(law=>!all.includes(law))
  if(!added.length)return []
  all.push(...added);revision++
  const revived:Law[]=[]
  // Restoration is monotone, not a publication transaction. On local expiry
  // every unvalidated relative witness is removed, including cascades. Outer
  // cancellation also restores conservatively before propagating; never roll
  // back to evidence for a smaller, stale family.
  try{
   for(let changed=true;changed;){
    changed=false;const family=active()
    for(const [law,witness] of records){
     if(witness.kind==='reachable')continue
     const valid=bounded(false,()=>declared(witness.params,witness.pre)&&family.every(l=>evaluate(l,witness.params,witness.pre)===true))
     if(!valid){records.delete(law);restored.add(law);revived.push(law);changed=true}
    }
   }
  }catch(error){
   for(const [law,witness] of records)if(witness.kind==='relative'){records.delete(law);restored.add(law)}
   throw error
  }
  return revived
 }
 function model(law:Law,witness:Record<string,number>):RejectionOutcome{
  return bounded(none(),()=>{const candidate=complete(active(),law,witness);return candidate.genuine?relative(candidate.params,candidate.pre,candidate.request):none()})
 }
 return {active,addCandidates,reachable,relative,model,restored:()=>active().filter(law=>restored.has(law)),safety:()=>safetyStatus,within:<T>(body:()=>T)=>bounded<T|undefined>(undefined,body),work:()=>({used:spent()/fullRate,limit:allowance}),evidence:()=>[...records.values()].map(record=>structuredClone(record))}
}
export type RejectionStage=ReturnType<typeof createRejectionStage>
// A restored helper belongs to EVERY later proof context, not only the call
// which enlarged the ledger. A subsequent validated rejection may omit it.
export function rejectionFamily(stage:RejectionStage,initial:readonly Law[]):Law[]{
 stage.addCandidates(initial)
 const requested=new Set([...initial,...stage.restored()])
 return stage.active().filter(law=>requested.has(law))
}
