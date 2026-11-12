// Section 46 production scheduling. This module owns finite recipe instances,
// not proof acceptance. Every payload still goes through the caller's unchanged
// replay/native-closing path. All allocations below are exact raw root work.
import {type CountRecipeMember,type CountRecipeGraph,countRecipeGraph,countRecipeRequirements} from './count-recipe-graph.ts'
import {CountAttemptTickets,planCountRetry,type CountAttemptStop,type CountRetryKey,type CountRetryPlan} from './count-retry-budget.ts'
import {runCountRetryRound} from './count-retry-round.ts'
import {CountAttemptWork,countLeafSlot} from './count-attempt-work.ts'
import {type LiftedWorkBudget,liftedWorkLeaseBudget} from './count-lifted-budget.ts'
import {closeGreatestCountFamily,greatestClosedCountFamily,type HeldCountPayload} from './count-closed-family.ts'
import {BudgetExpired,type WorkLedger,workLedger} from './work-admission.ts'
import {type WorkAmount,compareWork,exactRaw,minWork,workAdd,workFromExact,workShare,workSub,zeroWork} from './work-amount.ts'
export type CountControllerRecipe=Readonly<{id:string,kind:'ordinary'|'strategy',required?:readonly string[],caseKeys?:readonly string[]}>
export type CountControllerMember=Readonly<{name:string,reference:number,recipes:readonly CountControllerRecipe[]}>
export type CountCaptured<T>=Readonly<{payload:T,premises:readonly string[],checkedReduced:boolean,checkCost:WorkAmount}>
type RecipeState={recipe:CountControllerRecipe,tickets:CountAttemptTickets,terminal:boolean,keys:readonly CountRetryKey[],stop?:CountAttemptStop}
type MemberState={member:CountControllerMember,recipes:RecipeState[],allotted?:WorkAmount,used:WorkAmount,held?:CountCaptured<unknown>&{recipeId:string}}
function countMap<A,B>(input:Iterable<A>,visit:(value:A)=>B,tick:()=>void):B[]{
 const out:B[]=[];for(const value of input){tick();out.push(visit(value))}return out
}
function countFind<A>(input:Iterable<A>,test:(value:A)=>boolean,tick:()=>void):A|undefined{
 for(const value of input){tick();if(test(value))return value}return undefined
}
export class CountRecipePass<T>{
 readonly rootEpoch:number
 readonly original:WorkAmount
 readonly rootEnd:WorkAmount
 readonly states:MemberState[]
 context:string
 constructor(members:readonly CountControllerMember[],context:string,readonly bank:WorkLedger=workLedger){
  const tick=()=>bank.start('ticks',1,'count recipe pass setup')
  const snapshot=bank.snapshot(),root=countFind(snapshot.activeEndpoints,scope=>scope.kind==='root',tick)
  if(!root||!snapshot.rootBaseline)throw Error('count recipe pass needs an existing raw root')
  this.rootEpoch=snapshot.rootEpoch;this.rootEnd=workFromExact(root.end)
  this.original=workSub(this.rootEnd,workFromExact(snapshot.rootBaseline.actual));this.context=context
  this.states=countMap(members,source=>{
   const recipes=countMap(source.recipes,recipe=>{
    const fixed=Object.freeze({...recipe,...(recipe.required!==undefined?{required:Object.freeze(countMap(recipe.required,name=>name,tick))}:{}),
     ...(recipe.caseKeys!==undefined?{caseKeys:Object.freeze(countMap(recipe.caseKeys,key=>key,tick))}:{})})
    return {recipe:fixed,tickets:new CountAttemptTickets(),terminal:false,keys:[] as readonly CountRetryKey[]}
   },tick)
   const member=Object.freeze({name:source.name,reference:source.reference,recipes:Object.freeze(countMap(recipes,row=>row.recipe,tick))})
   return {member,used:zeroWork,recipes}
  },tick)
 }
 reconcile(context:string):void{
  this.bank.start('tableCells',Math.min(context.length,this.context.length),'count recipe context comparison')
  if(context===this.context)return
  // Context changes withdraw payloads, never recreate recipes or grant fuel.
  for(const state of this.states){this.bank.start('ticks',1,'count recipe context withdrawal');state.held=undefined}
  this.context=context
 }
 held():ReadonlyMap<string,CountCaptured<T>&{recipeId:string}>{
  const held=new Map<string,CountCaptured<T>&{recipeId:string}>()
  for(const state of this.states){
   this.bank.start('ticks',1,'count recipe held snapshot')
   if(state.held)held.set(state.member.name,state.held as CountCaptured<T>&{recipeId:string})
  }
  return held
 }
}
export type CountControllerHooks<T,R,P=CountCaptured<T>>=Readonly<{
 construct:(name:string,recipe:CountControllerRecipe,lease:LiftedWorkBudget|undefined)=>P|undefined,
 capture?:(name:string,recipe:CountControllerRecipe,proposal:P)=>CountCaptured<T>|undefined,
 preflight?:(name:string,recipe:CountControllerRecipe)=>boolean,
 close:(rows:readonly HeldCountPayload<T>[],targetInFamily:boolean)=>R,
 observe?:(event:Record<string,unknown>)=>void,
 active?:ReadonlySet<string>,basis?:ReadonlySet<string>
}>
export function runCountRecipeController<T,R,P=CountCaptured<T>>(pass:CountRecipePass<T>,targets:readonly string[],hooks:CountControllerHooks<T,R,P>):Readonly<{result?:R,reason:string}>{
 const bank=pass.bank,tick=()=>bank.start('ticks',1,'count recipe controller')
 const map=<A,B>(input:Iterable<A>,visit:(value:A)=>B)=>countMap(input,visit,tick)
 const find=<A>(input:Iterable<A>,test:(value:A)=>boolean)=>countFind(input,test,tick)
 if(!bank.inBudget()||bank.snapshot().rootEpoch!==pass.rootEpoch)return {reason:'stale-root'}
 if(!targets.length)throw Error('count recipe controller needs a target')
 const nodeRows=():CountRecipeMember[]=>map(pass.states,state=>{
  tick();const held=state.held
  return {name:state.member.name,reference:state.member.reference,recipes:map(state.recipes,row=>{
   tick();return {id:row.recipe.id,required:row.recipe.required,terminal:row.terminal||row.tickets.snapshot().terminal||hooks.active!==undefined&&!hooks.active.has(state.member.name)}
  }),...(held?{held:{premises:held.premises,recipeId:held.recipeId,checkedReduced:held.checkedReduced}}:{})}
 })
 const graph=()=>countRecipeGraph(nodeRows(),targets,tick,{basis:hooks.basis})
 let current:CountRecipeGraph,reason='nothing-eligible'
 let searchEnd=workSub(pass.rootEnd,workShare(pass.original,3n,8n))
 const search=<U>(run:()=>U):U=>bank.withEndpoint('scope',searchEnd,run)
 try{
 current=search(graph)
 for(;;){
  const prepared=search(()=>{
   const held=pass.held(),dependencies=new Map(map(held,([name])=>[name,map(current.requirements.get(name)??[],value=>value)] as const))
   const closed=greatestClosedCountFamily(map(pass.states,state=>state.member.name),dependencies,{basis:hooks.basis,tick})
   if(find(targets,name=>find(closed.members,member=>member===name)===undefined)===undefined){reason='target-held';return}
   if(!current.next){reason=current.stop??'nothing-eligible';return}
   const choice=current.next,state=find(pass.states,row=>row.member.name===choice.name)!,row=find(state.recipes,row=>row.recipe.id===choice.recipe.id)!
   tick()
   const measured=map(held.values(),item=>item.checkCost)
   let closing=workShare(pass.original,3n,8n)
   if(measured.length){let sum=zeroWork;for(const cost of measured){tick();sum=workAdd(sum,cost)}closing=minWork(pass.original,compareWork(sum,zeroWork)>0?workShare(sum,2n,1n):bank.weights.ticks)}
   const componentEnd=workSub(pass.rootEnd,closing)
   const phaseEnd=row.recipe.kind==='strategy'?workSub(componentEnd,workShare(pass.original,1n,40n)):componentEnd
   searchEnd=componentEnd
   return {choice,state,row,phaseEnd}
  })
  if(!prepared)break
  const {choice,state,row,phaseEnd}=prepared
  if(compareWork(phaseEnd,bank.actual())<=0){reason='phase-cap';break}
  let entered=false
  try{bank.withEndpoint('scope',phaseEnd,()=>{
   const remaining=bank.available()
   if(remaining===null||compareWork(remaining,zeroWork)<=0){row.terminal=true;return}
   if(!state.allotted){
    let pending=0
    for(const member of pass.states){tick();if(current.candidates.has(member.member.name)&&!current.usable.has(member.member.name)&&!current.blocked.has(member.member.name))pending++}
    const reserved=workShare(bank.weights.ticks,BigInt(Math.max(0,pending-1)),1n)
    state.allotted=row.recipe.kind==='ordinary'?workShare(remaining,1n,BigInt(Math.max(1,pending))):compareWork(remaining,reserved)>0?workSub(remaining,reserved):zeroWork
   }
   const left=workSub(state.allotted,state.used)
   if(compareWork(left,zeroWork)<=0){for(const recipe of state.recipes){tick();recipe.terminal=true}return}
   const before=bank.actual()
   try{bank.withBudget(left,()=>{
    entered=true
    if(hooks.preflight&&!hooks.preflight(choice.name,row.recipe)){row.terminal=true;return}
    if(!row.keys.length){
     const names=row.recipe.caseKeys
     row.keys=names?.length?[...map(names,key=>({key,allocation:workShare(pass.original,1n,30n),used:zeroWork})),{key:countLeafSlot,allocation:workShare(pass.original,1n,120n),used:zeroWork}]:[{key:'body',allocation:left,used:zeroWork}]
    }
    const headrooms=()=>{const snapshot=bank.snapshot(),used=bank.actual(),reserved=bank.reserved();return map(snapshot.activeEndpoints,scope=>({scope:scope.kind+':'+scope.id,remaining:workSub(workSub(workFromExact(scope.end),used),reserved)}))}
    let plan:CountRetryPlan=row.stop?planCountRetry(row.keys,row.stop,headrooms(),bank):{kind:'admitted',need:minWork(left,bank.available()!),keys:row.keys,rootEpoch:pass.rootEpoch}
    const attempt=new CountAttemptWork(plan.kind==='admitted'?plan.keys:row.keys,bank)
    const admissionAncestors=headrooms()
    // Preparation is charged before the initial full-headroom round. A retry
    // keeps its fixed need and is revalidated atomically by the round helper.
    if(!row.stop&&plan.kind==='admitted')plan={...plan,need:minWork(left,bank.available()!)}
    hooks.observe?.({phase:'count-recipe-admission',law:choice.name,recipe:row.recipe.id,plan,previousKeys:row.keys,original:exactRaw(pass.original),allotted:exactRaw(state.allotted!),used:exactRaw(state.used),ancestors:admissionAncestors,tickets:row.tickets.snapshot()})
    const result=runCountRetryRound(plan,row.tickets,()=>{
     hooks.observe?.({phase:'count-component-attempt',law:choice.name,recipe:row.recipe.id,mode:'recipe',purpose:'required',required:row.recipe.required,rootEpoch:pass.rootEpoch})
     let lease:LiftedWorkBudget|undefined
     if(row.recipe.kind==='strategy'&&row.recipe.caseKeys!==undefined){
      const keys=plan.kind==='admitted'?plan.keys:row.keys,cases:Record<string,WorkAmount>={};let leaf:WorkAmount|undefined
      for(const key of keys){tick();if(key.key===countLeafSlot)leaf=key.allocation;else if(key.key!=='body')cases[key.key]=key.allocation}
      lease=liftedWorkLeaseBudget(pass.original,{cases,leaf,trace:event=>{attempt.trace(event);hooks.observe?.({phase:'count-recipe-slice',law:choice.name,recipe:row.recipe.id,...event})}})
     }
     const captured=hooks.construct(choice.name,row.recipe,lease)
     if(!attempt.valid())throw new BudgetExpired('unclassified count slice inventory')
     return captured?{kind:'proposal',value:captured}:{kind:'decline',reason:'constructor-declined'}
    },{bank,slices:attempt.slices,eligible:()=>{
     const fresh=graph()
     return fresh.candidates.has(choice.name)&&!fresh.blocked.has(choice.name)&&!fresh.usable.has(choice.name)&&!row.terminal
      &&(hooks.active===undefined||hooks.active.has(choice.name))
      &&find(row.recipe.required??[],name=>fresh.blocked.has(name))===undefined
    }})
    row.keys=attempt.keys()
    row.terminal=result.kind!=='unfinished'||row.tickets.snapshot().terminal
    row.stop=result.kind==='unfinished'?result.stop:undefined
    if(result.kind==='proposal'){
     // The recipe is already terminal. Post-proposal capture/checks execute
     // outside the round but still inside this persistent member/ancestor cap.
     const captured=hooks.capture?hooks.capture(choice.name,row.recipe,result.value):result.value as CountCaptured<T>
     if(captured)state.held={...captured,recipeId:row.recipe.id}
    }
    hooks.observe?.({phase:'count-recipe-result',law:choice.name,recipe:row.recipe.id,outcome:result.kind,premises:state.held?.premises,checkedReduced:state.held?.checkedReduced,...('stop'in result?{stop:result.stop}:{}),tickets:row.tickets.snapshot(),inventory:attempt.inventory(),ancestors:headrooms()})
   })}finally{state.used=workAdd(state.used,workSub(bank.actual(),before))}
  })}catch(error){
   if(!(error instanceof BudgetExpired))throw error
   row.terminal=true
   hooks.observe?.({phase:'count-recipe-result',law:choice.name,recipe:row.recipe.id,outcome:'hard-cap',stop:{kind:'hard-cap',reason:'enclosing-limit'},tickets:row.tickets.snapshot()})
   // A root/ancestor failure is not repaired by another child allocation.
   bank.check('count recipe enclosing continuation')
  }
  current=search(()=>{if(!entered){tick();row.terminal=true}return graph()})
 }
 }catch(error){
  if(!(error instanceof BudgetExpired))throw error
  reason='phase-cap';bank.check('count recipe search continuation')
 }
 const held=pass.held(),rows:HeldCountPayload<T>[]=[]
 for(const member of nodeRows()){tick();const payload=held.get(member.name);if(payload)rows.push({id:member.name,premises:map(countRecipeRequirements(member,tick),value=>value),payload:payload.payload})}
 // This is closing preparation, not search selection: traverse only the held
 // conservative premise relation and never invent or start another recipe.
 const relation=new Map(map(rows,row=>[row.id,row.premises] as const)),needed=new Set<string>(),pending=map(targets,name=>name)
 for(let at=0;at<pending.length;at++){tick();const name=pending[at]!;if(needed.has(name))continue;needed.add(name);for(const next of relation.get(name)??[]){tick();if(!needed.has(next))pending.push(next)}}
 const plan=greatestClosedCountFamily(map(pass.states,state=>state.member.name),new Map(map(rows,row=>[row.id,row.premises] as const)),{basis:hooks.basis,tick})
 const target=find(targets,name=>find(plan.members,member=>member===name)===undefined)??targets[0]!
 const closing=closeGreatestCountFamily(target,rows,{
  legacy:()=>{const selected:HeldCountPayload<T>[]=[];for(const row of rows){tick();if(needed.has(row.id))selected.push(row)}return hooks.close(selected,true)},
  reserve:()=>{const available=bank.available();return available!==null&&compareWork(available,zeroWork)>0},
  submit:selected=>hooks.close(selected,false)
 },{basis:hooks.basis,tick})
 hooks.observe?.({phase:'count-recipe-closing',reason,route:closing.route,targetInFamily:closing.targetInFamily,members:closing.plan.members,blockers:closing.plan.blockers,paths:[...closing.plan.paths]})
 return {reason,...(closing.result!==undefined?{result:closing.result}:{})}
}
