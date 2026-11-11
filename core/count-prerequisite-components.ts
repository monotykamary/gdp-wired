// Untrusted mutual-induction scheduling. Holding a proposal is not admission;
// the caller still replays the closed family and invokes the native checker.
export type CountComponentRecipe=Readonly<{id:string,kind:'ordinary'|'strategy',required?:readonly string[],optional?:readonly string[]}>
export type CountComponentOptions=Readonly<{recipes?:ReadonlyMap<string,readonly CountComponentRecipe[]>,costs?:ReadonlyMap<string,number>,discoveryFirst?:boolean,proofGuided?:boolean,discoveryContexts?:ReadonlyMap<string,string>,targets?:readonly string[],held?:ReadonlyMap<string,readonly string[]>,discovered?:readonly string[],failed?:readonly string[]}>
export type ComponentOutcome=Readonly<{kind:'proof',citations:readonly string[]}>|Readonly<{kind:'unknown',reason:string}>|Readonly<{kind:'refuted'|'refused',reason?:string}>
export type ComponentAttempt=Readonly<{kind:'attempt',name:string,component:readonly string[],context:readonly string[],phase:'dissolve'|'joint',discovery:boolean,purpose:'discovery'|'required',recipe:CountComponentRecipe,pass?:0|1}>
export type ComponentDecision=ComponentAttempt|Readonly<{kind:'ready',members:readonly string[]}>
export function countPrerequisiteComponents(input:readonly string[],requirements:ReadonlyMap<string,readonly string[]>,strategies:readonly string[]=[],available:readonly string[]=[],options:CountComponentOptions={}){
 const order=[...input],members=new Set(order),strategic=new Set(strategies),admitted=new Set(available),failed=new Set(options.failed??[]),dissolved=new Set<string>(),discovered=new Set(options.discovered??[])
 const required=new Map(order.map(name=>[name,[...new Set(requirements.get(name)??[])].filter(p=>p!==name)])),actual=new Map<string,readonly string[]>()
 const recipes=new Map<string,readonly CountComponentRecipe[]>()
 for(const name of order){
  const declared:readonly CountComponentRecipe[]=options.recipes?.get(name)??[{id:strategic.has(name)?'strategy':'ordinary',kind:strategic.has(name)?'strategy':'ordinary',...(strategic.has(name)?{required:required.get(name)}:{})}]
  recipes.set(name,declared.map(recipe=>Object.freeze({...recipe,...(recipe.required?{required:[...recipe.required]}:{}),...(recipe.optional?{optional:[...recipe.optional]}:{})})))
 }
 for(const [name,premises]of options.held??[]){
  if(!members.has(name)||premises.some(p=>!members.has(p)||failed.has(p)))throw Error('invalid remembered component')
  actual.set(name,[...premises])
 }
 const costs=new Map(order.map((name,index)=>[name,options.costs?.get(name)??index]))
 const retries=new Map<string,number>(),requiredRuns=new Set<string>(),discoveryContexts=new Map(options.discoveryContexts),unknown=new Map<string,{reason:string,component:readonly string[],stamp:string,pass?:0|1}>()
 let active:ComponentAttempt|undefined
 if(members.size!==order.length||available.some(name=>!members.has(name))||strategies.some(name=>!members.has(name))||[...costs.values()].some(value=>!Number.isFinite(value)))throw Error('ambiguous component family')
 const primary=(name:string)=>recipes.get(name)?.[0]
 if(order.some(name=>!primary(name)))throw Error('component member has no recipe')
 const uncertain=(name:string)=>primary(name)?.required===undefined
 const deps=(name:string)=>actual.get(name)??required.get(name)??[]
 const live=()=>order.filter(name=>!admitted.has(name)&&!failed.has(name))
 const availableStamp=()=>JSON.stringify(order.filter(name=>admitted.has(name)))
 for(const name of discovered)if(!discoveryContexts.has(name))discoveryContexts.set(name,availableStamp())
 const stamp=(group:readonly string[],context:readonly string[],purpose='required')=>JSON.stringify([group,context,order.filter(name=>admitted.has(name)),purpose])
 function needed():Set<string>{
  const out=new Set(options.targets??strategies),todo=[...out]
  for(const name of todo)for(const premise of deps(name))if(members.has(premise)&&!out.has(premise)){out.add(premise);todo.push(premise)}
  return out
 }
 for(const name of discovered)if(members.has(name)&&!actual.has(name)&&!failed.has(name))unknown.set(name,{reason:'parked discovery',component:[name],stamp:''})
 const knownStrategy=(name:string)=>primary(name)?.kind==='strategy'&&primary(name)?.required!==undefined
 const ranked=(group:readonly string[],guided=options.proofGuided)=>[...group].sort((a,b)=>
  (guided?Number(requiredRuns.has(a))-Number(requiredRuns.has(b))||Number(knownStrategy(b))-Number(knownStrategy(a)):0)||costs.get(a)!-costs.get(b)!||order.indexOf(a)-order.indexOf(b))
 function components():string[][]{
  const pending=new Set(live()),index=new Map<string,number>(),low=new Map<string,number>(),stack:string[]=[],onStack=new Set<string>(),out:string[][]=[]
  // Unknown ordinary requirements are possibly incoming, not known absent.
  // Only an actual citation (or an expired required prerequisite) groups one
  // with its user. These reverse scheduling edges never become proof premises.
  const reverse=new Map<string,string[]>()
  for(const owner of pending)for(const premise of deps(owner))if(pending.has(premise)&&uncertain(premise)&&(actual.has(owner)||unknown.has(premise)&&(!options.discoveryFirst||needed().has(owner)))){
   const users=reverse.get(premise)??[];users.push(owner);reverse.set(premise,users)
  }
  const edges=(name:string)=>[...deps(name),...reverse.get(name)??[]]
  let at=0
  const visit=(name:string)=>{
   index.set(name,at);low.set(name,at++);stack.push(name);onStack.add(name)
   for(const premise of edges(name))if(pending.has(premise)){
    if(!index.has(premise)){visit(premise);low.set(name,Math.min(low.get(name)!,low.get(premise)!))}
    else if(onStack.has(premise))low.set(name,Math.min(low.get(name)!,index.get(premise)!))
   }
   if(low.get(name)===index.get(name)){
    const group:string[]=[]
    for(;;){const member=stack.pop()!;onStack.delete(member);group.push(member);if(member===name)break}
    out.push(order.filter(member=>group.includes(member)))
   }
  }
  for(const name of pending)if(!index.has(name))visit(name)
  return out.sort((a,b)=>costs.get(ranked(a)[0]!)!-costs.get(ranked(b)[0]!)!)
 }
 function next():ComponentDecision|undefined{
  if(active)return active
  const groups=components(),pending=new Set(live())
  // Commit actual closed scopes before scheduling more search. This shrinks
  // later discovery contexts without claiming native whole-family acceptance.
  for(const group of groups){
   const own=new Set(group)
   if(group.every(name=>actual.has(name)&&actual.get(name)!.every(p=>admitted.has(p)||own.has(p))))return {kind:'ready',members:group}
  }
  if(options.discoveryFirst){
   const name=ranked(live(),false).find(name=>!strategic.has(name)&&!actual.has(name)&&(!discovered.has(name)||options.proofGuided&&discoveryContexts.get(name)!==availableStamp()))
   if(name!==undefined){active={kind:'attempt',name,component:groups.find(group=>group.includes(name))!,context:order.filter(member=>admitted.has(member)||member===name),phase:'joint',discovery:true,purpose:'discovery',recipe:primary(name)!};return active}
  }
  const wanted=needed()
  const fresh=(group:readonly string[])=>group.some(name=>!actual.has(name)&&!requiredRuns.has(name)&&(strategic.has(name)||wanted.has(name)))
  const strategy=(group:readonly string[])=>group.some(name=>!actual.has(name)&&knownStrategy(name))
  const scheduled=options.discoveryFirst?[...groups].sort((a,b)=>options.proofGuided
   ?Number(fresh(b))-Number(fresh(a))||Number(strategy(b))-Number(strategy(a))
   :Number(b.some(name=>strategic.has(name)))-Number(a.some(name=>strategic.has(name)))):groups
  for(const group of scheduled){
   const own=new Set(group)
   if(!options.discoveryFirst&&!group.every(name=>deps(name).every(p=>!pending.has(p)||own.has(p))))continue
   const sorted=ranked(group)
   // An unknown ordinary recipe cannot justify cycle dissolution. A declared
   // alternative must have a known required set entirely outside this group.
   for(const name of group.length>1?sorted:[]){
    if(actual.has(name)||options.discoveryFirst&&!strategic.has(name)&&!wanted.has(name))continue
    const alternative=recipes.get(name)!.find(recipe=>recipe.id!==primary(name)!.id&&recipe.required!==undefined&&recipe.required.every(p=>!own.has(p))&&!dissolved.has(JSON.stringify([name,recipe.id])))
    if(alternative){active={kind:'attempt',name,component:group,context:order.filter(member=>admitted.has(member)||member===name),phase:'dissolve',discovery:false,purpose:'required',recipe:alternative};return active}
   }
   const discovery=group.length===1&&uncertain(group[0]!),potential=new Set(group)
   for(let changed=true;changed;){
    changed=false
    for(const member of pending)if(!potential.has(member)&&(deps(member).some(p=>potential.has(p))||options.discoveryFirst&&[...potential].some(owner=>deps(owner).includes(member)))){potential.add(member);changed=true}
   }
   const context=order.filter(member=>admitted.has(member)||potential.has(member)||uncertain(member)&&pending.has(member)||discovery&&pending.has(member))
   const currentStamp=stamp(group,context)
   const retry=(name:string)=>options.proofGuided&&primary(name)!.kind==='ordinary'&&unknown.get(name)?.stamp===currentStamp&&unknown.get(name)?.pass===0
   const name=sorted.find(member=>!actual.has(member)&&(!options.discoveryFirst||strategic.has(member)||wanted.has(member))&&(unknown.get(member)?.stamp!==currentStamp||retry(member)))
   if(name===undefined)continue
   active={kind:'attempt',name,component:group,context,phase:'joint',discovery,purpose:'required',recipe:primary(name)!,...(options.proofGuided?{pass:retry(name)?1 as const:0 as const}:{})}
   return active
  }
  return undefined
 }
 function finish(name:string,result:ComponentOutcome|readonly string[]|undefined):{held:boolean,invalidated:readonly string[]}{
  if(!active||active.name!==name)throw Error('component result without matching attempt')
  const attempt=active;active=undefined
  const received:ComponentOutcome=result===undefined?{kind:'refused'}:'kind'in result?result:{kind:'proof',citations:result}
  const outcome:ComponentOutcome=attempt.purpose==='discovery'&&received.kind==='refuted'?{kind:'unknown',reason:'narrow-sat'}:received
  if(attempt.purpose==='discovery'){discovered.add(name);discoveryContexts.set(name,availableStamp())}
  else requiredRuns.add(name)
  if(attempt.phase==='dissolve')dissolved.add(JSON.stringify([name,attempt.recipe.id]))
  if(outcome.kind==='unknown'){
   if(attempt.phase!=='dissolve')unknown.set(name,{reason:outcome.reason,component:[...attempt.component],stamp:stamp(attempt.component,attempt.context,attempt.purpose),...(attempt.pass===undefined?{}:{pass:attempt.pass})})
   return {held:false,invalidated:[]}
  }
  const scope=outcome.kind==='proof'?[...new Set(outcome.citations)].filter(p=>p!==name):undefined
  const valid=scope&&scope.every(p=>members.has(p)&&!failed.has(p)&&attempt.context.includes(p))
  if(!valid){
   if(attempt.phase==='dissolve')return {held:false,invalidated:[]}
   failed.add(name);actual.delete(name);unknown.delete(name)
   const invalidated:string[]=[],unavailable=new Set([name])
   for(let changed=true;changed;){
    changed=false
    for(const [owner,premises]of actual)if(premises.some(p=>unavailable.has(p))){
     actual.delete(owner);unknown.delete(owner);unavailable.add(owner);invalidated.push(owner);retries.set(owner,(retries.get(owner)??0)+1);changed=true
    }
   }
   return {held:false,invalidated}
  }
  unknown.delete(name);actual.set(name,scope!)
  return {held:true,invalidated:[]}
 }
 // Only the caller's validated original-reachable evidence uses this entry.
 // Dependents lose their old scopes/commit status, not their truth: rebuild
 // them in the reduced context rather than treating them as counterexamples.
 function reject(names:readonly string[]):readonly string[]{
  if(names.some(name=>!members.has(name)))throw Error('unknown rejected member')
  const unavailable=new Set(names),invalidated:string[]=[]
  for(const name of names){failed.add(name);actual.delete(name);admitted.delete(name);unknown.delete(name)}
  for(let changed=true;changed;){
   changed=false
   for(const [owner,premises]of actual)if(premises.some(p=>unavailable.has(p))){
    actual.delete(owner);admitted.delete(owner);unknown.delete(owner);requiredRuns.delete(owner)
    discovered.delete(owner);discoveryContexts.delete(owner)
    unavailable.add(owner);invalidated.push(owner);retries.set(owner,(retries.get(owner)??0)+1);changed=true
   }
  }
  if(active&&(unavailable.has(active.name)||active.context.some(name=>unavailable.has(name))))active=undefined
  return invalidated
 }

 function commit(names:readonly string[]):void{
  const decision=next()
  if(decision?.kind!=='ready'||names.length!==decision.members.length||names.some((name,i)=>name!==decision.members[i]))throw Error('component not closed')
  for(const name of names)admitted.add(name)
 }
 return {next,finish,commit,reject,available:()=>order.filter(name=>admitted.has(name)),failed:()=>order.filter(name=>failed.has(name)),held:()=>order.filter(name=>actual.has(name)&&!admitted.has(name)),unknown:()=>order.filter(name=>unknown.has(name)&&!admitted.has(name)&&!failed.has(name)).map(name=>({name,reason:unknown.get(name)!.reason,component:unknown.get(name)!.component,citedBy:order.filter(owner=>actual.get(owner)?.includes(name))})),retryCount:()=>Object.fromEntries(retries),discovered:()=>order.filter(name=>discovered.has(name)),discoveryContexts:()=>new Map(discoveryContexts),required:()=>order.filter(name=>needed().has(name)),components}
}
