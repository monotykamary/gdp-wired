// Section 46.2'/46.3': untrusted scheduling only. S is computed conservatively
// here; a checkedReduced marker must come from the accepted exact-scope replay.
// This graph never accepts a proof, replenishes fuel, or creates a recipe.
import {startWork} from './work-admission.ts'
import {checkWall} from './wall.ts'
export type CountRecipeNode=Readonly<{id:string,required?:readonly string[],terminal:boolean}>
export type CountHeldNode=Readonly<{premises:readonly string[],recipeId:string,checkedReduced:boolean}>
export type CountRecipeMember=Readonly<{name:string,reference:number,recipes:readonly CountRecipeNode[],held?:CountHeldNode}>
export type CountRecipeChoice=Readonly<{name:string,recipe:CountRecipeNode,stranded:boolean,weight:number,requiredSize:number}>
export type CountRecipeGraph=Readonly<{blocked:ReadonlySet<string>,usable:ReadonlySet<string>,closure:ReadonlySet<string>,requirements:ReadonlyMap<string,ReadonlySet<string>>,next?:CountRecipeChoice,stop?:'target-blocked'|'nothing-eligible'}>
const control=()=>{checkWall('count recipe graph');startWork('ticks',1,'count recipe graph')}
export function countRecipeGraph(members:readonly CountRecipeMember[],targets:readonly string[],tick:()=>void=control):CountRecipeGraph{
 const byName=new Map<string,CountRecipeMember>(),references=new Set<number>(),requirements=new Map<string,Set<string>>()
 for(const member of members){
  tick()
  if(byName.has(member.name)||!Number.isSafeInteger(member.reference)||member.reference<0||references.has(member.reference))throw Error('invalid or duplicate recipe member')
  byName.set(member.name,member);references.add(member.reference)
  const ids=new Set<string>(),required=new Set<string>()
  for(const recipe of member.recipes){tick();if(!recipe.id||ids.has(recipe.id))throw Error('duplicate recipe instance');ids.add(recipe.id)
   if(!member.held&&!recipe.terminal)for(const name of recipe.required??[]){tick();required.add(name)}
  }
  if(member.held){
   for(const name of member.held.premises){tick();required.add(name)}
   const producing=member.recipes.find(recipe=>{tick();return recipe.id===member.held!.recipeId})
   if(!producing)throw Error('held member has no producing recipe')
   if(!producing.terminal)throw Error('completed recipe must be terminal')
   if(!member.held.checkedReduced)for(const name of producing.required??[]){tick();required.add(name)}
  }
  requirements.set(member.name,required)
 }
 const blocked=new Set<string>()
 // A missing candidate is unobtainable in this pass. It participates in the
 // same least fixed point rather than being silently dropped from a scope.
 for(const required of requirements.values())for(const name of required){tick();if(!byName.has(name))blocked.add(name)}
 for(const member of members)for(const recipe of member.recipes)for(const name of recipe.required??[]){tick();if(!byName.has(name))blocked.add(name)}
 const eligible=(recipe:CountRecipeNode)=>{
  tick();if(recipe.terminal)return false
  for(const name of recipe.required??[]){tick();if(blocked.has(name))return false}
  return true
 }
 const isUsable=(member:CountRecipeMember)=>{
  tick();if(!member.held)return false
  for(const name of requirements.get(member.name)!){tick();if(blocked.has(name))return false}
  return true
 }
 let changed=true
 while(changed){changed=false
  for(const member of members){tick();if(blocked.has(member.name)||isUsable(member))continue
   let hasRecipe=false;for(const recipe of member.recipes){tick();if(eligible(recipe)){hasRecipe=true;break}}
   if(!hasRecipe){blocked.add(member.name);changed=true}
  }
 }
 const usable=new Set<string>()
 for(const member of members){tick();if(isUsable(member))usable.add(member.name)}
 const reachable=(starts:Iterable<string>)=>{
  const seen=new Set<string>(),queue:string[]=[]
  for(const name of starts){tick();queue.push(name)}
  for(let at=0;at<queue.length;at++){tick();const name=queue[at]!;if(seen.has(name))continue;seen.add(name)
   for(const prerequisite of requirements.get(name)??[]){tick();if(!seen.has(prerequisite))queue.push(prerequisite)}
  }
  return seen
 }
 const closure=reachable(targets)
 for(const target of targets){tick();if(!byName.has(target)||blocked.has(target))return {blocked,usable,closure,requirements,stop:'target-blocked'}}
 const weights=new Map<string,number>()
 for(const name of closure){tick();for(const prerequisite of reachable([name])){tick();if(prerequisite!==name&&closure.has(prerequisite))weights.set(prerequisite,(weights.get(prerequisite)??0)+1)}}
 let next:CountRecipeChoice|undefined,bestReference=Infinity
 for(const member of members){tick();if(!closure.has(member.name)||usable.has(member.name)||blocked.has(member.name))continue
  let recipe:CountRecipeNode|undefined
  for(const candidate of member.recipes){tick();if(eligible(candidate)&&(!recipe||(recipe.required===undefined&&candidate.required!==undefined)))recipe=candidate}
  if(!recipe)continue
  const candidate:CountRecipeChoice={name:member.name,recipe,stranded:!!member.held,weight:weights.get(member.name)??0,requiredSize:requirements.get(member.name)!.size}
  const known=recipe.required!==undefined,previousKnown=next?.recipe.required!==undefined
  if(!next||candidate.weight>next.weight||candidate.weight===next.weight&&(candidate.requiredSize>next.requiredSize||candidate.requiredSize===next.requiredSize&&(known&&!previousKnown||known===previousKnown&&member.reference<bestReference))){next=candidate;bestReference=member.reference}
 }
 return next?{blocked,usable,closure,requirements,next}:{blocked,usable,closure,requirements,stop:'nothing-eligible'}
}
