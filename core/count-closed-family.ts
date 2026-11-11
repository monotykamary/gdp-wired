// Untrusted closure bookkeeping. Only the existing native family check can accept.
import {startWork} from './work-admission.ts'
import {checkWall} from './wall.ts'
import {workSetArray,workStrings} from './work-collections.ts'
export type CountClosedOptions=Readonly<{basis?:ReadonlySet<string>,tick?:()=>void}>
export type CountBlockerPath=Readonly<{blocker:string,path:readonly string[]}>
export type ClosedCountFamily=Readonly<{members:readonly string[],missing:ReadonlyMap<string,readonly string[]>,blockers:readonly string[],paths:ReadonlyMap<string,readonly CountBlockerPath[]>}>
const control=()=>{checkWall('closed counted family');startWork('ticks',1,'closed counted family')}
// Frozen H/S: monotone deletion removes at most |H| members. Every closed subset
// survives every deletion, hence the fixed point is the unique greatest one.
export function greatestClosedCountFamily(order:readonly string[],held:ReadonlyMap<string,readonly string[]>,options:CountClosedOptions={}):ClosedCountFamily{
 const tick=options.tick??control,rank=new Map<string,number>(),dependencies=new Map<string,string[]>(),basis=new Set<string>()
 for(const name of options.basis??[]){tick();basis.add(name)}
 for(const name of order){tick();if(rank.has(name))throw Error('duplicate family member');rank.set(name,rank.size)}
 for(const [name,premises]of held){tick();if(!rank.has(name))throw Error('held member missing from family order');const copy:string[]=[],seen=new Set<string>();for(const premise of premises){tick();if(!seen.has(premise)){seen.add(premise);copy.push(premise)}}dependencies.set(name,copy)}
 const members=new Set<string>();for(const name of order){tick();if(dependencies.has(name))members.add(name)}
 let changed=true
 while(changed){changed=false;for(const name of order){tick();if(!members.has(name))continue;for(const premise of dependencies.get(name)!){tick();if(!members.has(premise)&&!basis.has(premise)){members.delete(name);changed=true;break}}}}
 const closed:string[]=[],missing=new Map<string,readonly string[]>(),paths=new Map<string,readonly CountBlockerPath[]>(),allRoots=new Set<string>()
 for(const name of order){tick();if(members.has(name)){closed.push(name);continue}if(!dependencies.has(name))continue
  const outside:string[]=[];for(const premise of dependencies.get(name)!){tick();if(!members.has(premise)&&!basis.has(premise))outside.push(premise)}missing.set(name,outside)
  const seen=new Set<string>(),queue:Array<{name:string,path:string[]}>= [{name,path:[name]}],found:CountBlockerPath[]=[]
  for(let at=0;at<queue.length;at++){tick();const item=queue[at]!;if(seen.has(item.name)||basis.has(item.name)||members.has(item.name))continue;seen.add(item.name)
   const next=dependencies.get(item.name);if(!next){allRoots.add(item.name);found.push({blocker:item.name,path:item.path});continue}
   for(const premise of next){tick();const path:string[]=[];for(const part of item.path){tick();path.push(part)}path.push(premise);queue.push({name:premise,path})}
  }
  paths.set(name,found)
 }
 const blockers:string[]=[];for(const name of order){tick();if(allRoots.delete(name))blockers.push(name)}
 for(const name of workStrings(workSetArray(allRoots,'closed-family:unknown-roots'),'closed-family:unknown-blockers')){tick();blockers.push(name)}
 return {members:closed,missing,blockers,paths}
}
export type HeldCountPayload<T>=Readonly<{id:string,premises:readonly string[],payload:T}>
export type CountCloseCallbacks<T,R>=Readonly<{legacy:()=>R,reserve:(members:readonly HeldCountPayload<T>[])=>boolean,submit:(members:readonly HeldCountPayload<T>[])=>R}>
// A owns callbacks, checked-basis policy and native verdict interpretation.
// The legacy callback receives no reconstructed family. No callback result is
// promoted to success for an outside target, even when its subset was accepted.
export function closeGreatestCountFamily<T,R>(target:string,held:readonly HeldCountPayload<T>[],callbacks:CountCloseCallbacks<T,R>,options:CountClosedOptions={}):Readonly<{plan:ClosedCountFamily,targetInFamily:boolean,route:'legacy'|'subset'|'empty'|'unfunded',submitted:boolean,result?:R}>{
 const tick=options.tick??control,order:string[]=[],byName=new Map<string,HeldCountPayload<T>>(),dependencies=new Map<string,readonly string[]>()
 for(const row of held){tick();if(byName.has(row.id))throw Error('duplicate held payload');order.push(row.id);byName.set(row.id,row);dependencies.set(row.id,row.premises)}
 const plan=greatestClosedCountFamily(order,dependencies,options)
 let containsTarget=false;for(const name of plan.members){tick();if(name===target)containsTarget=true}
 if(containsTarget)return {plan,targetInFamily:true,route:'legacy',submitted:true,result:callbacks.legacy()}
 if(!plan.members.length)return {plan,targetInFamily:false,route:'empty',submitted:false}
 const selected:HeldCountPayload<T>[]=[];for(const name of plan.members){tick();selected.push(byName.get(name)!)}
 if(!callbacks.reserve(selected))return {plan,targetInFamily:false,route:'unfunded',submitted:false}
 return {plan,targetInFamily:false,route:'subset',submitted:true,result:callbacks.submit(selected)}
}
