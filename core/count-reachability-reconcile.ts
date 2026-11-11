// Untrusted scheduling only. The supplied names must come from the original
// reachable-replay ledger, never from SAT or a failed finite search.
import {type countPrerequisiteComponents} from './count-prerequisite-components.ts'
type Queue=ReturnType<typeof countPrerequisiteComponents>
export function withoutReachableRejections<T extends {name:string}>(family:readonly T[],rejected:readonly string[]):T[]{
 const denied=new Set(rejected);return family.filter(law=>!denied.has(law.name))
}
export function reconcileReachableRejections<S>(queue:Queue,members:ReadonlySet<string>,rejected:readonly string[],scopes:Map<string,S>,committed:Set<string>,active?:string){
 const failed=new Set(queue.failed()),names=[...new Set(rejected)].filter(name=>members.has(name)&&!failed.has(name))
 if(!names.length)return {rejected:names,invalidated:[] as readonly string[],interrupted:false}
 // Do not finish a stale current proposal after rejecting one of its offered
 // premises. Park it first, then let the queue rebuild in the reduced context.
 if(active!==undefined)queue.finish(active,{kind:'unknown',reason:'reachable rejection changed context'})
 const invalidated=queue.reject(names)
 for(const name of [...names,...invalidated]){scopes.delete(name);committed.delete(name)}
 return {rejected:names,invalidated,interrupted:active!==undefined}
}
