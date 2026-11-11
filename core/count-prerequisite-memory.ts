// Request-local untrusted scheduling state. Reuse never authorizes a proof:
// the unchanged scope replay and native family check still run at completion.
export type CountRememberedScope=Readonly<{owner:Readonly<{name:string}>,premises:readonly Readonly<{name:string}>[]}>
export type CountPrerequisiteMemory<S extends CountRememberedScope>= {
 machine:string, family:string, keys:Map<string,string>,scopes:Map<string,S>,committed:Set<string>,discovered:Set<string>,failed:Set<string>
}
export function prepareCountPrerequisiteMemory<S extends CountRememberedScope>(previous:CountPrerequisiteMemory<S>|undefined,machine:unknown,laws:readonly Readonly<{name:string}>[]){
 const machineKey=JSON.stringify(machine)
 if(typeof machineKey!=='string')throw Error('invalid remembered machine')
 const keys=new Map(laws.map(law=>[law.name,JSON.stringify(law)])),family=JSON.stringify([...keys])
 if(keys.size!==laws.length)throw Error('ambiguous remembered family')
 const state:CountPrerequisiteMemory<S>=previous?.machine===machineKey?previous:{machine:machineKey,family,keys,scopes:new Map(),committed:new Set(),discovered:new Set(),failed:new Set()}
 const invalidated=new Set<string>(state===previous?[]:previous?.scopes.keys())
 if(state===previous){
  for(const [name,scope]of state.scopes)if(keys.get(name)!==state.keys.get(name)||[scope.owner,...scope.premises].some(law=>!keys.has(law.name)||keys.get(law.name)!==state.keys.get(law.name)))invalidated.add(name)
  for(let changed=true;changed;){changed=false;for(const [name,scope]of state.scopes)if(!invalidated.has(name)&&scope.premises.some(law=>invalidated.has(law.name))){invalidated.add(name);changed=true}}
  for(const name of invalidated){state.scopes.delete(name);state.committed.delete(name)}
  for(const name of state.discovered)if(!keys.has(name)||keys.get(name)!==state.keys.get(name))state.discovered.delete(name)
  if(state.family!==family)state.failed.clear()
 }
 state.keys=keys;state.family=family
 return {state,invalidated:[...invalidated]}
}
