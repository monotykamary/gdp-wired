// Untrusted scheduling only. Missing or cyclic proof metadata never authorizes
// acceptance; the final family is still replayed and checked by the kernel.
export function countClosingNeeds(callers: readonly string[], scopes: ReadonlyMap<string,{premises:readonly {name:string}[]}>): Set<string> {
 const needed=new Set(callers)
 for(const name of needed)for(const premise of scopes.get(name)?.premises??[])needed.add(premise.name)
 return needed
}
