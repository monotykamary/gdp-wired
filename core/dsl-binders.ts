// Private generated identities carry provenance in memory, not in their spelling.
// At the public machine/law boundary retain the historical readable name unless
// it collides with a declared or free identifier. Symbols never enter JSON/Lean.
const origin = Symbol('generated variable')
const issued = new Map<string,string>()
export const internalName=(token:string,legacy:string):string=>{issued.set(token,legacy);return token}
export const binder=(kind:string,index:number):string=>internalName(`?${kind}${index}`,`${kind}$${index}`)
const identity=(name:string):{root:string,legacy:string,suffix:string}|undefined=>{
  const end=name.search(/[.$]/),root=end<0?name:name.slice(0,end),legacy=issued.get(root)
  return legacy===undefined?undefined:{root,legacy,suffix:name.slice(root.length)}
}
export function variable(name:string):{op:'var',name:string} {
  const out={op:'var' as const,name}
  if(identity(name))Object.defineProperty(out,origin,{value:true,enumerable:true})
  return out
}
// Only generator sites may issue this mark; a matching name is not provenance.
export function generatedVariable(name:string):{op:'var',name:string} {
  const out={op:'var' as const,name}
  Object.defineProperty(out,origin,{value:true,enumerable:true})
  return out
}
export function copyVariable<T extends object>(from:object,to:T):T {
  if((from as Record<symbol,unknown>)[origin]) {
    Object.defineProperty(to,origin,{value:true,enumerable:true})
    const a=(from as {name?:unknown}).name,b=(to as {name?:unknown}).name
    // Composition prefixes an issued identity. Preserve its readable alias too,
    // but only a marked source node can authorize this renamed identity.
    if(typeof a==='string'&&typeof b==='string'&&b.endsWith(a)) {
      const id=identity(a),prefix=b.slice(0,b.length-a.length)
      if(id&&prefix)internalName(prefix+id.root,prefix+id.legacy)
    }
  }
  return to
}
export const reservedName=(name:string):boolean=>name==='1'||/[*[\],:#?~'⟦⟧⟨⟩|]/.test(name)
export function plainDeclaration(what:string,name:string):void {
  if(reservedName(name))throw new Error(`${what}: the name ${name} is reserved (1, or * [ ] , : # ? ~ ' ⟦ ⟧ ⟨ ⟩ |)`)
}
const bindings=(node:Record<string,unknown>):string[]=>[
  ...(node.op==='all'&&typeof node.key==='string'?[node.key,...Array.isArray(node.keys)?node.keys as string[]:[]]:[]),
  ...(typeof node.forall==='string'?[node.forall,...Array.isArray(node.keys)?node.keys as string[]:[]]:[]),
  ...(typeof node.each==='string'?[node.each]:[]),
  ...(typeof node.key==='string'&&'where' in node&&'by' in node?[node.key]:[]),
  ...(Array.isArray(node.some)?node.some.filter((n):n is string=>typeof n==='string'):[]),
]
export function guardReserved(value:unknown,allowedFree:string[]=[]):void {
  const allowed=new Set(allowedFree)
  const check=(x:unknown):void=>{
    if(!x||typeof x!=='object')return
    if(Array.isArray(x)){x.forEach(check);return}
    const node=x as Record<string,unknown>
    if(node.op==='var'&&typeof node.name==='string'&&reservedName(node.name)&&!allowed.has(node.name)&&!(node as Record<symbol,unknown>)[origin])
      throw Error(`law or rule reads free reserved name ${node.name}`)
    Object.values(node).forEach(check)
  }
  check(value)
}
export function encodeBinders<T>(value:T,declared:string[],allowedFree:string[]=[]):T {
  guardReserved(value,allowedFree)
  const used=new Set([...declared,...allowedFree]),groups=new Map<string,{legacy:string,parts:Set<string>}>()
  const generated=(name:string):boolean=>{
    const id=identity(name)
    if(!id)return false
    const group=groups.get(id.root)??{legacy:id.legacy,parts:new Set<string>()}
    group.parts.add(id.suffix);groups.set(id.root,group);return true
  }
  const collect=(x:unknown):void=>{
    if(!x||typeof x!=='object')return
    if(Array.isArray(x)){x.forEach(collect);return}
    const node=x as Record<string,unknown>
    for(const n of bindings(node))if(!generated(n))used.add(n)
    if(node.op==='var'&&typeof node.name==='string'){
      if(!(node as Record<symbol,unknown>)[origin]||!generated(node.name))used.add(node.name)
    }
    if(typeof node.map==='string')used.add(node.map)
    if(node.op==='flag'&&typeof node.name==='string')used.add(node.name)
    Object.values(node).forEach(collect)
  }
  collect(value)
  if(!groups.size)return value
  const names=new Map<string,string>();let next=0
  for(const [root,group]of groups){
    const suffixes=[...group.parts]
    let fresh=group.legacy
    if(suffixes.some(s=>used.has(fresh+s)))do{fresh=`gdp$bound$${++next}`}while(used.has(fresh)||suffixes.some(s=>used.has(fresh+s)))
    for(const suffix of suffixes){const alias=fresh+suffix;used.add(alias);names.set(root+suffix,alias)}
  }
  const rewrite=(x:unknown):unknown=>{
    if(typeof x==='string')return names.get(x)??x
    if(!x||typeof x!=='object')return x
    if(Array.isArray(x))return x.map(rewrite)
    if(Object.getPrototypeOf(x)!==Object.prototype&&Object.getPrototypeOf(x)!==null)return x
    return Object.fromEntries(Object.entries(x).map(([k,v])=>[names.get(k)??k,rewrite(v)]))
  }
  return rewrite(value) as T
}
