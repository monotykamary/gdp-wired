// Reserved surface identities cannot equal user declarations. Kernel.scope also
// rejects reserved *bound* names, so the final DSL boundary alpha-encodes them
// to fresh plain names. No kernel code or trusted axiom is changed.
export const binder=(kind:string,index:number):string=>`?${kind}${index}`
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
  const check=(x:unknown,scope:Set<string>):void=>{
    if(!x||typeof x!=='object')return
    if(Array.isArray(x)){x.forEach(v=>check(v,scope));return}
    const node=x as Record<string,unknown>,inner=new Set([...scope,...bindings(node)])
    if(node.op==='var'&&typeof node.name==='string'&&reservedName(node.name)&&!inner.has(node.name)&&!allowed.has(node.name))
      throw Error(`law or rule reads free reserved name ${node.name}`)
    for(const [key,v] of Object.entries(node))check(v,node.op==='all'&&key==='witness'?scope:inner)
  }
  check(value,new Set())
}
// Collect first: every user/free name, even a later occurrence, excludes an
// alias. Replace only exact identities, never substrings or rendered code.
export function encodeBinders<T>(value:T,declared:string[],allowedFree:string[]=[]):T {
  const used=new Set(declared),boundNames=new Set<string>()
  const collect=(x:unknown):void=>{
    if(typeof x==='string'){used.add(x);return}
    if(!x||typeof x!=='object')return
    if(Array.isArray(x)){x.forEach(collect);return}
    const node=x as Record<string,unknown>
    for(const n of bindings(node))if(n.startsWith('?')){
      if(!/^\?(?:k|key|s|some)\d+(?:\$.*)?$/.test(n))throw Error(`unowned reserved binder ${n}`)
      boundNames.add(n)
    }
    for(const [k,v] of Object.entries(node)){used.add(k);collect(v)}
  }
  collect(value);guardReserved(value,allowedFree)
  if(!boundNames.size)return value
  const names=new Map<string,string>();let next=0
  for(const n of boundNames){
    if(names.has(n))continue
    // Integer witnesses are one signed value encoded by stem/stem$neg.
    // Search/decoding and Lean export use this relationship, so rename the
    // whole group together and exclude collisions with either fresh member.
    const stem=n.endsWith('$neg')?n.slice(0,-4):n
    const group=[stem,`${stem}$neg`].filter(part=>boundNames.has(part))
    let fresh:string
    do{fresh=`gdp$bound$${++next}`}while(used.has(fresh)||group.some(part=>used.has(fresh+part.slice(stem.length))))
    for(const part of group){const alias=fresh+part.slice(stem.length);used.add(alias);names.set(part,alias)}
  }
  const rewrite=(x:unknown):unknown=>{
    if(typeof x==='string')return names.get(x)??x
    if(!x||typeof x!=='object')return x
    if(Array.isArray(x))return x.map(rewrite)
    // Runtime capabilities / Maps / Sets are not syntax trees.
    if(Object.getPrototypeOf(x)!==Object.prototype&&Object.getPrototypeOf(x)!==null)return x
    return Object.fromEntries(Object.entries(x).map(([k,v])=>[names.get(k)??k,rewrite(v)]))
  }
  return rewrite(value) as T
}
