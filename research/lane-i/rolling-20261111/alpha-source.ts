// Research-only structural alpha audit, not a proof rule or an interpreter.
// Only declared lexical binders are renamed. All free names, operators, keys,
// scalar values, field presence and array order remain exact. Fresh names are
// absent from both inputs, so substitution cannot capture a free variable.
export type AlphaKind = 'value' | 'count' | 'law' | 'machine'
export function alphaEqual(a: unknown, b: unknown, kind: AlphaKind = 'value'): boolean {
 let prefix = '$I_alpha$'
 const input = JSON.stringify([a,b]); while (input.includes(prefix)) prefix = '$' + prefix
 const canonical = (root: unknown) => {
  let next = 0
  const visit = (value: any, scope = new Map<string,string>(), context: AlphaKind = 'value'): any => {
   if (!value || typeof value !== 'object') return value
   if (Array.isArray(value)) return value.map(v => visit(v,scope))
   const bind = (names: unknown[]) => {
    if (names.some(n => typeof n !== 'string') || new Set(names).size !== names.length) throw Error('invalid alpha binder')
    const inner = new Map(scope), renamed = names.map(n => { const fresh = prefix + next++; inner.set(n as string,fresh); return fresh })
    return {inner,renamed}
   }
   if (value.op === 'var') return Object.fromEntries(Object.keys(value).sort().map(k => [k,k === 'name' ? scope.get(value.name) ?? value.name : visit(value[k],scope)]))
   if (value.op === 'all') {
    const {inner,renamed} = bind([value.key,...(value.keys ?? [])])
    return Object.fromEntries(Object.keys(value).sort().map(k => [k,k === 'key' ? renamed[0] : k === 'keys' ? renamed.slice(1) : visit(value[k],k === 'c' ? inner : scope)]))
   }
   if (typeof value.each === 'string' && Object.keys(value).every(k => k === 'each' || k === 'value')) {
    const {inner,renamed} = bind([value.each])
    return Object.fromEntries(Object.keys(value).sort().map(k => [k,k === 'each' ? renamed[0] : visit(value[k],inner)]))
   }
   if (context === 'count') {
    const names = [value.j,value.key,...(value.lo === undefined ? [] : [value.lo])], {inner,renamed} = bind(names)
    const belowScope = new Map(scope); belowScope.set(value.j,renamed[0]!)
    return Object.fromEntries(Object.keys(value).sort().map(k => [k,k === 'j' ? renamed[0] : k === 'key' ? renamed[1] : k === 'lo' ? renamed[2] : visit(value[k],k === 'body' ? inner : k === 'below' ? belowScope : scope)]))
   }
   if (context === 'law' && value.forall !== undefined) {
    const {inner,renamed} = bind([value.forall,...(value.keys ?? [])])
    return Object.fromEntries(Object.keys(value).sort().map(k => [k,k === 'forall' ? renamed[0] : k === 'keys' ? renamed.slice(1) : visit(value[k],k === 'holds' ? inner : scope)]))
   }
   return Object.fromEntries(Object.keys(value).sort().map(k => [k,context === 'machine' && k === 'counts' && value[k] ? Object.fromEntries(Object.keys(value[k]).sort().map(name => [name,visit(value[k][name],scope,'count')])) : visit(value[k],scope)]))
  }
  return JSON.stringify(visit(root,new Map(),kind))
 }
 return canonical(a) === canonical(b)
}
