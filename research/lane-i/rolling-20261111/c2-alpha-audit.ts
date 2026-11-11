// Research-only audit, never a substitute for strict binding/native replay.
// Preserve every field. Only lexical all.key/keys occurrences inside c bind;
// extra fields (including below/witness) remain in the outer scope.
const object=(value:unknown):Record<string,unknown>=>{
 if(!value||typeof value!=='object'||Array.isArray(value))throw Error('expected an object')
 return value as Record<string,unknown>
}
function bindings(value:unknown):string[]{
 if(!Array.isArray(value)||value.some(name=>typeof name!=='string')||new Set(value).size!==value.length)throw Error('invalid binders')
 return value as string[]
}
function visit(value:unknown,scope:readonly string[]):unknown{
 if(value===undefined)return ['undefined']
 if(value===null||typeof value==='string'||typeof value==='boolean'||typeof value==='number'&&Number.isFinite(value))return ['literal',value]
 if(typeof value!=='object')throw Error('non-JSON AST literal')
 if(Array.isArray(value))return ['array',...value.map(item=>visit(item,scope))]
 const node=object(value),keys=Object.keys(node).sort()
 if(node.op==='all'){
  if(typeof node.key!=='string'||!Object.hasOwn(node,'c'))throw Error('invalid all binder')
  const local=bindings([node.key,...(node.keys===undefined?[]:bindings(node.keys))])
  return ['object',...keys.map(key=>[key,key==='key'?['binder',0]:key==='keys'?['binders',...local.slice(1).map((_,index)=>index+1)]:visit(node[key],key==='c'?[...scope,...local]:scope)])]
 }
 if(node.op==='var'){
  if(typeof node.name!=='string')throw Error('invalid variable')
  const index=scope.lastIndexOf(node.name)
  return ['object',...keys.map(key=>[key,key==='name'?(index<0?['free',node.name]:['bound',scope.length-index-1]):visit(node[key],scope)])]
 }
 return ['object',...keys.map(key=>[key,visit(node[key],scope)])]
}
export const alphaAstKey=(value:unknown):string=>JSON.stringify(visit(value,[]))
// Explicit MapUpdate audit, not a generic interpretation of any `each` field.
// Only step.maps[name].value is bound; extra fields remain in outer scope.
export function alphaStepKey(value:unknown):string{
 const step=object(value)
 const update=(value:unknown):unknown=>{
  const node=object(value)
  if(!Object.hasOwn(node,'each'))return visit(node,[])
  if(typeof node.each!=='string'||!Object.hasOwn(node,'value')||Object.hasOwn(node,'key'))throw Error('invalid each update')
  return ['object',...Object.keys(node).sort().map(key=>[key,key==='each'?['binder',0]:visit(node[key],key==='value'?[node.each as string]:[])])]
 }
 return JSON.stringify(['object',...Object.keys(step).sort().map(key=>[key,key==='maps'?['object',...Object.keys(object(step.maps)).sort().map(name=>[name,update(object(step.maps)[name])])]:visit(step[key],[])])])
}
// Deliberately conservative for Counted: keep j/lo/key and their occurrences
// LITERAL, preserving aliases (including legitimate j===lo), order and base.
// No count-binder alpha theorem is claimed; only nested C.all may alpha-vary.
export function alphaCountKey(value:unknown):string{
 const node=object(value)
 if(typeof node.j!=='string'||typeof node.key!=='string'||!Object.hasOwn(node,'below')||!Object.hasOwn(node,'body')||node.lo!==undefined&&typeof node.lo!=='string')throw Error('invalid counted definition')
 return alphaAstKey(node)
}
export function sameAlphaCounts(a:Record<string,unknown>,b:Record<string,unknown>):boolean{
 const keys=Object.keys(a).sort()
 return JSON.stringify(keys)===JSON.stringify(Object.keys(b).sort())&&keys.every(key=>alphaCountKey(a[key])===alphaCountKey(b[key]))
}
