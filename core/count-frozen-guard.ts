// Scalar search guards use the same quantified-flag aliases as countedObligations.
// This is preprocessing, not a proof rule or an additional hypothesis.
import {type C,n,same,walkOnce,x} from './machine.ts'
import {substC} from '../kernel/kernel.ts'
export function inlineFrozenGuard(flags:Readonly<Record<string,C>>,root:string):C{
 const memo=new Map<string,C>(),visiting=new Set<string>()
 const expand=(name:string):C=>{
  const old=memo.get(name);if(old)return old
  if(visiting.has(name))throw Error('cyclic guard flag '+name)
  const raw=Object.hasOwn(flags,name)?flags[name]:undefined
  if(!raw)throw Error('missing guard flag '+name)
  if(raw.op==='all'){const value=same(x('?'+name),n(1));memo.set(name,value);return value}
  visiting.add(name)
  const dependencies:Record<string,C>={}
  walkOnce(raw,(node:any)=>{if(node.op==='flag')dependencies[node.name]=expand(node.name)})
  const value=substC(raw,{vars:{},maps:{},flags:dependencies})
  visiting.delete(name);memo.set(name,value)
  return value
 }
 return expand(root)
}
