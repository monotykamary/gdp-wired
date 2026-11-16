// Canonical weighted frontier over the ACTUAL retained tree. 1=yes, 0=no.
// Weight is a deterministic structural proxy, NOT RSS or native search work.
import type {Tree,CountCert} from '../../kernel/kernel.ts'
export type Piece={address:string,weight:string}
export type Frontier={schema:'final29-frontier/v1',proxy:'structure-v1',limit:string,contextWeight:string,pieces:Piece[]}
const natural=(v:bigint)=>{if(v<0n)throw Error('negative structural weight');return v}
function scalarSize(x:unknown):bigint {
  if(x===null||x===undefined)return 1n
  if(typeof x==='string')return 1n+BigInt(x.length)
  if(typeof x==='number'||typeof x==='boolean'||typeof x==='bigint')return 1n
  throw Error('non-data structural value')
}
export function structuralWeight(root:unknown):bigint {
  let weight=0n;const seen=new Set<object>(),stack:unknown[]=[root]
  while(stack.length) {
    const x=stack.pop()
    if(x===null||typeof x!=='object'){weight+=scalarSize(x);continue}
    if(seen.has(x))continue;seen.add(x);weight++
    if(x instanceof Map){for(const [k,v]of x)stack.push(k,v);continue}
    if(x instanceof Set){for(const v of x)stack.push(v);continue}
    for(const key of Reflect.ownKeys(x)) {
      if(typeof key!=='string')throw Error('symbol structural property')
      const d=Object.getOwnPropertyDescriptor(x,key)!
      if(!('value'in d))throw Error('accessor structural property')
      weight+=1n+BigInt(key.length);stack.push(d.value)
    }
  }
  return weight
}
function weights(root:Tree):Map<Tree,bigint> {
  const out=new Map<Tree,bigint>(),active=new Set<Tree>(),todo:[Tree,boolean][]=[[root,false]]
  while(todo.length) {
    const [node,done]=todo.pop()!
    if(done){active.delete(node);out.set(node,'split'in node?1n+structuralWeight(node.split)+out.get(node.yes)!+out.get(node.no)!:structuralWeight(node));continue}
    if(active.has(node))throw Error('cyclic certificate tree')
    if(out.has(node))continue
    if(!node||typeof node!=='object'||(!('split'in node)&&!('leaf'in node)))throw Error('invalid certificate tree')
    active.add(node);todo.push([node,true])
    if('split'in node)todo.push([node.no,false],[node.yes,false])
  }
  return out
}
export function makeFrontier(root:Tree,limit:bigint,contextWeight:bigint):Frontier {
  if(limit<=0n)throw Error('positive piece limit required');natural(contextWeight)
  const all=weights(root),pieces:Piece[]=[],todo:[Tree,string][]=[[root,'']]
  while(todo.length) {
    const [node,address]=todo.pop()!,weight=all.get(node)!+contextWeight+2n*BigInt(address.length)
    if(weight<=limit)pieces.push({address,weight:String(weight)})
    else if('split'in node)todo.push([node.no,address+'0'],[node.yes,address+'1'])
    else throw Error(`oversized leaf/context at ${address}; separate reviewed decomposition required`)
  }
  return {schema:'final29-frontier/v1',proxy:'structure-v1',limit:String(limit),contextWeight:String(contextWeight),pieces}
}
// Independent coverage walk. Does not trust generator node weights, leaf count,
// claimed paths or a fixed 2^depth table. Stops at each real leaf, never below it.
export function verifyFrontier(root:Tree,frontier:Frontier):void {
  if(frontier.schema!=='final29-frontier/v1'||frontier.proxy!=='structure-v1'||!/^[1-9][0-9]*$/.test(frontier.limit)||!/^(0|[1-9][0-9]*)$/.test(frontier.contextWeight))throw Error('invalid frontier header')
  const limit=BigInt(frontier.limit),context=BigInt(frontier.contextWeight),byAddress=new Map<string,Piece>()
  for(const p of frontier.pieces) {
    if(!/^[01]*$/.test(p.address)||!/^[1-9][0-9]*$/.test(p.weight)||byAddress.has(p.address))throw Error('invalid or duplicate frontier address')
    byAddress.set(p.address,p)
  }
  if(!byAddress.size)throw Error('empty frontier')
  for(const address of byAddress.keys())for(let n=0;n<address.length;n++)if(byAddress.has(address.slice(0,n)))throw Error('frontier is not prefix-free')
  // Recompute subtree weights independently, preserving multiplicity of shared
  // subtree occurrences (the proof checks an occurrence on each distinct path).
  const score=(start:Tree):bigint=>{
    let value=0n;const todo:Tree[]=[start],active=new Set<Tree>(),walk:[Tree,boolean][]=[]
    walk.push([start,false]);void todo
    while(walk.length){const [n,leave]=walk.pop()!;if(leave){active.delete(n);continue}if(active.has(n))throw Error('cyclic certificate tree');active.add(n);walk.push([n,true]);if('split'in n){value+=1n+structuralWeight(n.split);walk.push([n.no,false],[n.yes,false])}else if('leaf'in n)value+=structuralWeight(n);else throw Error('invalid tree')}
    return value
  }
  let consumed=0;const todo:[Tree,string][]=[[root,'']],order:string[]=[]
  while(todo.length) {
    const [node,address]=todo.pop()!,p=byAddress.get(address),weight=score(node)+context+2n*BigInt(address.length)
    if(p){if(weight>limit||p.weight!==String(weight))throw Error('frontier weight mismatch');consumed++;order.push(address);continue}
    if(weight<=limit)throw Error('noncanonical over-split frontier')
    if(!('split'in node))throw Error('uncovered real leaf or oversized context')
    todo.push([node.no,address+'0'],[node.yes,address+'1'])
  }
  if(consumed!==byAddress.size||order.some((a,i)=>a!==frontier.pieces[i]?.address))throw Error('extra, below-leaf, or noncanonical ordered frontier address')
}
export function certificateTrees(cert:CountCert):{role:string,tree:Tree}[] {
  return [{role:'main',tree:cert.tree},...(cert.lemmas??[]).map((x,i)=>({role:`lemma/${i}`,tree:x.tree})),
    ...(cert.monos??[]).map((x,i)=>({role:`mono/${i}`,tree:x.tree})),...(cert.lins??[]).map((x,i)=>({role:`lin/${i}`,tree:x.tree}))]
}
