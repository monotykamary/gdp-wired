import type {C,E,Law,Machine} from '../../core/machine.ts'
import type {ProofOutputNode} from '../../core/proof-output.ts'
import type {GenericLiftSource} from '../lift/source.ts'
import {sourceStructure} from '../lift/source.ts'

/** Structural ABI shared by native and historical capsules. No schema or
 * protocol discriminant is used to choose this transport. */
export type RadixSimulationBundle = {
  original:{machine:Machine,laws:Law[]}
  verdict:{proven:boolean,checked:boolean}
  proof?:ProofOutputNode
  final?:unknown
}
export type RadixLayout={map:string,arity:number}
export type RadixShapePlan={
  radix:number
  layouts:RadixLayout[]
  producer:Extract<ProofOutputNode,{kind:'usual'}>
  sumMachine:Machine
  publicLawIndices:number[]
  booleanEntries:{map:string,index:number}[]
}
export class UnsupportedRadixSimulation extends Error {
  constructor(message:string){super(message);this.name='UnsupportedRadixSimulation'}
}
const eq=(a:unknown,b:unknown)=>sourceStructure(a)===sourceStructure(b)
const fail=(s:string):never=>{throw new UnsupportedRadixSimulation(s)}
const object=(x:unknown):x is Record<string,unknown>=>!!x&&typeof x==='object'&&!Array.isArray(x)
function walk(x:unknown,f:(x:Record<string,unknown>)=>void):void{
  if(Array.isArray(x)){x.forEach(y=>walk(y,f));return}
  if(!object(x))return
  f(x);Object.values(x).forEach(y=>walk(y,f))
}
function tupleParts(e:E):E[]{return e.op==='tup'?[e.a,...tupleParts(e.b)]:[e]}
function packed(e:E):{radix:number,parts:E[]}|null{
  if(e.op!=='add')return null
  if(e.a.op==='mul'&&Number.isSafeInteger(e.a.k)&&e.a.k>1){
    const nested=packed(e.a.a)
    if(nested&&nested.radix===e.a.k)return {radix:e.a.k,parts:[...nested.parts,e.b]}
    return {radix:e.a.k,parts:[e.a.a,e.b]}
  }
  // Historical flattened three-component polynomial.
  if(e.a.op==='add'&&e.a.a.op==='mul'&&e.a.b.op==='mul'&&e.a.a.k===e.a.b.k*e.a.b.k&&e.a.b.k>1)
    return {radix:e.a.b.k,parts:[e.a.a.a,e.a.b.a,e.b]}
  return null
}
function keys(m:Machine,laws:Law[]):{map:string,key:E}[]{
  const result:{map:string,key:E}[]=[]
  walk([m,laws],n=>{if(n.op==='get'&&typeof n.map==='string'&&object(n.key))result.push({map:n.map,key:n.key as E})})
  for(const [map,w]of Object.entries(m.step.maps??{}))if('key'in w)result.push({map,key:w.key})
  return result
}
function plainCondition(c:C,radix:number,params:readonly string[]):unknown{
  if((c.op==='<'||c.op==='<=')&&(c.b.op==='const'&&c.b.value===radix||c.b.op==='var'&&params.includes(c.b.name)))return {op:'and',xs:[]}
  if(c.op==='and'||c.op==='or'){
    const xs=c.xs.map(x=>plainCondition(x,radix,params)).flatMap(x=>object(x)&&x.op===c.op&&Array.isArray(x.xs)?x.xs:[x])
    const kept=c.op==='and'?xs.filter(x=>!eq(x,{op:'and',xs:[]})):xs
    return kept.length===1?kept[0]:{op:c.op,xs:kept}
  }
  if(c.op==='not')return {op:'not',x:plainCondition(c.x,radix,params)}
  return c
}
function booleanBound(l:Law):string|null{
  const c=l.holds
  if(l.keys?.length||l.some?.length||l.ex||!l.forall||c.op!=='<='||c.a.op!=='get'||c.b.op!=='const'||c.b.value!==1||c.a.key.op!=='var'||c.a.key.name!==l.forall)return null
  return c.a.map
}

/** Data-only shape derivation. A noncandidate returns null. Once packed-key
 * evidence exists, ambiguity or missing proof data is a hard failure, never a
 * fallback to another route or to a fixed-bound theorem. */
export function planRadixSimulation(bundle:RadixSimulationBundle,source:GenericLiftSource):RadixShapePlan|null{
  if(source.schema!=='gdp-lift-source/v1')throw Error('invalid provided source ABI')
  sourceStructure(source)
  if(!bundle.proof)return null
  const leaves:Extract<ProofOutputNode,{kind:'usual'}>[]=[],sumSources:Machine[]=[]
  const visited=new Set<ProofOutputNode>(),active=new Set<ProofOutputNode>();let counted=0
  const record=(m:unknown)=>{if(object(m)&&object(m.sums)&&Object.keys(m.sums).length&&object(m.step)&&Array.isArray(m.inputs))sumSources.push(m as Machine)}
  const visit=(n:ProofOutputNode):void=>{
    if(active.has(n))fail('cyclic radix provenance')
    if(visited.has(n))return
    active.add(n)
    if(n.kind==='derived'){
      if(!n.parents.length||n.parents.some(x=>!x))fail('incomplete radix provenance')
      if(object(n.context)){record(n.context.original);if(object(n.context.original))record(n.context.original.machine)}
      for(const p of n.parents)visit(p!)
    }else if(n.kind==='usual'){leaves.push(n);record(n.machine)}else if(n.kind==='counted'){counted++}
    active.delete(n);visited.add(n)
  }
  visit(bundle.proof)
  record(bundle.original.machine)
  const allKeys=leaves.flatMap(n=>keys(n.machine,n.laws))
  const packedKeys=allKeys.flatMap(x=>{const p=packed(x.key);return p?[{...x,...p}]:[]})
  if(!packedKeys.length)return null
  if(!bundle.verdict?.proven||!bundle.verdict.checked)fail('unverified radix candidate')
  if(leaves.length!==1||counted)fail('radix transport needs a unique complete usual producer without counted mixing')
  const producer=leaves[0]!
  if(Object.keys(source.machine.sums??{}).length)fail('provided source SUM semantics are unsupported; refusing to drop declarations')
  for(const m of [source.machine,producer.machine])if(m.history||Object.keys(m.counts??{}).length||Object.keys(m.fns??{}).length||Object.keys(m.leasts??{}).length)fail('unsupported radix machine extension')
  if(source.machine.facts?.length||producer.machine.facts?.length)fail('radix source facts require explicit checked correspondence')
  const radices=[...new Set(packedKeys.map(k=>k.radix))]
  if(radices.length!==1)fail('ambiguous packed-key radix')
  const radix=radices[0]!,layouts:RadixLayout[]=[]
  for(const k of packedKeys){
    const prior=layouts.find(l=>l.map===k.map)
    if(prior&&prior.arity!==k.parts.length)fail('inconsistent packed-key arity for '+k.map)
    if(!prior)layouts.push({map:k.map,arity:k.parts.length})
  }
  const sourceKeys=keys(source.machine,source.laws)
  for(const layout of layouts){
    const typed=sourceKeys.filter(k=>k.map===layout.map&&k.key.op==='tup')
    if(!typed.length)fail('provided source has no tuple-key evidence for '+layout.map)
    if(typed.some(k=>tupleParts(k.key).length!==layout.arity))fail('source tuple-key arity mismatch for '+layout.map)
  }
  if(!producer.laws.length||new Set(producer.laws.map(l=>l.name)).size!==producer.laws.length)fail('empty or ambiguous radix family')
  const expected=producer.laws.flatMap(l=>[l.name+' @start',l.name+' @step'])
  // Primary trees are goal-indexed. Instances are law-indexed and an absent
  // law entry denotes the empty set in the unchanged kernel obligations API.
  if(expected.some(k=>!Object.hasOwn(producer.proof.trees,k)))fail('missing retained radix primary obligation')
  const uniqueSums=sumSources.filter((m,i)=>sumSources.findIndex(q=>eq(q,m))===i)
  // A high-level producer is authoritative. Earlier provenance contexts may
  // use different local row-binder names and are not competing declarations.
  const direct=Object.keys(producer.machine.sums??{}).length?producer.machine:undefined
  if(!direct&&uniqueSums.length!==1)fail(uniqueSums.length?'ambiguous high-level SUM declaration source':'capsule lacks reconstructible high-level SUM declarations')
  const sumMachine=direct??uniqueSums[0]!
  for(const [name,d]of Object.entries(sumMachine.sums??{})){
    let unsupported=false
    walk(d.term,n=>{if(n.op==='get'&&(!object(n.key)||n.key.op!=='var'||n.key.name!==d.key))unsupported=true})
    if(unsupported)fail('SUM integrand is not whole-address: '+name)
  }
  const publicLawIndices=source.laws.map(l=>{
    if(l.some?.length||l.ex||l.witness||l.stated||l.finite)fail('unsupported radix public law quantification')
    const shape=plainCondition(l.holds,radix,source.machine.params)
    const found=producer.laws.flatMap((p,i)=>p.forall===l.forall&&eq(p.keys??[],l.keys??[])&&eq(plainCondition(p.holds,radix,[]),shape)?[i]:[])
    if(found.length!==1)fail('missing or ambiguous public-law shape: '+l.name)
    return found[0]!
  })
  const booleanEntries=producer.laws.flatMap((l,index)=>{const map=booleanBound(l);return map?[{map,index}]:[]})
  for(const layout of layouts)if(!booleanEntries.some(e=>e.map===layout.map))fail('packed map lacks a checked Boolean family entry: '+layout.map)
  return {radix,layouts,producer,sumMachine,publicLawIndices,booleanEntries}
}
