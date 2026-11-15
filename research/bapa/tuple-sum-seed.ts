// Untrusted finite sub-sum proposals, NOT a declaration of a global tuple total.
import type {C, E, Law} from '../../core/machine.ts'

export type TupleSumSeed = {sourceMap:string, targetMap:string, arity:number}
export type TupleSumProjection = TupleSumSeed & {sourceSum:string, kind:'finite-subsum', points:2, globalTotal:false}

/** For a positive LHS bound on one tuple total, propose one-cell and two-distinct-cell
 * bounds. All coordinates stay universally quantified; no finite radix or size cap
 * is a domain restriction. These are necessary consequences, not an equivalent
 * replacement for the total (three unit cells and budget two are a counterexample).
 * Each resulting law must independently survive the public prover's kernel check. */
export function proposeTupleSumCells(law:Law, sums:Record<string,TupleSumSeed>, reserved:Iterable<string> = []):{law:Law,audit?:TupleSumProjection} {
  const names=new Set<string>()
  const collect=(x:unknown):void=>{
    if(Array.isArray(x)){x.forEach(collect);return}
    if(!x||typeof x!=='object')return
    const o=x as Record<string,unknown>
    if(o.op==='var')names.add(String(o.name))
    Object.values(o).forEach(collect)
  }
  collect(law.holds)
  const active=Object.keys(sums).filter(n=>names.has(n))
  if(!active.length)return {law}
  if(active.length!==1)throw Error('tuple SUM projection needs one tuple total per law')
  const sourceSum=active[0]!, seed=sums[sourceSum]!
  if(!Number.isSafeInteger(seed.arity)||seed.arity<2)throw Error('invalid tuple SUM arity')
  const reads=(x:unknown):boolean=>!!x&&typeof x==='object'&&(Array.isArray(x)?x.some(reads):((x as any).op==='var'&&(x as any).name===sourceSum)||Object.values(x).some(reads))
  const positive=(e:E):boolean=>e.op==='var'||e.op==='const'&&Number.isSafeInteger(e.value)&&e.value>=0
    ||e.op==='add'&&positive(e.a)&&positive(e.b)
    ||e.op==='mul'&&Number.isSafeInteger(e.k)&&e.k>=0&&positive(e.a)
  if(law.holds.op!=='<='||reads(law.holds.b)||!positive(law.holds.a))throw Error('tuple SUM projection needs a positive linear LHS <= a tuple-SUM-free RHS')
  for(const n of reserved)names.add(n)
  for(const n of [law.forall,...(law.keys??[])])if(n)names.add(n)
  const fresh=(point:number,coordinate:number):string=>{let n=`seed$sum$${point}$${coordinate}`;while(names.has(n))n+='$';names.add(n);return n}
  const points=[0,1].map(p=>Array.from({length:seed.arity},(_,i)=>fresh(p,i)))
  const tuple=(xs:string[]):E=>xs.length===1?{op:'var',name:xs[0]!}:{op:'tup',a:{op:'var',name:xs[0]!},b:tuple(xs.slice(1))}
  const cells=points.map(xs=>({op:'get',map:seed.sourceMap,key:tuple(xs)} as E))
  const replace=(x:unknown,term:E):unknown=>{
    if(Array.isArray(x))return x.map(v=>replace(v,term))
    if(!x||typeof x!=='object')return x
    const o=x as Record<string,unknown>
    if(o.op==='var'&&o.name===sourceSum)return term
    return Object.fromEntries(Object.entries(o).map(([k,v])=>[k,replace(v,term)]))
  }
  const one=replace(law.holds,cells[0]!) as C
  const two=replace(law.holds,{op:'add',a:cells[0]!,b:cells[1]!}) as C
  const distinct:C={op:'or',xs:points[0]!.map((n,i)=>({op:'not',x:{op:'=',a:{op:'var',name:n},b:{op:'var',name:points[1]![i]!}}}))}
  const binders=[law.forall,...(law.keys??[]),...points.flat()].filter((n):n is string=>!!n)
  return {law:{...law,forall:binders[0],keys:binders.slice(1),holds:{op:'and',xs:[one,{op:'or',xs:[{op:'not',x:distinct},two]}]}},
    audit:{...seed,sourceSum,kind:'finite-subsum',points:2,globalTotal:false}}
}
