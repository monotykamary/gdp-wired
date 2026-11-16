// Row-based proposals, NOT a semantic alias for last-written ghost witnesses.
// Empty-row/default cases are deliberately not covered. The original public
// goal is unchanged and every resulting candidate still needs native checking.
import type {C,E,Law,Machine} from '../../core/machine.ts'
import type {SeedBindings} from './candidate-seed-restatement.ts'
export type FieldSeedBinding={relation:string,keyPositions:number[],valuePosition:number}
export type FieldRowAudit={kind:'row-guarded-proposal',absence:'not-covered',fields:string[],rows:number}
export function proposeFieldRows(law:Law,source:Machine|undefined,target:Machine,bindings:SeedBindings):{law:Law,audit?:FieldRowAudit} {
 const specs=bindings.fields??{}, bound=[law.forall,...(law.keys??[])].filter((x):x is string=>!!x)
 const used=new Set([...bound,...target.params,...target.inputs,...Object.keys(target.state)])
 const fresh:string[]=[], fields=new Set<string>(), rows=new Map<string,{relation:string,coords:E[],radix:number}>()
 const variable=():E=>{let name=`seed$field$${fresh.length}`;while(used.has(name))name+='$';used.add(name);fresh.push(name);return {op:'var',name}}
 const visit=(value:unknown):unknown=>{
  if(Array.isArray(value))return value.map(visit)
  if(!value||typeof value!=='object')return value
  const o=value as Record<string,unknown>, name=String(o.map), cfg=specs[name]
  if(o.op==='get'&&cfg){
   if(!source||!Object.hasOwn(source.maps??{},name))throw Error(`field source declaration absent: ${name}`)
   const layout=bindings.maps[cfg.relation], key=o.key as E
   if(!layout||!Object.hasOwn(target.maps??{},layout.target)||!layout.sorts.length)throw Error(`field relation not mapped: ${name}`)
   if(!Number.isSafeInteger(layout.radix)||layout.radix<2)throw Error(`invalid field radix: ${name}`)
   const declared=target.relations?.[layout.target]
   if(declared&&JSON.stringify(declared)!==JSON.stringify(layout.sorts))throw Error(`field relation layout mismatch: ${name}`)
   if(cfg.keyPositions.length!==1||!key||key.op!=='var'||!bound.includes(key.name))throw Error(`unsupported field selector: ${name}`)
   const kp=cfg.keyPositions[0]!,vp=cfg.valuePosition
   if(!Number.isInteger(kp)||!Number.isInteger(vp)||kp<0||vp<0||kp>=layout.sorts.length||vp>=layout.sorts.length||kp===vp)throw Error(`invalid field coordinate: ${name}`)
   for(const sort of layout.sorts)if(!target.params.includes(bindings.domains[sort]??''))throw Error(`missing field domain: ${sort}`)
   const id=JSON.stringify([cfg.relation,cfg.keyPositions,key])
   let row=rows.get(id)
   if(!row){row={relation:cfg.relation,coords:layout.sorts.map((_,i)=>i===kp?key:variable()),radix:layout.radix};rows.set(id,row)}
   fields.add(name);return row.coords[vp]!
  }
  return Object.fromEntries(Object.entries(o).map(([k,v])=>[k,visit(v)]))
 }
 const holds=visit(law.holds) as C
 if(!rows.size)return {law}
 const guards:C[]=[...rows.values()].map(row=>{
  const key=row.coords.slice(1).reduce<E>((a,b)=>({op:'add',a:{op:'mul',k:row.radix,a},b}),row.coords[0]!)
  return {op:'not',x:{op:'<=',a:{op:'const',value:1},b:{op:'get',map:row.relation,key}}}
 })
 const all=[...bound,...fresh]
 return {law:{...law,forall:all[0],keys:all.slice(1),holds:{op:'or',xs:[...guards,holds]}},audit:{kind:'row-guarded-proposal',absence:'not-covered',fields:[...fields],rows:rows.size}}
}
