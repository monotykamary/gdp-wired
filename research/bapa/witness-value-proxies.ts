// Exact syntactic preparation only: none of these proposals is a proof.
import type {C, E, Law} from '../../core/machine.ts'
import type {SeedBindings} from './candidate-seed-restatement.ts'

/** Replace each ghost cell by a universally quantified value guarded by equality
 * to that cell. This is equivalent over all naturals, including empty sorts;
 * it does not assert that a relation row exists. The ordinary restater still
 * has to translate the result and the native kernel must check the proposal. */
export function abstractWitnessValues(laws: Law[], bindings: SeedBindings, valueSorts: Record<string,string>): {laws: Law[], bindings: SeedBindings} {
  const maps = {...bindings.maps}, fields = {...bindings.fields}, variables = {...bindings.variables}
  const specs: Record<string,{sort:string, keySort:string, radix:number}> = Object.create(null)
  for (const [name, sort] of Object.entries(valueSorts)) {
    const layout = maps[name]
    if (!layout || layout.sorts.length !== 1 || !layout.sorts[0] || !layout.target || !Number.isSafeInteger(layout.radix) || layout.radix < 2 || !bindings.domains[sort] || !bindings.domains[layout.sorts[0]]) throw Error(`missing or invalid ghost coordinate: ${name}`)
    specs[name] = {sort, keySort:layout.sorts[0], radix:layout.radix}
    delete fields[name]
  }
  const used = new Set<string>([...Object.keys(maps), ...Object.values(maps).map(m=>m.target), ...Object.values(bindings.domains)])
  const collect = (x:unknown):void => {
    if (Array.isArray(x)) {x.forEach(collect);return}
    if (!x || typeof x !== 'object') return
    const o=x as Record<string,unknown>
    if (typeof o.name === 'string') used.add(o.name)
    if (typeof o.forall === 'string') used.add(o.forall)
    if (Array.isArray(o.keys)) for (const k of o.keys) if (typeof k === 'string') used.add(k)
    Object.values(o).forEach(collect)
  }
  collect(laws); Object.keys(variables).forEach(x=>used.add(x))
  let next=0
  const output=laws.map(law=>{
    if (Object.keys(law).some(k=>!['name','forall','keys','holds'].includes(k))) throw Error(`unsupported helper metadata: ${law.name}`)
    const bound=[law.forall,...(law.keys??[])].filter((x):x is string=>!!x)
    if(new Set(bound).size!==bound.length)throw Error(`duplicate binder: ${law.name}`)
    const found=new Map<string,{read:E,name:string}>()
    const visit=(x:unknown):unknown=>{
      if(Array.isArray(x))return x.map(visit)
      if(!x||typeof x!=='object')return x
      const o=x as Record<string,unknown>, spec=specs[String(o.map)]
      if(o.op==='get' && spec){
        const key=o.key as E
        if(!key || key.op!=='var' || Object.keys(key).some(k=>k!=='op' && k!=='name') || !bound.includes(key.name))throw Error(`unbound ghost key: ${String(o.map)}`)
        const id=JSON.stringify([o.map,key.name]); let cell=found.get(id)
        if(!cell){let name:string;do{name=`seed$ghost$value$${next++}`}while(used.has(name));used.add(name)
          cell={read:{op:'get',map:String(o.map),key:{...key}},name}; found.set(id,cell)
          variables[name]={sort:spec.sort,radix:spec.radix}
        }
        return {op:'var',name:cell.name}
      }
      return Object.fromEntries(Object.entries(o).map(([k,v])=>[k,visit(v)]))
    }
    const body=visit(law.holds) as C, cells=[...found.values()], names=[...bound,...cells.map(c=>c.name)]
    const holds:C=cells.length?{op:'or',xs:[...cells.map(({read,name}):C=>({op:'not',x:{op:'=',a:read,b:{op:'var',name}}})),body]}:body
    return {...law,...(names.length?{forall:names[0],keys:names.slice(1)}:{}),holds}
  })
  return {laws:output,bindings:{...bindings,maps,fields,variables}}
}
