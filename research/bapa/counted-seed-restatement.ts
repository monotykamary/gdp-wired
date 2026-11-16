// Conservative, untrusted producer declarations; never source assumptions.
import type {Counted, E, Machine} from '../../core/machine.ts'
import type {SeedBindings} from './candidate-seed-restatement.ts'

export type CountSeedBinding = {target:string, jSort:string, keySort:string}
export type CountSeedAudit = {source:string,status:'candidate',target:string,definition:Counted} | {source:string,status:'dropped',reason:string}

// Unary indexed counts only. Packed slices and fixed lo/base encodings are not
// silently promoted to symbolic domains. Unsupported definitions are audited.
export function restateCountSeeds(source:Record<string,Counted>, target:Machine, bindings:SeedBindings, configs:Record<string,CountSeedBinding>):CountSeedAudit[] {
  const reserved=new Set([...Object.keys(target.maps??{}),...Object.keys(target.counts??{}),...(target.inputMaps??[])])
  const used=new Set<string>()
  return [...new Set([...Object.keys(source),...Object.keys(configs)])].map((name):CountSeedAudit=>{
    try {
      const cfg=configs[name]
      if(!cfg)throw Error('count binding not supplied')
      const d=source[name]
      if(!d)throw Error('source count absent')
      if(!cfg.target || reserved.has(cfg.target) || used.has(cfg.target))throw Error('target count name not fresh')
      if(!cfg.jSort || !cfg.keySort || !target.params.includes(bindings.domains[cfg.jSort]??'') || !target.params.includes(bindings.domains[cfg.keySort]??''))throw Error('missing symbolic sort domain')
      if(d.lo!==undefined || d.base!==undefined)throw Error('packed lo/base count unsupported')
      if(!d.j || !d.key || d.j===d.key)throw Error('invalid count binders')
      const params=new Set(target.params), vars=new Set([d.j,d.key,...params])
      const rewrite=(value:unknown):unknown=>{
        if(Array.isArray(value))return value.map(rewrite)
        if(!value || typeof value!=='object')return value
        const o=value as Record<string,unknown>, op=o.op
        if(typeof op!=='string' || !['var','const','add','sub','min','max','mul','prod','if','get','tup','proj','<','<=','=','and','or','not'].includes(op))throw Error(`unsupported count AST op ${String(op)}`)
        if(op==='var' && !vars.has(String(o.name)))throw Error(`unmapped variable ${String(o.name)}`)
        if(op==='const' && Object.values(bindings.maps).some(m=>m.radix===o.value))throw Error('ambiguous fixed radix literal')
        if(op==='get'){
          const layout=bindings.maps[String(o.map)], key=o.key as E
          if(!layout || layout.sorts.length!==1 || !key || key.op!=='var')throw Error('unsupported count map layout')
          if(!Object.hasOwn(target.maps??{},layout.target) && !(target.inputMaps??[]).includes(layout.target))throw Error('unmapped count body map')
          const expected=key.name===d.j?cfg.jSort:key.name===d.key?cfg.keySort:undefined
          if(!expected || layout.sorts[0]!==expected)throw Error('count key sort mismatch')
          const relation=target.relations?.[layout.target]
          if(relation && (relation.length!==1 || relation[0]!==expected))throw Error('count map relation mismatch')
          return {op:'get',map:layout.target,key:{...key}}
        }
        return Object.fromEntries(Object.entries(o).map(([k,v])=>[k,rewrite(v)]))
      }
      const below=rewrite(d.below) as E, body=rewrite(d.body) as E
      const contains=(v:unknown):boolean=>!!v && typeof v==='object' && (Array.isArray(v)?v.some(contains):((v as any).op==='var'&&(v as any).name===d.key)||Object.values(v).some(contains))
      if(contains(below))throw Error('count bound mentions key')
      used.add(cfg.target)
      return {source:name,status:'candidate',target:cfg.target,definition:{j:d.j,key:d.key,below,body}}
    } catch(e) {return {source:name,status:'dropped',reason:e instanceof Error?e.message:String(e)}}
  })
}
