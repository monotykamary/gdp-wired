// Mechanical, fail-closed restatement of a restricted retained Law AST.
// Output is an untrusted candidate, never a fact or a proof.
import type {C, E, Law, Machine} from '../../core/machine.ts'
import {proposeFieldRows, type FieldSeedBinding, type FieldRowAudit} from './field-seed.ts'
import {expandFlatCellBinders} from './flat-cell-seed.ts'

export type SeedLayout = {target: string, sorts: string[], radix: number}
export type SeedBindings = {maps: Record<string, SeedLayout>, domains: Record<string, string>, fields?:Record<string,FieldSeedBinding>, variables?:Record<string,string|{sort:string,radix:number}>}
export type SeedAudit = {index: number, source: string, status: 'candidate', bindings: Record<string,string>, unboundedBinders?:string[], vacuousBinders?:string[], cellBinders?:Record<string,string[]>, sourceFamily?:number, sourceIndex?:number, regeneratedKind?:string, expandedKind?:string, fieldRows?:FieldRowAudit, law: Law} | {index: number, source: string, status: 'dropped', reason: string, original?:Law}

export type NativeSeedContext = {kindLaws?:Law[], sumVariables?:Record<string,string>, sourceMachine?:Machine}
export function restateSeeds(source: Law[], target: Machine, config: SeedBindings, native:NativeSeedContext = {}): SeedAudit[] {
  return source.map((law, index): SeedAudit => {
    const original=law
    try {
      const allowed = new Set(['name','forall','keys','holds'])
      if (Object.keys(law).some(k => !allowed.has(k))) throw Error('unsupported law metadata')
      let expandedKind:string|undefined
      const kind = /^every (.+) cell is a value of its kind$/.exec(law.name)
      if(kind) {
        const layout=config.maps[kind[1]!]
        const regenerated=layout && Object.hasOwn(target.maps ?? {},layout.target)
          ? native.kindLaws?.find(k=>k.name===`every ${layout.target} cell is a value of its kind`)
          : undefined
        if(regenerated) return {index,source:law.name,status:'candidate',bindings:{},regeneratedKind:layout!.target,
          law:{...regenerated,name:`retained:${index}:${law.name}`}}
        // A raw packed-cell kind quantifier ranges over one native key. Expand
        // it to explicit tuple coordinates when the target has no separate
        // kindLaws() entry; retain the source predicate as an untrusted proposal.
        if(layout && Object.hasOwn(target.maps ?? {},layout.target) && law.forall && !law.keys?.length && layout.sorts.length>1) {
          const old=law.forall, reserved=new Set([...target.params,...target.inputs,...Object.keys(target.state)])
          const names=layout.sorts.map((_,i)=>{let n=`seed$kind$${i}`;while(reserved.has(n))n+='$';reserved.add(n);return n})
          const coords=names.map(name=>({op:'var',name} as E))
          const packed=coords.slice(1).reduce<E>((a,b)=>({op:'add',a:{op:'mul',k:layout.radix,a},b}),coords[0]!)
          const expand=(x:unknown):unknown=>{
            if(Array.isArray(x))return x.map(expand)
            if(!x||typeof x!=='object')return x
            const o=x as Record<string,unknown>
            if(o.op==='get') {
              const key=o.key as E
              if(o.map!==kind[1] || key.op!=='var' || key.name!==old)throw Error('unsupported packed kind predicate')
              return {...o,key:packed}
            }
            if(o.op==='var'&&o.name===old)throw Error('kind key escapes its cell read')
            return Object.fromEntries(Object.entries(o).map(([k,v])=>[k,expand(v)]))
          }
          law={...law,forall:names[0],keys:names.slice(1),holds:expand(law.holds) as C}
          expandedKind=layout.target
        }
      }
      const fieldProposal=proposeFieldRows(law,native.sourceMachine,target,config)
      const flat=expandFlatCellBinders(fieldProposal.law,config)
      law=flat.law
      const binders = [law.forall, ...(law.keys ?? [])].filter((s): s is string => !!s)
      if (new Set(binders).size !== binders.length) throw Error('duplicate binders')
      const vars = new Set(binders), sorts: Record<string,string> = Object.create(null), bounded = new Set<string>()
      const widths=[...Object.values(config.maps).map(m=>m.radix),...Object.values(config.variables??{}).flatMap(v=>typeof v==='string'?[]:[v.radix])]
      const classify = (name: string, sort: string) => {
        if (!vars.has(name)) throw Error(`packed key is not a bound variable: ${name}`)
        if (sorts[name] && sorts[name] !== sort) throw Error(`conflicting sort for ${name}`)
        if (!config.domains[sort] || !target.params.includes(config.domains[sort]!)) throw Error(`missing symbolic domain for ${sort}`)
        sorts[name] = sort
      }
      const parts = (e:E, radix:number, arity:number): string[] => {
        // The historic pk3 is n*radix^2 + k*radix + v. Flatten
        // arithmetic into a linear coefficient table, then require one bound
        // variable at each exact position; aliases and offsets are refused.
        const terms: [string, number][] = []
        const visit = (x:E, multiplier:number):void => {
          if (x.op === 'add') {visit(x.a,multiplier);visit(x.b,multiplier)}
          else if (x.op === 'mul') visit(x.a,multiplier*x.k)
          else if (x.op === 'var') terms.push([x.name,multiplier])
          else throw Error('unsupported packed key expression')
        }
        visit(e,1)
        const expected = Array.from({length:arity},(_,i)=>radix ** (arity-i-1))
        if (!Number.isSafeInteger(radix) || radix < 2 || expected.some(n=>!Number.isSafeInteger(n)) || terms.length !== arity) throw Error('invalid packed layout')
        return expected.map(coef => {
          const found=terms.filter(t=>t[1]===coef)
          if(found.length!==1) throw Error('packed coefficient does not match layout')
          return found[0]![0]
        })
      }
      const constantCountKey = (name:string,key:E):boolean => {
        const layout=config.maps[name], d=layout && target.counts?.[layout.target]
        const reads=(x:unknown):boolean=>!!x && typeof x==='object' && (Array.isArray(x)?x.some(reads):((x as any).op==='var'&&(x as any).name===d?.j)||Object.values(x).some(reads))
        return !!d && key.op==='const' && layout!.sorts.length===1 && !reads(d.body) && !reads(d.below)
      }
      const gather = (v:unknown):void => {
        if (!v || typeof v !== 'object') return
        if (Array.isArray(v)) {v.forEach(gather);return}
        const o=v as Record<string,unknown>
        if(o.op==='<' && (o.a as E)?.op==='var' && (o.b as E)?.op==='const') {
          const a=o.a as Extract<E,{op:'var'}>, b=o.b as Extract<E,{op:'const'}>
          if(vars.has(a.name) && widths.includes(b.value)) bounded.add(a.name)
        }
        if (o.op==='get') {
          const name=String(o.map), layout=config.maps[name]
          const ordinary = !!layout && Object.hasOwn(target.maps ?? {},layout.target)
          const counted = !!layout && Object.hasOwn(target.counts ?? {},layout.target)
          if(!layout || (!ordinary && !counted)) throw Error(`unmapped map ${name}`)
          if(ordinary && counted) throw Error(`ambiguous map/count target ${name}`)
          const targetSorts=target.relations?.[layout.target]
          // Unary native maps have no relation metadata. Their sized key is
          // supplied explicitly by this manifest and checked by classify below.
          // Check declared positions when present; otherwise the manifest's
          // explicit per-coordinate binding defines the proposed layout.
          // A count-definition adapter supplies the logical argument layout
          // for declared count maps; it is still only a candidate proposal.
          if(!layout.sorts.length || (targetSorts && JSON.stringify(targetSorts)!==JSON.stringify(layout.sorts)))
            throw Error(`target layout not established for ${name}`)
          if(constantCountKey(name,o.key as E)) return
          const keys=parts(o.key as E,layout.radix,layout.sorts.length)
          keys.forEach((key,i)=>classify(key,layout.sorts[i]!))
          return
        }
        Object.values(o).forEach(gather)
      }
      for(const [name,binding] of Object.entries(config.variables??{})) if(vars.has(name)) {
        if(typeof binding!=='string' && (!Number.isSafeInteger(binding.radix)||binding.radix<2))throw Error(`invalid variable radix for ${name}`)
        classify(name,typeof binding==='string'?binding:binding.sort)
      }
      gather(law.holds)
      const occurrences=new Set<string>()
      const collect=(x:unknown):void=>{if(Array.isArray(x)){x.forEach(collect);return}if(!x||typeof x!=='object')return;const o=x as Record<string,unknown>;if(o.op==='var')occurrences.add(String(o.name));Object.values(o).forEach(collect)}
      collect(law.holds)
      const vacuousBinders=binders.filter(b=>!occurrences.has(b))
      for (const binder of binders) {
        if (!sorts[binder] && !vacuousBinders.includes(binder)) throw Error(`unclassified bound variable ${binder}`)
      }
      if(vacuousBinders.length){const live=binders.filter(b=>!vacuousBinders.includes(b));law={...law,forall:live[0],keys:live.slice(1)}}
      const rewrite = (value:unknown):unknown => {
        if (Array.isArray(value)) return value.map(rewrite)
        if (!value || typeof value !== 'object') return value
        const o=value as Record<string,unknown>
        const op=o.op
        if (typeof op !== 'string' || !['var','const','add','sub','min','max','mul','prod','if','get','tup','proj','<','<=','=','and','or','not','flag'].includes(op)) throw Error(`unsupported AST op ${String(op)}`)
        if (op==='flag') throw Error('flag reference not mapped')
        if (op==='var' && native.sumVariables?.[String(o.name)]) return {op:'var',name:native.sumVariables[String(o.name)]}
        if (op==='var' && !vars.has(String(o.name)) && !target.params.includes(String(o.name)) && !Object.hasOwn(target.state,String(o.name))) throw Error(`unmapped variable ${String(o.name)}`)
        if (op==='get') {
          const layout=config.maps[String(o.map)]!
          if(constantCountKey(String(o.map),o.key as E)) return {op:'get',map:layout.target,key:{op:'const',value:0}}
          const keys=parts(o.key as E,layout.radix,layout.sorts.length)
          const tuple=(ks:string[]):E => ks.length===1 ? {op:'var',name:ks[0]!} : {op:'tup',a:{op:'var',name:ks[0]!},b:tuple(ks.slice(1))}
          return {op:'get',map:layout.target,key:tuple(keys)}
        }
        if (op==='<' && (o.a as E)?.op==='var' && (o.b as E)?.op==='const') {
          const a=o.a as Extract<E,{op:'var'}>, b=o.b as Extract<E,{op:'const'}>, sort=sorts[a.name]
          const radices=new Set(Object.values(config.maps).filter(m=>m.sorts.includes(sort!)).map(m=>m.radix))
          const binding=config.variables?.[a.name]
          if(binding && typeof binding!=='string' && binding.sort===sort)radices.add(binding.radix)
          if (sort && radices.size===1 && radices.has(b.value)) return {op:'<',a:{...a},b:{op:'var',name:config.domains[sort]!}}
        }
        if (op==='const' && widths.includes(o.value as number)) throw Error('ambiguous radix literal outside bound')
        return Object.fromEntries(Object.entries(o).map(([k,v])=>[k,rewrite(v)]))
      }
      const unboundedBinders = binders.filter(b => !bounded.has(b) && !vacuousBinders.includes(b))
      return {index,source:law.name,status:'candidate',bindings:{...sorts},...(vacuousBinders.length ? {vacuousBinders} : {}),...(Object.keys(flat.bindings).length ? {cellBinders:flat.bindings} : {}),...(expandedKind ? {expandedKind} : {}),...(fieldProposal.audit ? {fieldRows:fieldProposal.audit} : {}),...(unboundedBinders.length ? {unboundedBinders} : {}),law:{...law,name:`retained:${index}:${law.name}`,holds:rewrite(law.holds) as C}}
    } catch (error) {return {index,source:law.name,status:'dropped',reason:error instanceof Error ? error.message : String(error),original}}
  })
}
