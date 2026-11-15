// Mechanical, fail-closed restatement of a restricted retained Law AST.
// Output is an untrusted candidate, never a fact or a proof.
import type {C, E, Law, Machine} from '../../core/machine.ts'

export type SeedLayout = {target: string, sorts: string[], radix: number}
export type SeedBindings = {maps: Record<string, SeedLayout>, domains: Record<string, string>}
export type SeedAudit = {index: number, source: string, status: 'candidate', bindings: Record<string,string>, law: Law} | {index: number, source: string, status: 'dropped', reason: string}

export function restateSeeds(source: Law[], target: Machine, config: SeedBindings): SeedAudit[] {
  return source.map((law, index): SeedAudit => {
    try {
      const allowed = new Set(['name','forall','keys','holds'])
      if (Object.keys(law).some(k => !allowed.has(k))) throw Error('unsupported law metadata')
      const binders = [law.forall, ...(law.keys ?? [])].filter((s): s is string => !!s)
      if (new Set(binders).size !== binders.length) throw Error('duplicate binders')
      const vars = new Set(binders), sorts: Record<string,string> = Object.create(null), bounded = new Set<string>()
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
      const gather = (v:unknown):void => {
        if (!v || typeof v !== 'object') return
        if (Array.isArray(v)) {v.forEach(gather);return}
        const o=v as Record<string,unknown>
        if(o.op==='<' && (o.a as E)?.op==='var' && (o.b as E)?.op==='const') {
          const a=o.a as Extract<E,{op:'var'}>, b=o.b as Extract<E,{op:'const'}>
          if(vars.has(a.name) && Object.values(config.maps).some(m=>m.radix===b.value)) bounded.add(a.name)
        }
        if (o.op==='get') {
          const name=String(o.map), layout=config.maps[name]
          if(!layout || !Object.hasOwn(target.maps ?? {},layout.target)) throw Error(`unmapped map ${name}`)
          const targetSorts=target.relations?.[layout.target]
          if(!targetSorts || JSON.stringify(targetSorts)!==JSON.stringify(layout.sorts)) throw Error(`target layout not established for ${name}`)
          const keys=parts(o.key as E,layout.radix,layout.sorts.length)
          keys.forEach((key,i)=>classify(key,layout.sorts[i]!))
          return
        }
        Object.values(o).forEach(gather)
      }
      gather(law.holds)
      for (const binder of binders) {
        if (!sorts[binder]) throw Error(`unclassified bound variable ${binder}`)
        if (!bounded.has(binder)) throw Error(`no explicit source domain guard for ${binder}`)
      }
      const rewrite = (value:unknown):unknown => {
        if (Array.isArray(value)) return value.map(rewrite)
        if (!value || typeof value !== 'object') return value
        const o=value as Record<string,unknown>
        const op=o.op
        if (typeof op !== 'string' || !['var','const','add','sub','min','max','mul','prod','if','get','tup','proj','<','<=','=','and','or','not','flag'].includes(op)) throw Error(`unsupported AST op ${String(op)}`)
        if (op==='flag') throw Error('flag reference not mapped')
        if (op==='var' && !vars.has(String(o.name)) && !target.params.includes(String(o.name)) && !Object.hasOwn(target.state,String(o.name))) throw Error(`unmapped variable ${String(o.name)}`)
        if (op==='get') {
          const layout=config.maps[String(o.map)]!, keys=parts(o.key as E,layout.radix,layout.sorts.length)
          const tuple=(ks:string[]):E => ks.length===1 ? {op:'var',name:ks[0]!} : {op:'tup',a:{op:'var',name:ks[0]!},b:tuple(ks.slice(1))}
          return {op:'get',map:layout.target,key:tuple(keys)}
        }
        if (op==='<' && (o.a as E)?.op==='var' && (o.b as E)?.op==='const') {
          const a=o.a as Extract<E,{op:'var'}>, b=o.b as Extract<E,{op:'const'}>, sort=sorts[a.name]
          const radices=new Set(Object.values(config.maps).filter(m=>m.sorts.includes(sort!)).map(m=>m.radix))
          if (sort && radices.size===1 && radices.has(b.value)) return {op:'<',a:{...a},b:{op:'var',name:config.domains[sort]!}}
        }
        if (op==='const' && Object.values(config.maps).some(m=>m.radix===o.value)) throw Error('ambiguous radix literal outside bound')
        return Object.fromEntries(Object.entries(o).map(([k,v])=>[k,rewrite(v)]))
      }
      return {index,source:law.name,status:'candidate',bindings:{...sorts},law:{...law,name:`retained:${index}:${law.name}`,holds:rewrite(law.holds) as C}}
    } catch (error) {return {index,source:law.name,status:'dropped',reason:error instanceof Error ? error.message : String(error)}}
  })
}
