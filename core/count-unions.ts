// Untrusted set-cover proposals for Count.lean's existing single-witness CInst.
// Two positive counts may be disjoint inside one set or a union of three
// Venn regions. No disjointness/coverage fact is assumed here: a generated
// instance keeps its witness alternative, checked by the ordinary kernel.
import {type C, type E, x} from './machine.ts'
import {type Count, type CountInst, substE} from '../kernel/kernel.ts'

type Bool = boolean | {atom: string} | {not: Bool} | {and: Bool[]} | {or: Bool[]}
const key = (x: unknown) => JSON.stringify(x)
const cond = (c: C, atoms: Set<string>): Bool | undefined => {
  if (c.op === 'flag' || c.op === 'all') return undefined
  if (c.op === 'not') { const b = cond(c.x, atoms); return b === undefined ? undefined : {not: b} }
  if (c.op === 'and' || c.op === 'or') {
    const bs = c.xs.map(c => cond(c, atoms))
    return bs.some(b => b === undefined) ? undefined : {[c.op]: bs as Bool[]} as Bool
  }
  const atom = key(c); atoms.add(atom); return {atom}
}
const body = (e: E, atoms: Set<string>): Bool | undefined => {
  if (e.op === 'const') return e.value === 0 ? false : e.value === 1 ? true : undefined
  if (e.op !== 'if') return undefined
  const c = cond(e.c, atoms), a = body(e.then, atoms), b = body(e.else, atoms)
  return c === undefined || a === undefined || b === undefined ? undefined : {or: [{and: [c, a]}, {and: [{not: c}, b]}]}
}
const evaluate = (b: Bool, at: Map<string, boolean>): boolean => typeof b === 'boolean' ? b : 'atom' in b ? at.get(b.atom)! : 'not' in b ? !evaluate(b.not, at) : 'and' in b ? b.and.every(c => evaluate(c, at)) : b.or.some(c => evaluate(c, at))

export function proposeCountUnions(counts: Count[], pairs: [string, string][], maxFacts = 128): CountInst[] {
  const out: CountInst[] = [], seen = new Set<string>()
  const add = (a: Count, b: Count, cover: Count[]) => {
    if (out.length >= maxFacts || cover.some(c => c.v === a.v || c.v === b.v)) return
    const terms: [number, string][] = [[1, a.v], [1, b.v], ...cover.map(c => [-1, c.v] as [number, string])]
    const signature = key(terms)
    if (!seen.has(signature)) { seen.add(signature); out.push({wit: `union$${out.length}`, below: a.below, terms, unit: 0}) }
  }
  const groups = new Map<string, Count[]>()
  for (const c of counts.slice(0, 128)) { const k = key(c.below), cs = groups.get(k) ?? []; cs.push(c); groups.set(k, cs) }
  for (const cs of groups.values()) {
    const byName = new Map(cs.map(c => [c.v, c])), regions = new Map<string, Map<number, Count>>()
    for (const c of cs) {
      const atoms = new Set<string>(), f = body(substE(c.body, {vars: {[c.key]: x('union$key')}, maps: {}, flags: {}}), atoms)
      if (f === undefined || atoms.size !== 2) continue
      const ks = [...atoms].sort()
      let mask = 0
      for (let bits = 0; bits < 4; bits++) if (evaluate(f, new Map(ks.map((k, i) => [k, !!(bits & (1 << i))])))) mask |= 1 << bits
      // One region of two primitive predicates; select a representative for duplicates.
      if (![1, 2, 4, 8].includes(mask)) continue
      const id = key(ks), rs = regions.get(id) ?? new Map<number, Count>()
      if (!rs.has(mask)) rs.set(mask, c)
      regions.set(id, rs)
    }
    // An indicator is the disjoint union of the two regions where its atom
    // holds. Raw map-valued counts are only *candidates* for indicators: the
    // returned CInst retains its pointwise alternative, so 0/1 membership must
    // still be established from the actual machine's hypotheses.
    for(const c of cs){
      const e=substE(c.body,{vars:{[c.key]:x('union$key')},maps:{},flags:{}})
      const atoms=new Set<string>(),f=body(e,atoms)
      const atom=e.op==='get'?key({op:'=',a:e,b:{op:'const',value:1}}):atoms.size===1?[...atoms][0]:undefined
      if(!atom)continue
      const on=(v:boolean)=>e.op==='get'?v:f!==undefined&&evaluate(f,new Map([[atom,v]]))
      for(const [id,rs] of regions){
        const ks=JSON.parse(id) as string[],i=ks.indexOf(atom)
        if(i<0)continue
        const parts=[1,2,4,8].filter((_,bits)=>on(!!(bits&(1<<i)))).map(mask=>rs.get(mask))
        const [left,right]=parts
        if(parts.length!==2||!left||!right||out.length+2>maxFacts)continue
        for(const sign of [1,-1]){
          const terms:[number,string][]=[[sign,c.v],[-sign,left.v],[-sign,right.v]],signature=key(terms)
          if(!seen.has(signature)){seen.add(signature);out.push({wit:`union$${out.length}`,below:c.below,terms,unit:0})}
        }
      }
    }
    const triples = [...regions.values()].filter(rs => rs.has(2) && rs.has(4) && rs.has(8)).map(rs => [rs.get(2)!, rs.get(4)!, rs.get(8)!])
    const positive = pairs.flatMap(([a, b]) => byName.has(a) && byName.has(b) && a !== b ? [[byName.get(a)!, byName.get(b)!] as [Count, Count]] : [])
    // Reserve room for both shapes, rather than letting all the singleton covers
    // precede the five-term certificate a relational union needs.
    for (const [a, b] of positive) for (const cover of triples) add(a, b, cover)
    for (const [a, b] of positive) for (const c of cs) add(a, b, [c])
  }
  return out
}
