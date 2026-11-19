// Untrusted, intentionally small syntax recognizers. Their products are
// candidates for exact finite-fold replay, never extra source facts.
import { type C, type E, type Law, type Machine, get, n, x, plus, same } from '../../core/machine.ts'
import { substC } from '../../kernel/kernel.ts'

const equal = (a: unknown, b: unknown) => JSON.stringify(a) === JSON.stringify(b)
const atoms = (c?: C): C[] => !c ? [] : c.op === 'and' ? c.xs.flatMap(atoms) : [c]
const subKey = (c: C, name: string, term: E) => substC(c, {vars:{[name]:term},maps:{},flags:{}})
const rootReset = (u: E, start: E) => u.op === 'if' && equal(u.then,start) ? u : undefined
const increase = (u: E, field: string) => u.op === 'if' && equal(u.else, x(field)) && equal(u.then,plus(x(field),n(1))) ? u.c : undefined
const guardIncludes = (full: C, sub: C) => atoms(sub).every(p => atoms(full).some(q => equal(p,q)))
const onlyVariable = (e: E, name: string) => e.op === 'var' && e.name === name

export type FilteredCounterProposal = {
  map: string, key: string, reset: C, bound: E, offset: number,
  fields: {field:string, value:number}[],
}
export function proposeFilteredCounters(m: Machine, caller: Law): FilteredCounterProposal[] {
  if (m.history || Object.keys(m.counts ?? {}).length || Object.keys(m.sums ?? {}).length || caller.forall || caller.keys?.length) return []
  const uses = JSON.stringify(caller.holds)
  const out: FilteredCounterProposal[] = []
  for (const [map, wr] of Object.entries(m.step.maps ?? {})) {
    // Cover singleton point writes and broadcast-reset-plus-point writes. A
    // spatial guard is not accepted as a scalar guard; it is first specialized.
    if (!('each' in wr) || m.maps?.[map] === undefined) continue
    const init = n(m.maps[map]!)
    const outer = rootReset(wr.value, init), first = outer?.else
    if (!outer || first?.op !== 'if') continue
    const keyAtom = atoms(first.c).find(c => c.op === '=' && onlyVariable(c.a,wr.each) && c.b.op === 'var' && m.inputs.includes(c.b.name))
    if (keyAtom?.op !== '=' || keyAtom.b.op !== 'var') continue
    const key = keyAtom.b.name
    const below = atoms(m.assume).find(c => (c.op === '<=' || c.op === '<') && onlyVariable(c.a,key) && c.b.op === 'var' && m.params.includes(c.b.name))
    if (!below || (below.op !== '<=' && below.op !== '<')) continue
    const lower = atoms(m.assume).filter(c => c.op === '<=' && c.a.op === 'const' && onlyVariable(c.b,key)).map(c => c.op === '<=' && c.a.op === 'const' ? c.a.value : 0)
    const offset = Math.max(0,...lower)
    const bound0 = below.op === '<=' ? plus(below.b,n(1)) : below.b
    const bound = below.op === '<=' && offset === 1 ? below.b : offset ? {op:'sub',a:bound0,b:n(offset)} as const : bound0
    const options: {value:number, guard:C}[] = []
    let walk = first as E
    for (let i=0; i<8 && walk.op === 'if'; i++, walk=walk.else) {
      const value = walk.then
      const parts = atoms(walk.c)
      if (!parts.some(p=>equal(p,keyAtom)) || value.op !== 'const' || equal(value,init)) break
      const [one,...more] = parts.filter(p=>!equal(p,keyAtom))
      if (!one) break
      options.push({value:value.value,guard:more.length ? {op:'and',xs:[one,...more]} : one})
    }
    if (!equal(walk,get(map,x(wr.each))) || !options.length) continue
    const counters = Object.entries(m.step.state ?? {}).flatMap(([field,u]) => {
      if (!uses.includes(`"name":${JSON.stringify(field)}`) || !equal(m.state[field],n(0))) return []
      const reset = rootReset(u,n(0)), guard = reset && increase(reset.else,field)
      return reset && guard && equal(reset.c,outer.c) ? [{field,guard}] : []
    })
    const fields = counters.flatMap(({field,guard}) => {
      // Prefer the first branch whose guard is covered by the increment. Later
      // alternatives are fallback writes in the source's own branch order.
      const opt = options.find(o => guardIncludes(guard,o.guard))
      return opt ? [{field, value:opt.value}] : []
    })
    if (!fields.length || new Set(fields.map(f=>f.value)).size !== fields.length) continue
    out.push({map,key,reset:subKey(outer.c,wr.each,x(key)),bound,offset,fields})
  }
  return out
}
