// Untrusted instances of the machine's universal flags at selected count witnesses.
// Count.lean only supplies a witness; the pointwise request predicates at that
// witness must still be instantiated and proved useful by the ordinary kernel.
import {type E, type Machine, walkOnce, x} from './machine.ts'
import {type CountCert, type CountDecl, type Instances} from '../kernel/kernel.ts'

const mapsIn = (value: unknown): Set<string> => {
  const maps = new Set<string>()
  walkOnce(value, (o: any) => { if (o.op === 'get') maps.add(o.map) })
  return maps
}
export function seedCountWitnessFlags(m: Machine, at: Instances, packets: {decls: CountDecl[], cert: Pick<CountCert, 'reads' | 'insts'>}[], preferCarried = false, options: {dependencies?: (body: E) => Set<string>, carriedOnly?: boolean} = {}): Instances {
  let out = at
  const flags = Object.entries(m.step.flags ?? {}).filter(([, q]) => q.op === 'all' && !q.keys?.length).map(([name, q]) => ({name: `?${name}`, maps: mapsIn(q)}))
    // A count read at its own CInst witness is outside checkMC's read-key scope.
    .filter(q => ![...q.maps].some(mp => mp in (m.counts ?? {})))
  for (const {decls, cert} of packets) {
    const bodies = new Map(cert.reads.map(([id, map]) => { const d = decls.find(d => d.map === map); return [id, d ? (options.dependencies ?? mapsIn)(d.body) : new Set<string>()] }))
    for (const inst of cert.insts) {
      let used = new Set(inst.terms.flatMap(([, id]) => [...bodies.get(id) ?? []]))
      if (preferCarried) {
        const carried = new Set(inst.terms.filter(([coefficient]) => coefficient > 0).flatMap(([, id]) => [...bodies.get(id) ?? []]).filter(mp => m.inputMaps?.includes(mp)))
        if (carried.size || options.carriedOnly) used = carried
      }
      for (const f of flags) if (!f.maps.size || [...f.maps].some(mp => used.has(mp))) {
        const term: E = x(inst.wit), had = out[f.name] ?? []
        if (had.some(e => e.op === 'var' && e.name === inst.wit)) continue
        if (out === at) out = {...at}
        out[f.name] = [...had, term]
      }
    }
  }
  return out
}
