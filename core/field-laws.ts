// Untrusted candidates for maps of numeric fields. Boolean cubes lose comparisons
// between fields (and between two records), even when the transition reads them.
// Propose their shapes, not facts: counts.ts filters on reachable samples, and the
// ordinary counted induction/checker must prove every surviving candidate.
import {type C, type E, type Law, type Machine, all, any, atMost, get, less, n, not, same, tuple, walk, x} from './machine.ts'

export function fieldLaws(m: Machine): Law[] {
  const fields = new Set<string>(), roles = new Map<string, {map: string, value: number}>(), bounds = new Map<string, E>()
  const maps = m.maps ?? {}, source = [m.assume, m.step.flags]
  const direct = (e: E): e is Extract<E, {op: 'get'}> => e.op === 'get' && e.key.op === 'var' && e.map in maps
  const cells = (e: E): string[] => {
    const out = new Set<string>()
    walk(e, o => { const t = o as E; if (direct(t)) out.add(t.map) })
    return [...out]
  }
  walk(source, o => {
    if (o.op !== '=' && o.op !== '<' && o.op !== '<=') return
    const c = o as Extract<C, {op: '=' | '<' | '<='}>, a = cells(c.a), b = cells(c.b)
    if (a.length && b.length) for (const name of [...a, ...b]) fields.add(name)
    if (c.op === '=' && direct(c.a) && c.a.key.op === 'var' && m.inputs.includes(c.a.key.name) && c.b.op === 'const') roles.set(`${c.a.map}:${c.b.value}`, {map: c.a.map, value: c.b.value})
    if (c.op === '<' && c.a.op === 'var' && m.inputs.includes(c.a.name) && c.b.op === 'var' && m.params.includes(c.b.name)) bounds.set(JSON.stringify(c.b), c.b)
  })
  // Different key domains need a sort analysis. Do not guess a shared domain.
  if (fields.size < 2 || bounds.size !== 1) return []
  const bound = [...bounds.values()][0]!, fs = [...fields].sort(), rs = [...roles.values()].filter(r => !fields.has(r.map))
  const names = new Set<string>([...m.params, ...m.inputs, ...Object.keys(m.state)])
  walk(m, o => { if (o.op === 'var') names.add(o.name as string) })
  const fresh = (base: string) => { let s = base; while (names.has(s)) s += '$'; names.add(s); return s }
  const ka = fresh('a$field'), kb = fresh('b$field'), kc = fresh('c$field'), a = x(ka), b = x(kb), c = x(kc), da = less(a, bound), db = less(b, bound)
  const out: Law[] = [], seen = new Set<string>()
  const propose = (name: string, guards: C[], holds: C, pair = false) => {
    const body = any(not(all(da, ...(pair ? [db] : []), ...guards)), holds), id = JSON.stringify(body)
    if (seen.has(id)) return
    seen.add(id); out.push({name: `fields: ${name}`, forall: ka, ...(pair ? {keys: [kb]} : {}), holds: body})
  }
  const guards: {name: string, c: C[]}[] = [{name: '', c: []}, ...rs.map(r => ({name: `${r.map}[a]=${r.value} -> `, c: [same(get(r.map, a), n(r.value))]}))]
  for (const f of fs) for (const g of fs) {
    if (f === g) continue
    for (const h of guards) {
      if (f < g) propose(`${h.name}${f}[a]=${g}[a]`, h.c, same(get(f, a), get(g, a)))
      propose(`${h.name}${f}[a]<=${g}[a]`, h.c, atMost(get(f, a), get(g, a)))
    }
    // Equality of a record's first field can constrain the order of its second
    // field across records. A role applies to the first record, not both.
    for (const h of guards) {
      const eq = same(get(f, a), get(f, b))
      propose(`${h.name}${f}[a]=${f}[b] -> ${g}[b]<=${g}[a]`, [...h.c, eq], atMost(get(g, b), get(g, a)), true)
      propose(`${h.name}${f}[a]=${f}[b] -> ${g}[a]=${g}[b]`, [...h.c, eq], same(get(g, a), get(g, b)), true)
    }
  }
  // Versioned rows: two equal numeric fields identify the contents of a row.
  // Quantify the member independently; no finite row is baked into the claim.
  for (const [map, sorts] of Object.entries(m.relations ?? {})) {
    if (sorts.length !== 2 || sorts[0] !== sorts[1]) continue
    for (let i = 0; i < fs.length; i++) for (let j = i + 1; j < fs.length; j++) {
      const f = fs[i]!, g = fs[j]!
      const guard = all(da, db, less(c, bound), same(get(f, a), get(f, b)), same(get(g, a), get(g, b)))
      const holds = any(not(guard), same(get(map, tuple([a, c])), get(map, tuple([b, c]))))
      out.push({name: `fields: ${f}[a]=${f}[b] and ${g}[a]=${g}[b] -> ${map} rows agree`, forall: ka, keys: [kb, kc], holds})
    }
  }
  return out
}
