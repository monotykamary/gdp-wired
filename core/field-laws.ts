// Untrusted candidates for maps of numeric fields. Boolean cubes lose comparisons
// between fields (and between two records), even when the transition reads them.
// Propose their shapes, not facts: counts.ts filters on reachable samples, and the
// ordinary counted induction/checker must prove every surviving candidate.
import {type C, type E, type Law, type Machine, all, any, atMost, get, less, n, not, same, times, plus, tuple, walk, x} from './machine.ts'

// A guarded form and the stronger candidate it weakens; the guarded one is admitted only when the stronger is not.
export const weakensField = new WeakMap<Law, Law>()
const loadFieldFamily = new WeakMap<Law, Law>()
// Prefer the unguarded load, otherwise the first admitted singleton guard.
// Older field families retain their order and admission behavior.
export function selectFieldLaws(laws: Law[], admit: (law: Law) => boolean): Law[] {
  const kept = new Set<Law>(), selectedLoads = new Set<Law>()
  return laws.filter(law => {
    const stronger = weakensField.get(law), load = loadFieldFamily.get(law)
    if ((stronger && kept.has(stronger)) || (load && selectedLoads.has(load)) || !admit(law)) return false
    kept.add(law)
    if (load) selectedLoads.add(load)
    return true
  })
}

export function fieldLaws(m: Machine, composed = true, loaded = true): Law[] {
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
  // The numeric encoding base*row + member is a relation too. Discover it
  // from reads, not map names; explicit tuple metadata keeps its old encoding.
  if (composed) {
    const rows = new Map<string, number>()
    walk([m.assume, m.step, m.counts], o => {
      if (o.op !== 'get' || !(o.map as string in maps) || m.relations?.[o.map as string]) return
      const key = o.key as E
      if (key.op !== 'add' || key.a.op !== 'mul' || key.a.k <= 1 || key.a.a.op !== 'var' || key.b.op !== 'var' || key.a.a.name === key.b.name || !m.inputs.includes(key.a.a.name)) return
      const old = rows.get(o.map as string)
      rows.set(o.map as string, old === undefined || old === key.a.k ? key.a.k : 0)
    })
    // Zero is reserved for ambiguous packed strides; -1 denotes a native tuple.
    for (const [map, sorts] of Object.entries(m.relations ?? {})) if (sorts.length === 2 && sorts[0] === sorts[1]) rows.set(map, -1)
    const agrees: {map: string, f: string, g: string, law: Law}[] = []
    for (const [map, base] of rows) if (base) for (let i = 0; i < fs.length; i++) for (let j = i + 1; j < fs.length; j++) {
      const f = fs[i]!, g = fs[j]!, cell = (row: E) => get(map, base === -1 ? tuple([row, c]) : plus(times(base, row), c))
      const guard = all(da, db, less(c, bound), same(get(f, a), get(f, b)), same(get(g, a), get(g, b)))
      const law: Law = {name: `fields: ${f}[a]=${f}[b] and ${g}[a]=${g}[b] -> ${map} rows agree`, forall: ka, keys: [kb, kc], holds: any(not(guard), same(cell(a), cell(b)))}
      // Tuple agreement was already emitted above; use that same stronger law.
      const existing = base === -1 ? out.find(l => l.name === law.name) : undefined
      if (!existing) out.push(law)
      agrees.push({map, f, g, law: existing ?? law})
    }
    if (!loaded) return out
    // Loaded rows: an every-key write that, in a flag's branch and inside the row of an input, reads ANOTHER plain-key
    // map at the column fills that row from the map. A cell the same branch sets at the input marks the rows so
    // filled. Proposed: a marked row is the source, outright and under each scalar literal of the flag (the phase in
    // which the load happens); and each versioned-rows law above restricted to marked rows. The guarded forms are
    // weakenings (`weakensField`): the caller admits one only when its stronger form failed the samples.
    type Node = {op?: string, [k: string]: unknown}
    const node = (t: unknown): t is Node => !!t && typeof t === 'object' && !Array.isArray(t)
    const atoms = (t: Node | undefined): Node[] => !t ? [] : t.op === 'and' ? (t.xs as Node[]).flatMap(atoms) : [t]
    const sameTerm = (a: unknown, b: unknown) => JSON.stringify(a) === JSON.stringify(b)
    const restrictCondition = (condition: C, flag: string, value: boolean): C | boolean => {
      if (condition.op === 'flag') return condition.name === flag ? value : condition
      if (condition.op === 'not') {
        const inner = restrictCondition(condition.x, flag, value)
        return typeof inner === 'boolean' ? !inner : not(inner)
      }
      if (condition.op === 'and' || condition.op === 'or') {
        const parts = condition.xs.map(c => restrictCondition(c, flag, value)), conjunction = condition.op === 'and'
        if (parts.includes(!conjunction)) return !conjunction
        const rest = parts.filter((c): c is C => typeof c !== 'boolean')
        return !rest.length ? conjunction : rest.length === 1 ? rest[0]! : conjunction ? all(...rest) : any(...rest)
      }
      if ((condition.op === '=' || condition.op === '<' || condition.op === '<=') && condition.a.op === 'const' && condition.b.op === 'const') {
        return condition.op === '=' ? condition.a.value === condition.b.value : condition.op === '<' ? condition.a.value < condition.b.value : condition.a.value <= condition.b.value
      }
      return condition
    }
    const restrictValue = (value: E, flag: string, active: boolean): E => {
      if (value.op !== 'if') return value
      const condition = restrictCondition(value.c, flag, active)
      if (typeof condition === 'boolean') return restrictValue(condition ? value.then : value.else, flag, active)
      return {...value, c: condition, then: restrictValue(value.then, flag, active), else: restrictValue(value.else, flag, active)}
    }
    const markerValue = (value: E, map: string, key: E, flag: string): number | undefined => {
      const active = restrictValue(value, flag, true), inactive = restrictValue(value, flag, false)
      if (active.op !== 'const' || !Number.isSafeInteger(active.value) || active.value < 1) return undefined
      const old = get(map, key), v = active.value
      if (sameTerm(inactive, old) || inactive.op === 'const' && inactive.value !== v) return v
      // Boolean maps compile a preserved cell as if old=1 then 1 else 0.
      // This cannot manufacture a marker outside the load branch.
      if (inactive.op === 'if' && inactive.c.op === '=' && inactive.then.op === 'const' && inactive.then.value === v
        && inactive.else.op === 'const' && inactive.else.value !== v
        && (sameTerm(inactive.c, same(old, n(v))) || sameTerm(inactive.c, same(n(v), old)))) return v
      return undefined
    }
    const emitted = new Map<string, Law>()
    const add = (law: Law): Law => {
      const key = JSON.stringify(law.holds), old = emitted.get(key)
      if (old) return old
      emitted.set(key, law); out.push(law); return law
    }
    for (const [map, base] of rows) {
      const w = m.step.maps?.[map]
      if (!base || !w || !('each' in w)) continue
      const loads = new Map<string, {src: string, input: string, flag: string}>()
      const visit = (t: unknown, positive: Node[]): void => {
        if (Array.isArray(t)) { for (const u of t) visit(u, positive); return }
        if (!node(t) || t.op === 'not') return
        if (t.op === 'if') {
          const branch = [...positive, ...atoms(t.c as Node)]
          visit(t.c, branch); visit(t.then, branch); visit(t.else, positive)
          return
        }
        const here = t.op === 'and' ? [...positive, ...atoms(t)] : positive
        const key = t.key as Node | undefined, row = key?.b as Node | undefined, input = (row?.a as Node | undefined)?.name as string | undefined, src = t.map as string
        if (base === -1 && t.op === 'get' && src !== map && src in maps && !rows.has(src)) {
          const first: E = {op: 'proj', k: 0, a: x(w.each)}, second: E = {op: 'proj', k: 1, a: x(w.each)}
          if (sameTerm(t.key, second)) for (const input of m.inputs) if (here.some(q => sameTerm(q, same(first, x(input))) || sameTerm(q, same(x(input), first))))
            for (const q of here) if (q.op === 'flag') { const flag = q.name as string; loads.set(`${src}:${input}:${flag}`, {src, input, flag}) }
        }
        if (base !== -1 && t.op === 'get' && src !== map && src in maps && !rows.has(src) && key?.op === 'sub' && (key.a as Node).op === 'var' && (key.a as Node).name === w.each
          && row?.op === 'mul' && row.k === base && (row.a as Node).op === 'var' && input !== undefined && m.inputs.includes(input)
          && here.some(q => sameTerm(q, atMost(times(base, x(input)), x(w.each))))
          && here.some(q => sameTerm(q, less(x(w.each), plus(times(base, x(input)), n(base))))))
          for (const q of here) if (q.op === 'flag') { const flag = q.name as string; loads.set(`${src}:${input}:${flag}`, {src, input, flag}) }
        for (const u of Object.values(t)) visit(u, here)
      }
      visit(w.value, [])
      const cell = (r: E) => get(map, base === -1 ? tuple([r, c]) : plus(times(base, r), c))
      for (const {src, input, flag} of loads.values()) for (const [mk, mw] of Object.entries(m.step.maps ?? {})) {
        if ('each' in mw || mw.key.op !== 'var' || mw.key.name !== input || !(mk in maps) || rows.has(mk) || mk === src) continue
        const v = markerValue(mw.value, mk, mw.key, flag)
        if (v === undefined) continue
        const marked = (r: E) => same(get(mk, r), n(v)), def = m.step.flags?.[flag] as Node | undefined
        const literals = atoms(def).filter(q => q.op === '=' && (q.a as Node).op === 'var' && ((q.a as Node).name as string) in m.state && (q.b as Node).op === 'const') as unknown as C[]
        const load = (guards: C[], label: string): Law => ({name: `fields: ${mk}[a]=${v}${label} -> ${map} row is ${src}`, forall: ka, keys: [kc],
          holds: any(not(all(da, less(c, bound), marked(a), ...guards)), same(cell(a), get(src, c)))})
        const whole = add(load([], ''))
        loadFieldFamily.set(whole, whole)
        for (const lit of literals) {
          const q = lit as unknown as {a: {name: string}, b: {value: number}}, weaker = load([lit], ` and ${q.a.name}=${q.b.value}`)
          const choice = add(weaker)
          weakensField.set(choice, whole); loadFieldFamily.set(choice, whole)
        }
        for (const {f, g, law} of agrees.filter(r => r.map === map)) {
          const guard = all(da, db, less(c, bound), same(get(f, a), get(f, b)), same(get(g, a), get(g, b)), marked(a), marked(b))
          const weaker: Law = {name: `fields: ${f}[a]=${f}[b] and ${g}[a]=${g}[b] and ${mk}[a]=${mk}[b]=${v} -> ${map} rows agree`, forall: ka, keys: [kb, kc], holds: any(not(guard), same(cell(a), cell(b)))}
          weakensField.set(add(weaker), law)
        }
      }
    }
  }
  return out
}
