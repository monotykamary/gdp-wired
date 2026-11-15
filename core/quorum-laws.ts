// Untrusted quorum candidates read from a stored row, a majority assumption, and
// an action's quantified guard. No protocol vocabulary or facts live here.
import {type C, type E, type Law, type Machine, all, any, atMost, get, ite, less, n, not, plus, same, times, tuple, walk, x} from './machine.ts'
import {substC, substE} from '../kernel/kernel.ts'
import {env} from './solver.ts'

// Candidate-only provenance. Weak identity preserves the serialised law and all
// existing certificate bytes; a changed formula invalidates its original tag.
export type QuorumLawProvenance = {
  kind: 'stored-row-guard', formula: string, guard: string, guardFormula: string,
  membershipMap: string, rowInput: string, rowCount: string, requestSet: string,
  width: number, halves: string[], disabled: boolean,
  twins: {request: string, row: string, key: string}[], definitions: Record<string, string>
}
const origins = new WeakMap<Law, QuorumLawProvenance>()
export function quorumLawProvenance(law: Law): Readonly<QuorumLawProvenance> | undefined {
  const origin = origins.get(law)
  return origin?.formula === JSON.stringify(law.holds) ? origin : undefined
}
const text = (t: unknown) => JSON.stringify(t)
const eq = (a: unknown, b: unknown) => text(a) === text(b)
const conjs = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(conjs) : [c]
const atoms = (c: C): C[] => c.op === 'and' || c.op === 'or' ? c.xs.flatMap(atoms) : c.op === 'not' ? atoms(c.x) : [c]
const vars = (t: unknown) => { const out = new Set<string>(); walk(t, o => { if (o.op === 'var') out.add(o.name as string) }); return out }
const flagsIn = (t: unknown) => { const out = new Set<string>(); walk(t, o => { if (o.op === 'flag') out.add(o.name as string) }); return out }
const sub = (names: Record<string, E>) => ({vars: names, maps: {}, flags: {}})
const indicator = (c: C): E => ite(c, n(1), n(0))
const bodyOf = (d: NonNullable<Machine['counts']>[string]): C | undefined => d.body.op === 'if' && eq(d.body.then, n(1)) && eq(d.body.else, n(0)) ? d.body.c : undefined
const packed = (base: number, a: E, b: E) => plus(times(base, a), b)
const contains = (t: unknown, part: unknown) => { let found = false; walk(t, o => { if (eq(o, part)) found = true }); return found }
// Replace the value an action stores BEFORE renaming the request's row. The
// fresh target key denotes any stored occurrence of that value, not the writer.
const replace = <T>(t: T, values: [E, E][]): T => {
  for (const [from, to] of values) if (eq(t, from)) return to as T
  if (Array.isArray(t)) return t.map(v => replace(v, values)) as T
  if (t && typeof t === 'object') return Object.fromEntries(Object.entries(t).map(([k, v]) => [k, replace(v, values)])) as T
  return t
}

type Row = {name: string, map: string, input: string, base: number, below: E, key: string, body: C}
// A positive row cell at base*request + member, in a 0/1 count.
function rowOf(m: Machine, name: string): Row | undefined {
  const d = m.counts?.[name], body = d && bodyOf(d)
  if (!d || !body || (body.op !== '=' && body.op !== '<=')) return undefined
  const cell = body.op === '=' && eq(body.b, n(1)) ? body.a : body.op === '<=' && eq(body.a, n(1)) ? body.b : undefined
  if (cell?.op !== 'get' || !(cell.map in (m.maps ?? {}))) return undefined
  const k = cell.key
  const packedRow = k.op === 'add' && k.a.op === 'mul' && k.a.k > 1 && k.a.a.op === 'var' && k.b.op === 'var' && k.b.name === d.key ? {input: k.a.a.name, base: k.a.k} : undefined
  const sorts = m.relations?.[cell.map]
  const tupleRow = k.op === 'tup' && k.a.op === 'var' && k.b.op === 'var' && k.b.name === d.key && sorts?.length === 2 && sorts[0] === sorts[1] ? {input: k.a.name, base: 0} : undefined
  const row = packedRow ?? tupleRow
  if (!row || !m.inputs.includes(row.input) || [d.j, ...m.inputs].some(v => vars(d.below).has(v))) return undefined
  return {name, map: cell.map, ...row, below: d.below, key: d.key, body}
}

export function quorumLaws(m: Machine, provenance = env.GDP_COUNT_LIFTED === '1'): {counts: NonNullable<Machine['counts']>, laws: Law[]} {
  const counts: NonNullable<Machine['counts']> = {}, laws: Law[] = []
  if (!m.assume || !m.counts || !m.inputMaps?.length) return {counts, laws}
  const names = new Set([...vars(m), ...Object.keys(m.counts), ...Object.keys(m.maps ?? {}), ...m.inputs, ...m.params, ...Object.keys(m.state)])
  const fresh = (stem: string) => { let name = stem; while (names.has(name)) name += '$'; names.add(name); return name }
  const a = fresh('a$quorum'), b = fresh('b$quorum'), u = fresh('u$quorum'), w = fresh('w$quorum')
  const j = fresh('row$quorum'), lo = fresh('other$quorum'), key = fresh('member$quorum')
  const fs = m.step.flags ?? {}, assumptions = atoms(m.assume)
  const rows = new Map<string, {row: Row, sets: Set<string>}>()
  for (const g of assumptions) {
    if (g.op !== '<' || g.a.op !== 'get' || g.b.op !== 'mul' || g.b.k !== 2 || g.b.a.op !== 'get') continue
    const row = rowOf(m, g.a.map), d = m.counts[g.b.a.map], body = d && bodyOf(d)
    if (!row || !d || !body || !eq(d.below, row.below) || vars([d.body, d.below]).has(d.j)) continue
    const used = new Set<string>(); walk(body, o => { if (o.op === 'get') used.add(o.map as string) })
    if (used.size !== 1 || !m.inputMaps.includes([...used][0]!)) continue
    let entry = rows.get(row.name)
    if (!entry) rows.set(row.name, (entry = {row, sets: new Set()}))
    entry.sets.add(g.b.a.map)
  }
  // Fast no-op on machines with parameter majorities rather than stored rows.
  for (const {row, sets} of rows.values()) {
    const rowBody = substC(row.body, sub({[row.input]: x(j), [row.key]: x(key)}))
    const domain = (v: string) => less(x(v), row.below)
    const registry = new Map<string, {name: string, pair: boolean, swap: boolean}>(), pairCounts = new Set<string>()
    // A count map accepts a plain key only. Quantify a single paired natural
    // and project its components in the law; count reads use that key directly.
    const pairLaw = (law: Law): Law | undefined => {
      if (row.base) return law
      const first: E = {op: 'proj', k: 0, a: x(a)}, second: E = {op: 'proj', k: 1, a: x(a)}
      const project = substC(law.holds, sub({[a]: first, [b]: second})), expected = tuple([first, second])
      let unsupported = false
      const plain = (t: unknown): unknown => {
        if (Array.isArray(t)) return t.map(plain)
        if (!t || typeof t !== 'object') return t
        const o = t as Record<string, unknown>
        if (o.op === 'get' && pairCounts.has(o.map as string)) {
          if (!eq(o.key, expected)) { unsupported = true; return o }
          return {...o, key: x(a)}
        }
        return Object.fromEntries(Object.entries(o).map(([k, v]) => [k, plain(v)]))
      }
      const keys = law.keys?.filter(k => k !== b), holds = plain(project) as C
      return unsupported ? undefined : {...law, ...(keys?.length ? {keys} : {keys: undefined}), holds}
    }
    const normal = (c: C): string => c.op === 'and' ? text(['and', conjs(c).map(normal).sort()]) : text(c)
    const count = (body: C, pair: boolean, label: string): ((a: string, b?: string) => E) => {
      const pairKey = (a: E, b: E) => row.base ? packed(row.base, a, b) : tuple([a, b])
      const id = normal(body), old = registry.get(id)
      if (old) return (a, b) => get(old.name, old.pair ? pairKey(x(old.swap ? b! : a), x(old.swap ? a : b!)) : x(a))
      const name = fresh(`${row.name}$${label}`)
      const pairBody = pair && !row.base ? substC(body, sub({[j]: {op: 'proj', k: 0, a: x(j)}, [lo]: {op: 'proj', k: 1, a: x(j)}})) : body
      counts[name] = {j, key, below: row.below, body: indicator(pairBody), ...(pair && row.base ? {lo, base: row.base} : {})}
      registry.set(id, {name, pair, swap: false})
      if (pair) pairCounts.add(name)
      if (pair && row.base) {
        const swapped = normal(substC(body, sub({[j]: x(lo), [lo]: x(j)})))
        if (!registry.has(swapped)) registry.set(swapped, {name, pair, swap: true})
      }
      return (a, b) => get(name, pair ? pairKey(x(a), x(b!)) : x(a))
    }
    let size: ((a: string) => E) | undefined
    const rowSize = (a: string) => (size ??= count(rowBody, false, 'row'))(a)
    const noQuorums: ((a: string) => C)[] = []
    let flagCount = 0
    for (const [flag, q] of Object.entries(fs)) {
      if (flagCount >= 2 || q.op !== 'all' || q.keys?.length || q.c.op !== 'or' || q.c.xs.length !== 2) continue
      const neg = q.c.xs.find(c => c.op === 'not'), rest = q.c.xs.find(c => c !== neg)
      if (neg?.op !== 'not' || !rest) continue
      const set = [...sets].find(name => {
        const d = m.counts![name]!, body = bodyOf(d)!
        return eq(substC(body, sub({[d.key]: x(q.key)})), neg.x)
      })
      const parts = conjs(rest)
      if (!set || !parts.length || parts.length > 3) continue
      const actions = Object.entries(fs).filter(([, c]) => c.op !== 'all' && flagsIn(c).has(flag))
      if (!actions.length) continue
      flagCount++
      const values: [E, E][] = []
      for (const [action] of actions) for (const [map, update] of Object.entries(m.step.maps ?? {})) {
        const visit = (value: E) => {
          if (value.op !== 'if') return
          const atRow = 'each' in update ? conjs(value.c).some(c => eq(c, same(x(update.each), x(row.input))) || eq(c, same(x(row.input), x(update.each)))) : eq(update.key, x(row.input))
          if (atRow && flagsIn(value.c).has(action) && value.then.op !== 'const' && value.then.op !== 'var' && value.then.op !== 'if' && !values.some(([from]) => eq(from, value.then))) values.push([value.then, get(map, x(lo))])
          visit(value.then); visit(value.else)
        }
        visit(update.value)
      }
      for (let bits = 1; bits < 1 << parts.length && laws.length < 32; bits++) {
        const selected = parts.filter((_, i) => bits >> i & 1)
        const lifted = substC(replace(all(...selected), values), sub({[row.input]: x(j), [q.key]: x(key)}))
        if (m.inputs.some(i => vars(lifted).has(i)) || [...flagsIn(lifted)].length) continue
        const pair = vars(lifted).has(lo), c = count(all(rowBody, ...conjs(lifted)), pair, `${flag}$${bits}`)
        const atom = (a: string, b?: string) => atMost(times(2, c(a, b)), rowSize(a))
        const law: Law = {name: `${row.name}: no quorum ${flag}/${bits}`, forall: a, ...(pair ? {keys: [b]} : {}), holds: any(not(all(domain(a), ...(pair ? [domain(b)] : []))), atom(a, b))}
        const proposal = pair ? pairLaw(law) : law
        if (proposal) laws.push(proposal)
        if (!pair) noQuorums.push(a => atom(a))
      }
    }
    // A carried set stored into this row licenses replacing that set by row b
    // in its action guard, and the request row by a. Half witnesses retain the
    // assumption atoms that constrain them; no arithmetic identity is trusted.
    for (const [action, guard] of Object.entries(fs)) {
      if (guard.op === 'all') continue
      const update = m.step.maps?.[row.map]
      if (!update || !('each' in update)) continue
      for (const [set, d] of Object.entries(m.counts)) {
        const setBody = bodyOf(d)
        if (!setBody || !eq(d.below, row.below)) continue
        const used = new Set<string>(); walk(setBody, o => { if (o.op === 'get' && m.inputMaps!.includes(o.map as string)) used.add(o.map as string) })
        if (used.size !== 1) continue
        const carried = [...used][0]!, column: E = row.base ? {op: 'sub', a: x(update.each), b: times(row.base, x(row.input))} : {op: 'proj', k: 1, a: x(update.each)}
        const shifted = substE(d.body, sub({[d.key]: column}))
        let stores = false
        walk(update.value, o => {
          if (o.op === 'if' && flagsIn(o.c).has(action) && eq(o.then, shifted) && (row.base || conjs(o.c as C).some(c => eq(c, same({op: 'proj', k: 0, a: x(update.each)}, x(row.input))) || eq(c, same(x(row.input), {op: 'proj', k: 0, a: x(update.each)}))))) stores = true
          // Boolean maps lower an if-tree to disjunctive membership clauses.
          if (o.op === 'and' && shifted.op === 'if') {
            const parts = conjs(o as C)
            const inRow = row.base || parts.some(c => eq(c, same({op: 'proj', k: 0, a: x(update.each)}, x(row.input))) || eq(c, same(x(row.input), {op: 'proj', k: 0, a: x(update.each)})))
            if (inRow && parts.some(c => c.op === 'flag' && c.name === action) && parts.some(c => eq(c, shifted.c))) stores = true
          }
        })
        if (!stores) continue
        const mapped = new Map<string, (a: string, b?: string) => E>()
        // Lift every matching set-vs-row count the action reads. 0/1 membership
        // substitutions are simplified so the reversed difference shares a count.
        const simplify = (c: C): C => {
          if (c.op === 'and' || c.op === 'or') return {...c, xs: c.xs.map(simplify)}
          if (c.op === 'not') return not(simplify(c.x))
          if (c.op === '=' && c.a.op === 'if' && eq(c.a.then, n(1)) && eq(c.a.else, n(0)) && eq(c.b, n(1))) return simplify(c.a.c)
          if (c.op === '<=' && eq(c.a, n(1)) && c.b.op === 'if' && eq(c.b.then, n(1)) && eq(c.b.else, n(0))) return simplify(c.b.c)
          return c
        }
        for (const [name, decl] of Object.entries(m.counts)) {
          const body = bodyOf(decl)
          if (!body || !eq(decl.below, row.below) || vars(decl.body).has(decl.j)) continue
          const lifted = simplify(substC(body, {vars: {[row.input]: x(j), [decl.key]: x(key)}, maps: {[carried]: at => indicator(substC(row.body, sub({[row.input]: x(lo), [row.key]: at})))}, flags: {}}))
          if (m.inputs.some(i => vars(lifted).has(i)) || contains(lifted, {op: 'get', map: carried}) || flagsIn(lifted).size) continue
          let request = false; walk(lifted, o => { if (o.op === 'get' && m.inputMaps!.includes(o.map as string)) request = true })
          if (request) continue
          if (eq(normal(lifted), normal(rowBody))) mapped.set(name, aa => rowSize(aa))
          else if (eq(normal(lifted), normal(substC(rowBody, sub({[j]: x(lo)}))))) mapped.set(name, (_aa, bb) => rowSize(bb!))
          else if (vars(lifted).has(j) && vars(lifted).has(lo)) mapped.set(name, count(lifted, true, `rows$${name}`))
        }
        const comparisons = conjs(guard).filter(c => ['<', '<='].includes(c.op) && [...mapped.keys()].some(name => contains(c, {op: 'get', map: name, key: n(0)})))
        for (const comparison of comparisons) {
          const free = [...vars(comparison)].filter(v => m.inputs.includes(v) && v !== row.input)
          if (free.length > 2) continue
          const varsSub = Object.fromEntries(free.map((v, i) => [v, x(i ? w : u)]))
          const mapSub = Object.fromEntries([...mapped].map(([name, read]) => [name, () => read(a, b)]))
          const translate = (c: C) => substC(c, {vars: varsSub, maps: mapSub, flags: {}})
          const hyps = assumptions.filter(c => free.some(v => vars(c).has(v)) && [...vars(c)].every(v => free.includes(v) || m.params.includes(v)))
          const lifted = translate(comparison), constraints = hyps.map(translate)
          if ([lifted, ...constraints].some(c => m.inputs.some(i => vars(c).has(i)))) continue
          let leaks = false; walk([lifted, constraints], o => { if (o.op === 'get' && (m.inputMaps!.includes(o.map as string) || (o.map as string) in m.counts!)) leaks = true })
          if (leaks) continue
          const base: C[] = [not(all(domain(a), domain(b), ...constraints)), lifted]
          const add = (suffix: string, extra: C[]) => {
            if (laws.length >= 32) return
            const law: Law = {name: `${row.name}: stored guard ${action}/${set}${suffix}`, forall: a, keys: [b, ...free.map((_, i) => i ? w : u)], holds: any(...base, ...extra)}
            // Metadata builds charged AST nodes too; it must be a no-op while the route is off.
            if (provenance && row.base) {
            const rowRead = rowSize(a), twins = [...mapped].flatMap(([request, value]) => {
              if (!contains(comparison, {op: 'get', map: request, key: n(0)})) return []
              const read = value(a, b)
              return read.op === 'get' ? [{request, row: read.map, key: text(read.key)}] : []
            })
            const used = new Set<string>(); walk(law.holds, node => {if (node.op === 'get') used.add(node.map as string)})
            if (rowRead.op === 'get') origins.set(law, {kind: 'stored-row-guard', formula: text(law.holds), guard: action, guardFormula: text(guard), membershipMap: row.map, rowInput: row.input, rowCount: rowRead.map, requestSet: carried, width: row.base, halves: free.map((_, i) => i ? w : u), disabled: extra.length > 0, twins, definitions: Object.fromEntries([...used].flatMap(name => {const d = counts[name] ?? m.counts![name]; return d ? [[name, text(d)]] : []}))})
            }
            const proposal = pairLaw(law)
            if (proposal) laws.push(proposal)
          }
          add('', [])
          for (const [i, atom] of noQuorums.entries()) add(` or disabled/${i}`, [atom(a), atom(b)])
        }
      }
    }
  }
  const used = new Set<string>()
  walk(laws, o => { if (o.op === 'get') used.add(o.map as string) })
  for (const name of Object.keys(counts)) if (!used.has(name)) delete counts[name]
  return {counts, laws}
}
