// UNTRUSTED search scopes, not consequences of the source goal. A caller must
// prove every proposed cut under its scope and retain/check its branch guards.
import {type C, type E, type Machine, same, n, walkOnce, x} from '../machine.ts'
import {type CountCert, type CountDecl, type CountInst, type Goal, type Path, substC, substE, truth} from '../../kernel/kernel.ts'
import {countsForReads} from '../count-facts.ts'

type Atom = Extract<C, {a: E}>
type Cell = Extract<E, {op: 'get'}>
const id = (value: unknown): string => JSON.stringify(value)

// Source goals are shared by many candidate queries. Cache only syntactic
// hints (never truth/proofs), and do not recursively scan their count-witness
// tail for each frame. An oversized or cyclic tail cannot suppress count hints.
const goalHints = new WeakMap<Goal, {hyps: C[], atoms: Atom[]}>()
function scalarHints(goal: Goal): Atom[] {
  const cached = goalHints.get(goal)
  if (cached?.hyps === goal.hyps) return cached.atoms
  const atoms: Atom[] = [], pending: unknown[] = [goal.hyps], seen = new Set<object>()
  let left = 20000
  while (pending.length && --left >= 0 && atoms.length < 128) {
    const value = pending.pop()
    if (!value || typeof value !== 'object' || seen.has(value)) continue
    seen.add(value)
    const c = value as Partial<Atom>
    if ((c.op === '<' || c.op === '<=' || c.op === '=') && c.a?.op === 'get' && c.b?.op === 'get'
      && ['var', 'const'].includes(c.a.key?.op) && ['var', 'const'].includes(c.b.key?.op)) atoms.push({op: c.op, a: c.a, b: c.b})
    const children = Object.values(value)
    for (let i = children.length - 1; i >= 0; i--) pending.push(children[i])
  }
  goalHints.set(goal, {hyps: goal.hyps, atoms})
  return atoms
}

// Reject cycles and oversized/deep inputs before the recursive AST helpers run.
// This is a proposal budget, never a claim about the machine's validity.
function bounded(value: unknown): boolean {
  const active = new WeakSet<object>(), done = new WeakSet<object>()
  let left = 20000
  const visit = (v: unknown, depth: number): boolean => {
    if (--left < 0 || depth > 80) return false
    if (!v || typeof v !== 'object') return true
    if (active.has(v)) return false
    if (done.has(v)) return true
    active.add(v)
    for (const child of Object.values(v)) if (!visit(child, depth + 1)) return false
    active.delete(v); done.add(v)
    return true
  }
  return visit(value, 0)
}

// Most source instances are Boolean partitions. They cannot yield a scalar
// guard; reject them before scanning the machine, flags, or optional goal.
function scalarSource(ds: CountDecl[], reads: CountCert['reads'], inst: CountInst): boolean {
  const selected = new Set(inst.terms.filter(([k]) => k !== 0).map(([, name]) => name))
  const maps = new Set(reads.filter(([name]) => selected.has(name)).map(r => r[1]))
  let left = 4096
  for (const d of ds) {
    if (!maps.has(d.map)) continue
    const pending: unknown[] = [d.body], seen = new Set<object>()
    while (pending.length && --left >= 0) {
      const value = pending.pop()
      if (!value || typeof value !== 'object' || seen.has(value)) continue
      seen.add(value)
      const o = value as Partial<Atom>
      if ((o.op === '<' || o.op === '<=' || o.op === '=') && o.a?.op === 'get' && o.b?.op === 'get'
        && [o.a.key, o.b.key].some(key => key.op === 'var' && key.name === d.key)) return true
      pending.push(...Object.values(value))
    }
    if (left < 0) return false
  }
  return false
}

/** At most eight deterministic, witness-free scalar comparison conjunctions.
 * Universal equalities only suggest substitutions; nothing here asserts them,
 * adds a hypothesis, mutates the path, or establishes a proof. */
export function countScalarGuards(m: Machine, ds: CountDecl[], reads: CountCert['reads'], inst: CountInst, root: Path, goal?: Goal): C[][] {
  try {
    const selected = new Set(inst.terms.map(([, name]) => name))
    const frame = !!goal && inst.terms.length === 2 && reads.some(([name, map]) => selected.has(name) && map.endsWith('#'))
    if (!frame && !scalarSource(ds, reads, inst)) return []
    const picked = reads.filter(([name]) => selected.has(name)), maps = new Set(picked.map(r => r[1]))
    if (!bounded([ds.filter(d => maps.has(d.map)), picked, inst, m.inputs, m.params, m.inputMaps, m.step.flags])) return []
    return propose(m, ds, reads, inst, root, goal)
  } catch {
    // Malformed/unsupported ASTs are not a reason to guess a source scope.
    return []
  }
}

function propose(m: Machine, ds: CountDecl[], reads: CountCert['reads'], inst: CountInst, root: Path, goal?: Goal): C[][] {
  const selected = new Set(inst.terms.filter(([k]) => k !== 0).map(([, name]) => name))
  if (!selected.size || inst.terms.some(([k]) => !Number.isSafeInteger(k))) return []
  const flags = Object.entries(m.step.flags ?? {})
  const opaqueFlags = Object.fromEntries(flags.map(([name]) => [name, same(x(`?${name}`), n(1))]))
  const normal = {maps: {}, flags: opaqueFlags}
  // countsForReads substitutes with no flag environment. Encode raw references
  // first, preserving the production ?name representation rather than unfolding
  // a universal predicate into an unbound count member.
  const picked = reads.filter(([name]) => selected.has(name))
  const declarations = ds.filter(d => picked.some(r => r[1] === d.map)).map(d => ({...d,
    below: substE(d.below, {...normal, vars: {}}), body: substE(d.body, {...normal, vars: {}})}))
  const counts = countsForReads(declarations, picked)
  if (!counts || counts.length !== selected.size || new Set(picked.map(r => r[0])).size !== picked.length) return []
  const forbidden = new Set([inst.wit, ...reads.map(r => r[0]), ...ds.map(d => d.key)])
  for (const [name, q] of flags) {
    forbidden.add(`?${name}`)
    if (q.op === 'all') for (const key of [q.key, ...q.keys ?? []]) forbidden.add(key)
  }
  for (const write of Object.values(m.step.maps ?? {})) if ('each' in write) forbidden.add(write.each)
  const allowed = new Set([...m.inputs, ...m.params])
  for (const read of picked) walkOnce(read[2], (o: any) => { if (o.op === 'var') allowed.add(o.name) })
  for (const name of forbidden) allowed.delete(name)
  const used = new Set<string>([...allowed, ...forbidden])
  walkOnce([declarations, flags], (o: any) => { if (o.op === 'var') used.add(o.name) })
  let member = 'scalar$member'
  while (used.has(member)) member += '$'
  const countMaps = new Set([...ds.map(d => d.map), ...Object.keys(m.counts ?? {})])
  const primitiveMaps = (value: unknown): Set<string> => {
    const out = new Set<string>(), followed = new Set<string>()
    const visit = (part: unknown): void => {
      walkOnce(part, (o: any) => {
        if (o.op === 'get' && !countMaps.has(o.map)) out.add(o.map)
        const name = o.op === 'flag' ? o.name : o.op === 'var' && o.name.startsWith('?') ? o.name.slice(1) : undefined
        if (name !== undefined && !followed.has(name)) {
          followed.add(name)
          const flag = flags.find(([key]) => key === name)?.[1]
          if (flag) visit(flag)
        }
      })
    }
    visit(value)
    return out
  }
  const positive = new Set(inst.terms.filter(([k]) => k > 0).map(([, name]) => name)), carried = new Set(m.inputMaps ?? [])
  const preferred = new Set(counts.filter(c => positive.has(c.v)).flatMap(c => [...primitiveMaps(c.body)].filter(map => carried.has(map))))
  const relevant = preferred.size ? preferred : new Set(counts.flatMap(c => [...primitiveMaps(c.body)]))
  // Named flags remain opaque, rather than recursively following aliases (which
  // may be cyclic). Only active, single-member universal flags supply anchors.
  const cell = (e: E): e is Cell => e.op === 'get' && !countMaps.has(e.map)
    && (e.key.op === 'var' ? allowed.has(e.key.name) : e.key.op === 'const' && Number.isSafeInteger(e.key.value) && e.key.value >= 0)
  const memberCell = (e: E): e is Cell => e.op === 'get' && !countMaps.has(e.map) && e.key.op === 'var' && e.key.name === member
  const anchors = new Map<string, E>()
  for (const [name, q] of flags) {
    if (q.op !== 'all' || q.keys?.length || truth(same(x(`?${name}`), n(1)), root) !== true) continue
    if (![...primitiveMaps(q.c)].some(map => relevant.has(map))) continue
    const body = substC(q.c, {...normal, vars: {[q.key]: x(member)}})
    walkOnce(body, (o: any) => {
      if (o.op !== '=') return
      for (const [from, to] of [[o.a, o.b], [o.b, o.a]] as [E, E][]) {
        if (!memberCell(from) || !cell(to)) continue
        // Stable first anchor avoids a Cartesian product of equality choices.
        const key = id(from)
        if (!anchors.has(key) && anchors.size < 32) anchors.set(key, to)
      }
    })
  }
  const atoms: Atom[] = [], seen = new Set<string>()
  const add = (c: Atom): void => {
    if (atoms.length >= 32 || !cell(c.a) || !cell(c.b) || id(c.a) === id(c.b) || id(c.a.key) === id(c.b.key)) return
    // Equality is symmetric; strict/non-strict comparisons retain direction.
    const key = c.op === '=' ? id([c.op, ...[id(c.a), id(c.b)].sort()]) : id(c)
    if (!seen.has(key)) { seen.add(key); atoms.push(c) }
  }
  const maps = Object.fromEntries([...new Set([...anchors.values()].flatMap(e => e.op === 'get' ? [e.map] : [])),
    ...counts.flatMap(c => [...primitiveMaps(c.body)])].map(map => [map, (key: E): E => anchors.get(id({op: 'get', map, key})) ?? {op: 'get', map, key}]))
  for (const count of counts) {
    const body = substE(count.body, {...normal, vars: {[count.key]: x(member)}})
    walkOnce(body, (o: any) => {
      if (o.op !== '<' && o.op !== '<=' && o.op !== '=') return
      let mentions = false
      walkOnce(o, (v: any) => { if (v.op === 'var' && v.name === member) mentions = true })
      if (!mentions) return
      const comparison = substC(o, {vars: {}, maps, flags: opaqueFlags})
      if (comparison.op === '<' || comparison.op === '<=' || comparison.op === '=') add(comparison)
    })
  }
  const pair = (c: Atom): string => id([id((c.a as Cell).key), id((c.b as Cell).key)].sort())
  const goalPairs = new Set(atoms.map(pair)), rowKeys = new Set<string>()
  for (const read of picked) walkOnce(read[2], (o: any) => {
    if (o.op === 'var' && allowed.has(o.name)) rowKeys.add(id(o))
  })
  // A post body can mention its writing actor only in an update condition,
  // while the carried partner is keyless. Keep those actual input references
  // and active anchor destinations, not all inputs or arbitrary goal rows.
  const inputs = new Set(m.inputs)
  for (const count of counts) walkOnce(count.body, (o: any) => {
    if (o.op === 'var' && inputs.has(o.name) && allowed.has(o.name)) rowKeys.add(id(o))
  })
  for (const anchor of anchors.values()) if (cell(anchor)) rowKeys.add(id(anchor.key))
  // Frame hints must relate a candidate's own row pair, not just any input or
  // witness that occurs in the large source goal. Count comparisons above may
  // also establish the row-to-anchor pair when the carried read is keyless.
  if (goal) for (const hint of scalarHints(goal)) {
    if (cell(hint.a) && cell(hint.b)
      && (goalPairs.has(pair(hint)) || rowKeys.has(id(hint.a.key)) && rowKeys.has(id(hint.b.key)))) add(hint)
  }
  const fields = (c: Atom): string => id([(c.a as Cell).map, (c.b as Cell).map].sort())
  const out: C[][] = [], scopes = new Set<string>()
  const emit = (cs: Atom[]): void => {
    if (out.length >= 8) return
    const status = cs.map(c => truth(c, root))
    if (status.includes(false)) return
    const open = cs.filter((_, i) => status[i] !== true)
    if (!open.length) return
    const key = id(open.map(id).sort())
    if (!scopes.has(key)) { scopes.add(key); out.push(open) }
  }
  const strict = atoms.filter(c => c.op === '<'), equal = atoms.filter(c => c.op === '=')
  // Boolean post/pre frames use equal-view laws, so keep their paired field
  // equalities before optional strict-order alternatives consume the cap.
  if (inst.terms.length === 2 && picked.some(([, map]) => map.endsWith('#'))) {
    for (let i = 0; i < equal.length; i++) for (const other of equal.slice(i + 1)) {
      if (pair(equal[i]!) === pair(other) && fields(equal[i]!) !== fields(other)) emit([equal[i]!, other])
    }
  }
  // Reserve useful lexicographic refinements alongside each strict branch,
  // instead of letting a long tail of singleton comparisons crowd them out.
  for (const c of strict) {
    emit([c])
    for (const eq of equal) if (pair(c) === pair(eq) && fields(c) !== fields(eq)) emit([eq, c])
    if (out.length >= 8) break
  }
  for (let i = 0; i < equal.length; i++) {
    const eq = equal[i]!
    emit([eq])
    for (const other of equal.slice(i + 1)) if (pair(eq) === pair(other) && fields(eq) !== fields(other)) emit([eq, other])
  }
  for (const c of atoms) if (c.op === '<=') emit([c])
  return out
}
