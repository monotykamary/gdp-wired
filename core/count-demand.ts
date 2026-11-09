// Untrusted, demand-directed proposals for the existing single-witness count rule.
import {type C, type E, x} from './machine.ts'
import {type Count, type CountInst, substE} from '../kernel/kernel.ts'

export type CountDemandOptions = {
  /** Restrict positive pairs to these IDs; at least one ID must be demanded.
   * Omit to visit demanded/demanded pairs, then raw carried indicators,
   * then other partners sharing a primitive read with the demanded body. */
  pairs?: readonly (readonly [string, string])[]
  /** Output limit, clamped to 128 (default 128). */
  maxFacts?: number
  /** Disable partition emission when this call is only a bounded pair request. */
  partitions?: boolean
  /** Shared scan/AST/search budget, clamped to 1,000,000 (default 200,000).
   * Exhaustion returns a sound but possibly incomplete prefix, never a fallback pool. */
  maxWork?: number
  /** Names already used by goal hypotheses or other certificate witnesses. */
  reserved?: Iterable<string>
}

type Bool = boolean | {atom: string} | {not: Bool} | {and: Bool[]} | {or: Bool[]}
type View = {count: Count, atoms: string[], mask?: number, members: Set<string>, indicator?: string}
type Family = {atoms: string[], regions: Map<number, View>, members: Set<string>}
const stable = (v: unknown): string => JSON.stringify(v, (_, a: unknown) => a && typeof a === 'object' && !Array.isArray(a)
  ? Object.fromEntries(Object.entries(a).sort(([a], [b]) => a.localeCompare(b))) : a)
const limit = (n: number | undefined, fallback: number, cap: number): number => n === undefined ? fallback
  : Number.isSafeInteger(n) && n >= 0 ? Math.min(n, cap) : 0
const evaluate = (b: Bool, values: Map<string, boolean>): boolean => typeof b === 'boolean' ? b
  : 'atom' in b ? values.get(b.atom)! : 'not' in b ? !evaluate(b.not, values)
  : 'and' in b ? b.and.every(c => evaluate(c, values)) : b.or.some(c => evaluate(c, values))
// Equality is symmetric; no arithmetic predicate is identified with membership
// merely because it agrees on 0/1 values. Raw get bodies remain candidates only.
const atomKey = (c: C): string => c.op === '=' && stable(c.a) > stable(c.b)
  ? stable({...c, a: c.b, b: c.a}) : stable(c)

/** Demand is a set of Count.v IDs read by the goal or a numeric refuted core.
 * This function neither extracts the core nor asserts any returned inequality.
 * Pass its ordinary CountInsts through countedGoal/mcGoal and checkCounted/checkMC.
 * Every instance retains the SAME pointwise witness alternative, including raw
 * map-valued "indicators" and positive pairs that are not actually disjoint.
 *
 * Only same-bound groups containing a demanded ID are normalized. Within them,
 * two-atom truth tables index declared singleton regions (no synthetic counts).
 * Requested indicators get both partition directions; requested regions also
 * request identities containing that region. Positive pairs use only singleton
 * memberships they read, and three-region families selected by demanded regions
 * or a primitive map read shared with the positive bodies. There is no exhaustive
 * union pool, no Cartesian product of all positive pairs, and no final slice.
 *
 * Work includes every input/AST scan and each candidate visit. Individual input
 * ASTs are limited to 4096 nodes and depth 128 before recursive normalization;
 * an incomplete name scan returns [] so witnesses cannot capture unseen names.
 * Runtime is bounded by maxWork times these fixed local bounds; memory is O(maxWork).
 * No input-position cap: late demanded families are not discarded at count 128.
 */
export function proposeCountDemand(counts: Count[], demanded: ReadonlySet<string>, options: CountDemandOptions = {}): CountInst[] {
  const cap = limit(options.maxFacts, 128, 128)
  let work = limit(options.maxWork, 200_000, 1_000_000)
  const take = (): boolean => work > 0 && (--work >= 0)
  if (!cap || !work || !demanded.size) return []
  const used = new Set<string>(), byId = new Map<string, Count>()
  // Freshness must cover even counts in unrelated families, not only emitted terms.
  const inspect = (value: unknown): boolean => {
    const stack: [unknown, number][] = [[value, 0]]
    let nodes = 0
    while (stack.length) {
      if (!take() || ++nodes > 4096) return false
      const [v, depth] = stack.pop()!
      if (depth > 128) return false
      if (typeof v === 'string') used.add(v)
      else if (v && typeof v === 'object') {
        for (const child of Object.values(v)) {
          if (!take()) return false
          stack.push([child, depth + 1])
        }
      }
    }
    return true
  }
  for (const c of counts) {
    if (!take() || !inspect(c)) return []
    if (!byId.has(c.v)) byId.set(c.v, c) // matches kernel findCount
  }
  for (const name of options.reserved ?? []) { if (!take()) return []; used.add(name) }
  let serial = 0
  const fresh = (): string | undefined => {
    while (take()) {
      const name = `demand$${serial++}`
      if (!used.has(name)) { used.add(name); return name }
    }
    return undefined
  }
  const member = fresh()
  if (!member) return []
  const requested: Count[] = [], bounds = new Set<string>()
  for (const id of demanded) {
    if (!take()) return []
    const c = byId.get(id)
    if (c) { requested.push(c); bounds.add(stable(c.below)) }
  }
  if (!requested.length) return []
  const groups = new Map<string, Count[]>()
  // Demand first also chooses the demanded representative of duplicate regions.
  for (const c of requested) {
    const key = stable(c.below), group = groups.get(key) ?? []
    group.push(c); groups.set(key, group)
  }
  for (const c of byId.values()) {
    if (!take()) return []
    if (demanded.has(c.v)) continue
    const key = stable(c.below)
    if (bounds.has(key)) groups.get(key)!.push(c)
  }
  const out: CountInst[] = [], emitted = new Set<string>()
  const emit = (below: E, terms: [number, string][]): void => {
    if (out.length >= cap || !take()) return
    // Do not emit identities with self-cancellation or repeated cover IDs.
    if (new Set(terms.map(([, id]) => id)).size !== terms.length) return
    const signature = stable([below, [...terms].sort((a, b) => a[1].localeCompare(b[1]))])
    if (emitted.has(signature)) return
    const wit = fresh()
    if (!wit) return
    emitted.add(signature); out.push({wit, below, terms, unit: 0})
  }
  for (const cs of groups.values()) {
    if (!work || out.length >= cap) break
    const views = new Map<string, View>(), families = new Map<string, Family>()
    const indicators = new Map<string, View[]>(), memberships = new Map<string, View[]>()
    for (const count of cs) {
      if (!take()) break
      const e = substE(count.body, {vars: {[count.key]: x(member)}, maps: {}, flags: {}})
      const members = new Set<string>(), atoms = new Set<string>()
      const scan = (v: unknown): void => {
        if (!take() || !v || typeof v !== 'object') return
        if ('op' in v && v.op === 'get') members.add(stable(v))
        for (const child of Object.values(v)) scan(child)
      }
      scan(e)
      const cond = (c: C): Bool | undefined => {
        if (!take() || c.op === 'flag' || c.op === 'all') return undefined
        if (c.op === 'not') { const b = cond(c.x); return b === undefined ? undefined : {not: b} }
        if (c.op === 'and' || c.op === 'or') {
          const bs = c.xs.map(cond)
          return bs.some(b => b === undefined) ? undefined : {[c.op]: bs as Bool[]} as Bool
        }
        const a = atomKey(c); atoms.add(a)
        return atoms.size > 2 ? undefined : {atom: a}
      }
      const body = (v: E): Bool | undefined => {
        if (!take()) return undefined
        if (v.op === 'const') return v.value === 0 ? false : v.value === 1 ? true : undefined
        if (v.op !== 'if') return undefined
        const c = cond(v.c), a = body(v.then), b = body(v.else)
        return c === undefined || a === undefined || b === undefined ? undefined
          : {or: [{and: [c, a]}, {and: [{not: c}, b]}]}
      }
      const f = body(e), keys = [...atoms].sort()
      const view: View = {count, atoms: keys, members}
      if (f !== undefined && keys.length <= 2) {
        view.mask = 0
        for (let bits = 0; bits < 2 ** keys.length; bits++) {
          if (evaluate(f, new Map(keys.map((k, i) => [k, !!(bits & (1 << i))])))) view.mask |= 1 << bits
        }
      }
      if (!work) break // never use partial metadata
      if (e.op === 'get') view.indicator = atomKey({op: '=', a: e, b: {op: 'const', value: 1}})
      else if (keys.length === 1 && (view.mask === 1 || view.mask === 2)) view.indicator = keys[0]
      views.set(count.v, view)
      if (view.indicator) {
        const list = indicators.get(view.indicator) ?? []; list.push(view); indicators.set(view.indicator, list)
        for (const m of members) { const vs = memberships.get(m) ?? []; vs.push(view); memberships.set(m, vs) }
      }
      if (keys.length !== 2 || ![1, 2, 4, 8].includes(view.mask ?? 0)) continue
      const id = stable(keys), family = families.get(id) ?? {atoms: keys, regions: new Map<number, View>(), members: new Set<string>()}
      if (!family.regions.has(view.mask!)) family.regions.set(view.mask!, view)
      for (const m of members) family.members.add(m)
      families.set(id, family)
    }
    const byAtom = new Map<string, Family[]>(), byMember = new Map<string, Family[]>(), demandFamilies = new Set<Family>()
    for (const family of families.values()) {
      if (!take()) break
      for (const atom of family.atoms) { const fs = byAtom.get(atom) ?? []; fs.push(family); byAtom.set(atom, fs) }
      for (const m of family.members) { const fs = byMember.get(m) ?? []; fs.push(family); byMember.set(m, fs) }
      if ([...family.regions.values()].some(v => demanded.has(v.count.v))) demandFamilies.add(family)
    }
    const partition = (v: View, family: Family, required?: string): void => {
      if (!take() || out.length + 2 > cap) return
      let mask: number
      if (v.indicator) {
        const index = family.atoms.indexOf(v.indicator)
        if (index < 0) return
        const on = v.mask !== 1
        mask = [0, 1, 2, 3].reduce((m, bits) => !!(bits & (1 << index)) === on ? m | (1 << bits) : m, 0)
      } else if (stable(v.atoms) === stable(family.atoms) && v.mask !== undefined) mask = v.mask
      else return
      const parts: View[] = []
      for (const bit of [1, 2, 4, 8]) if (mask & bit) {
        const part = family.regions.get(bit)
        if (!part) return
        parts.push(part)
      }
      if (parts.length < 2 || (required && !parts.some(p => p.count.v === required))) return
      for (const sign of [1, -1]) emit(v.count.below, [[sign, v.count.v], ...parts.map(p => [-sign, p.count.v] as [number, string])])
    }
    if (options.partitions !== false) for (const c of requested) {
      if (!take() || out.length >= cap) break
      const v = views.get(c.v)
      if (!v) continue
      if (v.indicator) for (const f of byAtom.get(v.indicator) ?? []) { if (!work) break; partition(v, f) }
      else {
        const f = families.get(stable(v.atoms))
        if (!f) continue
        partition(v, f)
        for (const atom of f.atoms) for (const indicator of indicators.get(atom) ?? []) {
          if (!work) break
          partition(indicator, f, c.v)
        }
      }
    }
    const seenPairs = new Set<string>()
    const pair = (aId: string, bId: string): void => {
      if (!take() || out.length >= cap || aId === bId || (!demanded.has(aId) && !demanded.has(bId))) return
      const a = views.get(aId), b = views.get(bId)
      if (!a || !b) return
      const key = stable([aId, bId].sort())
      if (seenPairs.has(key)) return
      seenPairs.add(key)
      const selected = new Set<Family>(), covers = new Set<View>()
      for (const f of demandFamilies) { if (!take()) return; selected.add(f) }
      for (const m of new Set([...a.members, ...b.members])) {
        if (!take()) return
        for (const f of byMember.get(m) ?? []) { if (!take()) return; selected.add(f) }
        for (const v of memberships.get(m) ?? []) { if (!take()) return; covers.add(v) }
      }
      const add = (cover: View[]): void => emit(a.count.below, [[1, aId], [1, bId], ...cover.map(v => [-1, v.count.v] as [number, string])])
      // A cover is considered only here, at the requested pair, never pre-expanded.
      for (const f of selected) {
        if (!take() || out.length >= cap) return
        const cover = [2, 4, 8].map(bit => f.regions.get(bit))
        if (cover.every((v): v is View => v !== undefined)) add(cover)
      }
      for (const v of covers) { if (!take() || out.length >= cap) return; add([v]) }
    }
    if (options.pairs) {
      for (const [a, b] of options.pairs) { if (!work || out.length >= cap) break; pair(a, b) }
    } else {
      const ds = cs.filter(c => demanded.has(c.v))
      for (let i = 0; i < ds.length && work && out.length < cap; i++) {
        for (let j = i + 1; j < ds.length && work && out.length < cap; j++) pair(ds[i]!.v, ds[j]!.v)
      }
      // Raw carried indicators are useful partners even when absent from the
      // goal/core. Visit them before region columns used primarily as covers.
      // This is an AST-shape choice, independent of map names or read indices.
      for (const raw of [true, false]) for (const a of ds) for (const b of cs) {
        if (!take() || out.length >= cap) break
        if (demanded.has(b.v) || (b.body.op === 'get') !== raw) continue
        const left = views.get(a.v), right = views.get(b.v)
        if (!raw && (!left || !right || ![...left.members].some(m => right.members.has(m)))) continue
        pair(a.v, b.v)
      }
    }
  }
  return out
}
