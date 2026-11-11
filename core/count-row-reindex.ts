// Untrusted row transport. Exact mode checks every chosen linear form. Offset
// mode lazily caches demanded indices per source/layout and verifies each reused
// row against its current form. The enclosing complete checker still owns acceptance.
import {type Goal, type Tree, canon} from '../kernel/kernel.ts'
import {type Constraint, type Lin} from './solver.ts'
export type CountReindexStats = {hits: number, layouts: number}
export function countRowReindexer(target: Goal, options: {offsets?: boolean, stats?: CountReindexStats} = {}) {
  const layouts = new WeakMap<Goal, Map<string, (number | undefined)[]>>()
  const ids = new WeakMap<Lin, string>(), hypotheses = new Map<string, number>(), sources = new WeakMap<Goal, Map<number, number>>()
  const groups = new WeakMap<Constraint[], Map<string, number[]>>(), all = new WeakMap<Constraint[], Map<string, number>>()
  const id = (row: Lin): string => { let key = ids.get(row); if (key === undefined) {key = canon(row); ids.set(row, key)} return key }
  for (const [i, h] of target.hyps.entries()) {const key = JSON.stringify(h); if (!hypotheses.has(key)) hypotheses.set(key, i)}
  const tag = (row: Constraint, remap?: Map<number, number>): string | undefined => {
    const source = row.src
    if (!source) return
    if ('fact' in source) {const i = remap ? remap.get(source.fact) : source.fact; return i === undefined ? undefined : 'f:' + i}
    if ('atom' in source) return 'a'
    if ('nat' in source) return 'n:' + source.nat
    if ('term' in source) return 't:' + source.term
    return 'p:' + JSON.stringify(source.pair)
  }
  return (source: Goal, before: Constraint[], after: Constraint[]) => {
    let remap = sources.get(source)
    if (!remap) {
      remap = new Map()
      for (const [i, h] of source.hyps.entries()) {const found = hypotheses.get(JSON.stringify(h)); if (found !== undefined) remap.set(i, found)}
      sources.set(source, remap)
    }
    const key = options.offsets ? JSON.stringify([before.map(r => tag(r, remap) ?? null), after.map(r => tag(r) ?? null)]) : undefined
    let cache = layouts.get(source)
    const cached = key === undefined ? undefined : cache?.get(key)
    if (cached && options.stats) options.stats.hits++
    const exact = (i: number): number | undefined => {
      if (!Number.isSafeInteger(i) || i < 0) return
      if (i >= before.length) return i - before.length + after.length // appended product rows
      let byTag = groups.get(after)
      if (!byTag) {
        byTag = new Map()
        after.forEach((row, index) => {const name = tag(row); if (name !== undefined) {const list = byTag!.get(name) ?? []; list.push(index); byTag!.set(name, list)}})
        groups.set(after, byTag)
      }
      const row = before[i]!, key = id(row.lin), origin = tag(row, remap)
      for (const j of origin === undefined ? [] : byTag.get(origin) ?? []) if (id(after[j]!.lin) === key) return j
      // A changed assumption can yield the same row through a path atom or a
      // different hypothesis. This fallback is still exact, with no solver.
      let fallback = all.get(after)
      if (!fallback) {fallback = new Map(); after.forEach((r, j) => {const k = id(r.lin); if (!fallback!.has(k)) fallback!.set(k, j)}); all.set(after, fallback)}
      return fallback.get(key)
    }
    if (key === undefined) return exact
    const indices: (number | undefined)[] = cached ?? []
    if (!cached) {
      if (!cache) {cache = new Map(); layouts.set(source, cache)}
      if (cache.size >= 64) cache.delete(cache.keys().next().value!)
      cache.set(key, indices)
      if (options.stats) options.stats.layouts++
    }
    return (i: number): number | undefined => {
      if (!Number.isSafeInteger(i) || i < 0) return
      if (i >= before.length) return i - before.length + after.length
      const previous = indices[i]
      if (previous !== undefined && after[previous] && id(before[i]!.lin) === id(after[previous]!.lin)) return previous
      return indices[i] = exact(i)
    }
  }
}
// The missing operation branches are contradictory interval bounds. Emit
// their two-input linear derivation directly; decline any other shape.
export function operationRefutation(rows: Constraint[], operation: string): Tree | undefined {
  let upper: {index: number, constant: number} | undefined, lower: typeof upper
  for (const [index, row] of rows.entries()) {
    const names = Object.keys(row.lin).filter(name => name !== '1' && row.lin[name] !== 0), constant = row.lin['1'] ?? 0
    if (!Number.isSafeInteger(constant)) continue
    if (!names.length && constant > 0) return {leaf: [{kind: 'input', index}]}
    if (names.length !== 1 || names[0] !== operation) continue
    if (row.lin[operation] === 1 && (!upper || constant > upper.constant)) upper = {index, constant}
    if (row.lin[operation] === -1 && (!lower || constant > lower.constant)) lower = {index, constant}
  }
  if (upper && lower && upper.constant + lower.constant > 0) return {leaf: [{kind: 'input', index: upper.index}, {kind: 'input', index: lower.index}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]}
  return undefined
}
