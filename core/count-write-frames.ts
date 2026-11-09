// UNTRUSTED written-row count proposals. No equality or frame is assumed here:
// each direction keeps Count.lean's counterexample-key alternative. Only the
// source solver/checker, under its actual row/scalar guards, can discharge it.
import {type C, type E, type Machine, n} from './machine.ts'
import {type Count, type CountCert, type CountDecl, type CountInst} from '../kernel/kernel.ts'
import {countsForReads} from './count-facts.ts'

type Cell = Extract<E, {op: 'get'}>
type Literal = {cell: Cell, positive: boolean}
type Shape = {kind: 'single' | 'intersection' | 'difference', literals: Literal[]}
const stable = (value: unknown): string => JSON.stringify(value, (_, v: unknown) => v && typeof v === 'object' && !Array.isArray(v)
  ? Object.fromEntries(Object.entries(v).sort(([a], [b]) => a.localeCompare(b))) : v)

// These are membership syntaxes, not arbitrary predicates that happen to have
// two atoms (e.g. older-field lexicographic comparisons).
function membership(c: C): Cell | undefined {
  if (c.op === '=') {
    if (c.a.op === 'get' && c.b.op === 'const' && c.b.value === 1) return c.a
    if (c.b.op === 'get' && c.a.op === 'const' && c.a.value === 1) return c.b
  }
  if ((c.op === '<=' && c.a.op === 'const' && c.a.value === 1
    || c.op === '<' && c.a.op === 'const' && c.a.value === 0) && c.b.op === 'get') return c.b
  return undefined
}
function literals(c: C, positive = true): Literal[] | undefined {
  if (c.op === 'not') return literals(c.x, !positive)
  if (c.op === 'and' && positive) {
    const out: Literal[] = []
    for (const child of c.xs) {
      const part = literals(child)
      if (!part || out.length + part.length > 2) return undefined
      out.push(...part)
    }
    return out
  }
  const cell = membership(c)
  return cell && [{cell, positive}]
}
function shape(body: E): Shape | undefined {
  if (body.op !== 'if' || body.then.op !== 'const' || body.then.value !== 1
    || body.else.op !== 'const' || body.else.value !== 0) return undefined
  const ls = literals(body.c)
  if (ls?.length === 1) return ls[0]!.positive ? {kind: 'single', literals: ls} : undefined
  if (!ls || ls.length !== 2 || stable(ls[0]!.cell) === stable(ls[1]!.cell)) return undefined
  const positives = ls.filter(l => l.positive).length
  return positives ? {kind: positives === 2 ? 'intersection' : 'difference', literals: ls} : undefined
}

// Follow value branches, never general reads in a non-Boolean write guard.
// A Booleanized value can be an OR of guarded membership arms after lowering.
function booleanSources(c: C, inputs: ReadonlySet<string>, out: Set<string>, positive = true): void {
  if (c.op === 'not') { booleanSources(c.x, inputs, out, !positive); return }
  if (c.op === 'and' || c.op === 'or') { for (const child of c.xs) booleanSources(child, inputs, out, positive); return }
  const cell = positive && membership(c)
  if (cell && inputs.has(cell.map)) out.add(cell.map)
}
function copySources(value: E, inputs: ReadonlySet<string>, out = new Set<string>()): Set<string> {
  if (value.op === 'get' && inputs.has(value.map)) out.add(value.map)
  if (value.op === 'if') {
    if (value.then.op === 'const' && value.then.value === 1
      && value.else.op === 'const' && value.else.value === 0) booleanSources(value.c, inputs, out)
    copySources(value.then, inputs, out)
    copySources(value.else, inputs, out)
  }
  return out
}

/** Demand IDs are certificate read variables. Inspect PRE declarations at the
 * same keys: expanded post bodies hide the small two-membership shape. Match
 * only incoming counts joining a written map to its actual carried value source.
 * Difference counts deliberately offer both incoming directions: which row is
 * written/equal is a guarded proof obligation, not a syntactic equivalence.
 * No reads/declarations are added, no input is mutated, and at most 32 ordinary
 * unit-zero instances are returned (two-term frames or three-term compensated
 * differences, in a deterministic prefix).
 */
export function proposeWriteCountFrames(m: Machine, ds: CountDecl[], cert: Pick<CountCert, 'reads' | 'insts'>,
  demanded: ReadonlySet<string>, maxFacts = 32): CountInst[] {
  const cap = Number.isSafeInteger(maxFacts) && maxFacts >= 0 ? Math.min(maxFacts, 32) : 0
  if (!cap || !demanded.size) return []
  // Include ALL names, including unrelated declarations, flags, bindings, map
  // keys and existing witness bounds. Iterative traversal also handles sharing.
  const used = new Set<string>(), seenObjects = new Set<object>(), pending: unknown[] = [m, ds, cert, [...demanded]]
  while (pending.length) {
    const value = pending.pop()
    if (typeof value === 'string') used.add(value)
    else if (value && typeof value === 'object' && !seenObjects.has(value)) {
      seenObjects.add(value)
      for (const [key, child] of Object.entries(value)) { used.add(key); pending.push(child) }
    }
  }
  let serial = 0
  const fresh = (): string => {
    while (used.has(`writeFrame$${serial}`)) serial++
    const name = `writeFrame$${serial++}`; used.add(name); return name
  }
  const writers = new Map<string, Set<string>>(), inputs = new Set(m.inputMaps ?? [])
  for (const [map, write] of Object.entries(m.step.maps ?? {})) {
    const sources = copySources(write.value, inputs)
    if (sources.size) writers.set(map, sources)
  }
  if (!writers.size) return []
  const declarations = new Map<string, CountDecl>()
  for (const d of ds) if (!declarations.has(d.map)) declarations.set(d.map, d)
  const indexKey = (map: string, kind: Shape['kind'], below: E) => stable([map, kind, below])
  const incoming = new Map<string, Count[]>(), readIds = new Set<string>()
  for (const read of cert.reads) {
    if (readIds.has(read[0])) continue
    readIds.add(read[0])
    if (read[1].endsWith('#')) continue
    const c = countsForReads(ds, [read])?.[0], s = c && shape(c.body)
    if (!c || !s) continue
    for (const [map, sources] of writers) {
      if (!s.literals.some(l => sources.has(l.cell.map)) || s.kind !== 'single' && !s.literals.some(l => l.cell.map === map)) continue
      const key = indexKey(map, s.kind, c.below), group = incoming.get(key) ?? []
      group.push(c); incoming.set(key, group)
    }
  }
  // Coefficient-vector dedupe ignores term order and combines repeated IDs.
  // Each direction has its own signature; an existing reverse does not erase
  // the still-missing forward direction.
  const signature = (i: Pick<CountInst, 'terms' | 'unit'>): string => {
    const coefficients = new Map<string, number>()
    for (const [z, id] of i.terms) coefficients.set(id, (coefficients.get(id) ?? 0) + z)
    return stable([i.unit, [...coefficients].filter(([, z]) => z !== 0).sort(([a], [b]) => a.localeCompare(b))])
  }
  const emitted = new Set(cert.insts.map(signature)), out: CountInst[] = []
  readIds.clear()
  for (const read of cert.reads) {
    if (readIds.has(read[0])) continue
    readIds.add(read[0])
    if (!demanded.has(read[0]) || !read[1].endsWith('#')) continue
    const preRead: typeof read = [read[0], read[1].slice(0, -1), read[2]]
    const before = countsForReads(ds, [preRead])?.[0], s = before && shape(before.body)
    const postDecl = declarations.get(read[1])
    if (!before || !s || !postDecl) continue
    // Instantiate the real post bound without traversing the expanded body.
    const post = countsForReads([{...postDecl, body: n(0)}], [read])?.[0]
    if (!post || stable(post.below) !== stable(before.below)) continue
    for (const map of new Set(s.literals.map(l => l.cell.map))) {
      const kinds: Shape['kind'][] = s.kind === 'intersection' && s.literals.every(l => l.cell.map === map) ? [s.kind, 'single'] : [s.kind]
      for (const kind of kinds) for (const c of incoming.get(indexKey(map, kind, post.below)) ?? []) {
        if (c.v === read[0]) continue
        // A changed row need not equal its old value. Keep the old directed
        // difference as a compensating term: d(new,B) <= d(old,B)+d(new,old).
        // Both incoming orientations remain candidates, proved under the
        // actual write/row guards, never asserted by this syntactic match.
        if (s.kind === 'difference') {
          const previous = cert.reads.find(r => r[1] === preRead[1] && stable(r[2]) === stable(preRead[2]))
          if (previous) {
            const terms: CountInst['terms'] = [[1, read[0]], [-1, previous[0]], [-1, c.v]], key = signature({terms, unit: 0})
            if (!emitted.has(key)) {
              if (out.length >= cap) return out
              emitted.add(key); out.push({wit: fresh(), below: post.below, terms, unit: 0})
            }
          }
        }
        for (const sign of [1, -1]) {
          if (out.length >= cap) return out
          const terms: CountInst['terms'] = [[sign, read[0]], [-sign, c.v]], key = signature({terms, unit: 0})
          if (emitted.has(key)) continue
          emitted.add(key); out.push({wit: fresh(), below: post.below, terms, unit: 0})
        }
      }
    }
  }
  return out
}
