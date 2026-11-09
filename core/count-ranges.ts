// A 0/1-bodied count is at most its key bound. Propose its ordinary witness-
// bearing range instance when a model violates the bound, not eagerly for
// every read. Nothing is assumed: the unchanged kernel checks the instance.
// Unknown bounds and non-0/1 bodies do not trigger a proposal.
import type {E} from './machine.ts'
import type {CountDecl, CountInst, MapRead} from '../kernel/kernel.ts'
import {countsForReads} from './count-facts.ts'
export const zeroOne = (e: E): boolean => e.op === 'const' ? e.value === 0 || e.value === 1 : e.op === 'if' ? zeroOne(e.then) && zeroOne(e.else) : false
export function rangeInstances(decls: CountDecl[], reads: MapRead[], taken: Iterable<string>, present: CountInst[] = []): CountInst[] {
  const used = new Set(taken), out: CountInst[] = []
  for (const i of present) used.add(i.wit)
  const had = new Set(present.filter(i => i.unit === -1 && i.terms.length === 1 && i.terms[0]![0] === 1).map(i => i.terms[0]![1]))
  let n = 0
  for (const read of reads) {
    if (had.has(read[0])) continue
    const count = countsForReads(decls, [read])?.[0]
    if (!count || !zeroOne(count.body)) continue
    let wit: string
    do wit = `w$range$${n++}`; while (used.has(wit))
    used.add(wit)
    out.push({wit, below: count.below, terms: [[1, read[0]]], unit: -1})
  }
  return out
}
// Inspect only fully valued arithmetic bounds. Unassigned or unsupported
// terms are unknown, not evidence that a model violates a range.
export function rangeViolations(decls: CountDecl[], reads: MapRead[], model: Record<string, number>): MapRead[] {
  const value = (e: E): number | undefined => {
    switch (e.op) {
      case 'const': return e.value
      case 'var': return model[e.name]
      case 'add': { const a = value(e.a), b = value(e.b); return a === undefined || b === undefined ? undefined : a + b }
      case 'mul': { const a = value(e.a); return a === undefined ? undefined : e.k * a }
      case 'sub': { const a = value(e.a), b = value(e.b); return a === undefined || b === undefined ? undefined : Math.max(0, a - b) }
      case 'min': case 'max': { const a = value(e.a), b = value(e.b); return a === undefined || b === undefined ? undefined : e.op === 'min' ? Math.min(a, b) : Math.max(a, b) }
      case 'get': case 'if': case 'prod': case 'proj': case 'tup': return undefined
    }
  }
  return reads.filter(read => {
    const v = model[read[0]]
    if (v === undefined) return false
    const count = countsForReads(decls, [read])?.[0]
    if (!count || !zeroOne(count.body)) return false
    const bound = value(count.below)
    return bound !== undefined && v > bound
  })
}
