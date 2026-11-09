// A count whose body is 0 or 1 at every key is at most the number of keys it ranges over. The instance `count ≤ below`
// (Count.lean's countHyp with the one term at +1 and the unit at −1: the count is at most its bound, or some key below
// the bound has a body above 1, which no 0/1 body has) joins a counted attempt's selection as soon as a model of the goal
// puts such a count above its bound (`rangeViolations`), so that model is never kept and never returned as a refutation.
// Nothing is assumed: the instance is an ordinary count instance the kernel checks. A body that is not 0/1 gets no range;
// a goal whose models respect every range pays nothing.
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
// The reads whose count the model puts above its bound: the read's variable and the bound's variables all valued by the
// model (a bound over params and state, as counts declare them); anything the model leaves open is not a violation.
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
