// A count whose body is 0 or 1 at every key is at most the number of keys it ranges over. For every such count a goal
// reads, the instance `count ≤ below` (Count.lean's countHyp with the one term at +1 and the unit at −1: the count is at
// most its bound, or some key below the bound has a body above 1, which no 0/1 body has) is proposed in the initial
// selection of a counted attempt, so a model that puts a count above its universe is never a model of the goal. Nothing
// is assumed: the instance is an ordinary count instance the kernel checks. A body that is not 0/1 gets no range.
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
