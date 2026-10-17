// Lists of names: for the suite (`bun examples/lists.ts`), core/lists.test.ts and lean-kernel/package-check.ts.
//
// A scope kept in normal form: a list of names, strictly increasing (so no name twice), under inserts and removals that
// keep its order. The caller names the position (the runtimes' binary search, say); the rule checks it: an insert only
// between the neighbours it falls between, a removal only of the name at that position. Positions shift on both (a
// write at every key reading the list at k ∸ 1 or k + 1). Proven: nothing past the end, strictly increasing (a law
// about every two positions), an insert puts its name in and keeps every name (each through a witness position), a
// removal takes its name out (at every position, from the increasing order). Skipping the check against the right
// neighbour breaks the order; shifting the wrong way breaks it too.
import {type Law} from '../core/machine.ts'
import {forall, nat, oneOf, rule, someKey, when} from '../core/dsl.ts'
import type {StepLaw} from '../kernel/kernel.ts'
import {proveStepLaws} from '../kernel/prove.ts'

export type ScopeBug = 'skips the right neighbour' | 'shifts the wrong way on removal'
export const scope = (bug?: ScopeBug) => rule('normalized scope')
  .inputs({op: oneOf('insert', 'remove'), name: nat, at: nat})
  .lists('Scope')
  .flags(({op, name, at, Scope}) => ({
    fits: op.is('insert').and(at.atMost(Scope.len), at.eq(0).or(Scope.at(at.minus(1)).lt(name)), bug === 'skips the right neighbour' ? at.atMost(Scope.len) : at.eq(Scope.len).or(name.lt(Scope.at(at)))),
    found: op.is('remove').and(at.lt(Scope.len), Scope.at(at).eq(name)),
  }))
  .step(({at, name, fits, found, Scope}) => ({
    ...Scope.apply(Scope.insertAt(at, name, fits), bug === 'shifts the wrong way on removal' ? {when: found, at: k => when(k.lt(at), Scope.at(k), Scope.at(k.minus(1))), len: Scope.len.minus(1)} : Scope.removeAt(at, found)),
  }))
const ok = scope()
export const scopeLaws = (r = ok): Law[] => [
  r.law('nothing past the end', ({Scope}) => Scope.within()),
  r.law('strictly increasing', ({Scope}) => Scope.increasing()),
]
export const scopeSteps = (r = ok): StepLaw[] => [
  r.stepLaw('an insert puts its name in', ({name}, after) => someKey(j => j.lt(after.Scope.len).and(after.Scope.at(j).eq(name))), ({fits}) => fits),
  r.stepLaw('an insert keeps every name', ({at, Scope}, after) => forall(k => k.lt(Scope.len).implies(someKey(j => j.lt(after.Scope.len).and(after.Scope.at(j).eq(Scope.at(k))), when(k.lt(at), k, k.plus(1))))), ({fits}) => fits),
  r.stepLaw('a removal takes its name out', ({name}, after) => forall(j => j.lt(after.Scope.len).implies(after.Scope.at(j).ne(name))), ({found}) => found),
  r.stepLaw('an insert adds one position', ({Scope}, after) => after.Scope.len.eq(Scope.len.plus(1)), ({fits}) => fits),
]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'skips the right neighbour', 'shifts the wrong way on removal'] as const) {
    const r = scope(bug), v = proveStepLaws(r.machine, scopeLaws(r), bug ? [] : scopeSteps(r))
    if (!bug && !(v.proven && v.checked)) console.log(JSON.stringify(v.failed))
    results.push([`normalized scope${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
