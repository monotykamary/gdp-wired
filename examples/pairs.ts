// Conditions at every two keys (core/dsl.ts everyKey((i, j) => ...)): a flag over pairs, each key read on its own and
// compared with the other plainly, decided by the runtimes on every pair of a few keys per breakpoint and closed by the
// kernel at the pairs a proof names. For the suite (`bun examples/pairs.ts`), core/pairs.test.ts and
// lean-kernel/package-check.ts.
//   - a sorted list replaced whole: a request carries a list of n values, taken only when it increases (every two
//     places in order hold values in order), so the list kept increases; the broken variant checks every place but the
//     last
//   - a list of distinct names, replaced whole: taken only when no two places hold one name, so no two places kept do
import {type Law} from '../core/machine.ts'
import {everyKey, forall, nat, proveSteps, rule, when} from '../core/dsl.ts'

export const sortedList = (bug?: 'checks every place but the last') => rule('sorted list').inputs({n: nat}).state({len: 0}).maps({At: 0}).carries('New')
  .flags(({n, New}) => ({increasing: everyKey((i, j) => i.lt(j).and(j.lt(bug ? n.minus(1) : n)).implies(New.at(i).lt(New.at(j))))}))
  .step(({n, len, increasing, New, At}) => ({len: when(increasing, n, len), At: At.each(k => when(increasing, when(k.lt(n), New.at(k), 0), At.at(k)))}))
export const sortedListLaws = (r = sortedList()): Law[] => [
  r.law('the list increases', ({len, At}) => forall((i, j) => i.lt(j).and(j.lt(len)).implies(At.at(i).lt(At.at(j))))),
  r.law('nothing past its end', ({len, At}) => forall(k => len.atMost(k).implies(At.at(k).eq(0)))),
]

export const distinctNames = (bug?: 'compares each place with the first only') => rule('distinct names').inputs({n: nat}).state({len: 0}).maps({Names: 0}).carries('New')
  .flags(({n, New}) => ({distinct: bug
    ? everyKey(k => k.atLeast(1).and(k.lt(n)).implies(New.at(k).eq(New.at(0)).not()))
    : everyKey((i, j) => i.lt(j).and(j.lt(n)).implies(New.at(i).eq(New.at(j)).not()))}))
  .step(({n, len, distinct, New, Names}) => ({len: when(distinct, n, len), Names: Names.each(k => when(distinct, when(k.lt(n), New.at(k), 0), Names.at(k)))}))
export const distinctNamesLaws = (r = distinctNames()): Law[] => [
  r.law('no two places hold one name', ({len, Names}) => forall((i, j) => i.lt(j).and(j.lt(len)).implies(Names.at(i).eq(Names.at(j)).not()))),
]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'checks every place but the last'] as const) {
    const r = sortedList(bug), v = proveSteps(r, sortedListLaws(r), [])
    results.push([`sorted list${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'compares each place with the first only'] as const) {
    const r = distinctNames(bug), v = proveSteps(r, distinctNamesLaws(r), [])
    results.push([`distinct names${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
