// Folds over trees as values (core/dsl.ts fold): each leaf's values from its inputs, each node's from its inputs and its
// two children's; a law holds of every tree by induction over it. For the suite (`bun examples/folds.ts`),
// core/folds.test.ts and lean-kernel/package-check.ts.
//   - a spend roll-up over an org chart: each team's spend capped per team, the roll-up at most the cap times the teams
//     (a product of the cap, a param, and the count); the broken variant caps the leaves only
//   - sign-offs over a document's sections: a document is approved when every section is; then its approved count is
//     its section count; the broken variant approves when the children are, whatever the node's own sign-off
import {type Law} from '../core/machine.ts'
import {bool, count, fold, max, min, nat, proveFold, when} from '../core/dsl.ts'

export const rollup = (bug?: 'caps the leaves only') => fold('spend roll-up').params({cap: nat}).inputs({spend: nat})
  .leaf(({spend, cap}) => ({total: min(spend, cap), teams: 1, depth: 0}))
  .node(({spend, cap}, l, r) => ({total: l.total.plus(r.total).plus(bug ? spend : min(spend, cap)), teams: l.teams.plus(r.teams).plus(1), depth: max(l.depth, r.depth).plus(1)}))
export const rollupLaws = (f = rollup()): Law[] => [
  f.law('the roll-up is at most the cap per team', ({total, teams, cap}) => total.atMost(teams.mul(cap))),
  f.law('a chart is at least as wide as it is deep', ({depth, teams}) => depth.lt(teams)),
]

export const signoffs = (bug?: 'ignores the node\'s own sign-off') => fold('sign-offs').inputs({signed: bool})
  .leaf(({signed}) => ({approved: count(signed), sections: 1, signedCount: count(signed)}))
  .node(({signed}, l, r) => ({
    approved: when(l.approved.eq(1).and(r.approved.eq(1), bug ? signed.or(signed.not()) : signed), 1, 0),
    sections: l.sections.plus(r.sections).plus(1),
    signedCount: l.signedCount.plus(r.signedCount).plus(count(signed)),
  }))
export const signoffLaws = (f = signoffs()): Law[] => [
  f.law('approved is a yes or no', ({approved}) => approved.atMost(1)),
  f.law('an approved document has every section signed', ({approved, sections, signedCount}) => approved.eq(1).implies(signedCount.eq(sections))),
]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'caps the leaves only'] as const) {
    const f = rollup(bug), v = proveFold(f, rollupLaws(f))
    results.push([`spend roll-up${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'ignores the node\'s own sign-off'] as const) {
    const f = signoffs(bug), v = proveFold(f, signoffLaws(f))
    results.push([`sign-offs${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
