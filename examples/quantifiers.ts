// Quantifiers anywhere, and some key: for the suite (`bun examples/quantifiers.ts`), core/quantifiers.test.ts and
// lean-kernel/package-check.ts.
//   - the derived authority of examples/sets.ts with its quantifiers where they read naturally: inside the flags that
//     use them, in the assumption, and inside laws (each named as a flag, or pulled out as the law's key)
//   - a set that only grows, remembering the last name added: some name is in it once anything was added, and an add
//     puts some name in (each proven through a witness the prover finds: `last`, and the request's name)
import {type Law} from '../core/machine.ts'
import {everyKey, nat, oneOf, rule, someKey, when} from '../core/dsl.ts'
import type {StepLaw} from '../kernel/kernel.ts'
import {proveStepLaws} from '../kernel/prove.ts'

export const inlineAuthority = (bug?: 'checks only the named grant') => rule('derived authority, quantifiers inline')
  .inputs({op: oneOf('issue', 'derive', 'use', 'release'), name: nat})
  .state({issued: 0, live: 0})
  .maps({Grants: 0, Child: 0})
  .carries('Candidate')
  .flags(({op, name, issued, Candidate, Grants}) => ({
    accepted: op.is('derive').and(issued.eq(1), bug ? Candidate.has(name).implies(Grants.has(name)) : Candidate.subsetOf(Grants)),
    refused: op.is('derive').and(issued.eq(1).and(Candidate.subsetOf(Grants)).not()),
    issuing: op.is('issue').and(issued.eq(0)),
  }))
  .assume(({Candidate}) => everyKey(k => Candidate.at(k).atMost(1)))
  .step(({op, issued, live, issuing, accepted, refused, Candidate, Grants, Child}) => ({
    issued: when(issuing, 1, issued),
    live: when(accepted, 1, when(refused.or(op.is('release')), 0, live)),
    Grants: Grants.each(k => when(issuing, Candidate.at(k), Grants.at(k))),
    Child: Child.each(k => when(accepted, Candidate.at(k), when(refused.or(op.is('release')), 0, Child.at(k)))),
  }))
const inline = inlineAuthority()
export const inlineLaws = (a = inline): Law[] => [
  a.law('a live child is within the grants', ({live, Child, Grants}) => live.eq(1).implies(Child.subsetOf(Grants))),
  a.law('nothing is derived before the grants are issued', ({Child, issued}) => ({forall: k => Child.at(k).atMost(issued)})),
  a.law('the grants are a set, and the child is within them', ({Grants, Child}) => everyKey(k => Grants.at(k).atMost(1)).and(Child.subsetOf(Grants))),
  a.law('a live child was derived after the grants were issued', ({live, issued}) => live.atMost(issued)),
]
export const inlineSteps = (a = inline): StepLaw[] => [
  a.stepLaw('a refused derivation leaves no live child', (_, after) => after.live.eq(0), ({refused}) => refused),
  a.stepLaw('an accepted child is within the grants', ({Grants}, after) => after.Child.subsetOf(Grants), ({accepted}) => accepted),
]

export const members = (bug?: 'forgets the name') => rule('members').inputs({op: oneOf('add', 'look'), name: nat}).state({count: 0, last: 0}).maps({S: 0})
  .step(({op, name, count, last, S}) => ({
    S: S.set(name, when(op.is('add'), 1, S.at(name))),
    count: when(op.is('add'), count.plus(1), count),
    last: when(op.is('add'), bug ? last : name, last),
  }))
const grows = members()
export const memberLaws = (a = grows): Law[] => [a.law('something was added, so some name is in', ({count, S}) => count.atLeast(1).implies(someKey(k => S.at(k).eq(1))))]
export const memberSteps = (a = grows): StepLaw[] => [a.stepLaw('an add puts some name in', (_, after) => someKey(k => after.S.at(k).eq(1)), ({op}) => op.is('add'))]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'checks only the named grant'] as const) {
    const a = inlineAuthority(bug), v = proveStepLaws(a.machine, inlineLaws(a), bug ? [] : inlineSteps(a))
    results.push([`derived authority, quantifiers inline${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'forgets the name'] as const) {
    const a = members(bug), v = proveStepLaws(a.machine, memberLaws(a), bug ? [] : memberSteps(a))
    results.push([`members${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
