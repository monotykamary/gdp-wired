// Quantifiers anywhere, and some key: for the suite (`bun examples/quantifiers.ts`), core/quantifiers.test.ts and
// lean-kernel/package-check.ts.
//   - the derived authority of examples/sets.ts with its quantifiers where they read naturally: inside the flags that
//     use them, in the assumption, and inside laws (each named as a flag, or pulled out as the law's key)
//   - a set that only grows, remembering the last name added: some name is in it once anything was added, and an add
//     puts some name in (each proven through a witness the prover finds: `last`, and the request's name)
//   - a scope of names normalized, then rechecked against itself: the recheck keeps it, as the first step's check
//     holds at the key where the second's would fail (a flag read at a later step's witness); the broken variant
//     rechecks without the lengths
//   - a child derived from a parent's grants, then used: a use the child is granted names a grant of the parent, as the
//     derivation's cover holds at the use's name (a flag read at a later step's input); the broken variant derives
//     without the cover
import {type Law} from '../core/machine.ts'
import {all, bool, everyKey, nat, oneOf, rule, someKey, when} from '../core/dsl.ts'
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

const EMPTY = 0, WILDCARD = 1, NAMES = 66, LENGTH = 256
export const normalForm = () => rule('normal form')
  .inputs({op: oneOf('source', 'normalize'), first: nat}).state({exact: 0}).maps({Names: 0}).carries('Given', 'Len')
  .flags(({Given, Len, Names}) => ({
    bits: everyKey(k => Given.at(k).atMost(1)),
    identities: everyKey(k => Given.has(k).implies(k.ne(EMPTY).and(k.ne(WILDCARD)))),
    fits: everyKey(k => Given.has(k).iff(Names.has(k)).and(Given.has(k).implies(all(k.ne(EMPTY), k.ne(WILDCARD), k.lt(NAMES), Len.at(k).atMost(LENGTH))))),
  }))
  .flags(({Given, Len, Names}) => ({
    unchanged: everyKey(k => Given.at(k).eq(Names.at(k))),
    short: everyKey(k => Given.has(k).implies(Len.at(k).atMost(LENGTH))),
  }))
  .flags(({op, exact, first, Given, identities, fits}) => ({accepted: Given.has(first).and(op.match({source: () => identities, normalize: () => exact.eq(1).and(fits)}))}))
  .assume(({bits}) => bits)
  .step(({accepted, Given, Names}) => ({exact: when(accepted, 1, 0), Names: Names.each(k => when(accepted, Given.at(k), 0))}))
export const normalFormLaws = (r = normalForm()): Law[] => [r.law('the names are a set', ({Names}) => everyKey(k => Names.at(k).atMost(1)))]
export const normalFormSteps = (bug?: 'rechecks without the lengths', r = normalForm()): StepLaw[] => [
  r.stepsLaw('rechecking a normal form against itself keeps it', 2, ({Given}, last) => last.exact.eq(1).and(everyKey(k => last.Names.at(k).eq(Given.at(k)))),
    ({op, accepted, first, Given, unchanged, short}, j) => (j === 0 ? op.is('normalize').and(accepted) : op.is('normalize').and(unchanged, ...(bug ? [] : [short]), Given.has(first)))),
]

export const childUse = (bug?: 'derives without the cover') => rule('derived child')
  .inputs({op: oneOf('issue', 'derive', 'use', 'release'), name: nat, parentLive: bool}).state({live: 0, granted: 0}).maps({Grants: 0}).carries('Candidate', 'Parent')
  .flags(({Candidate, Parent}) => ({
    bits: everyKey(k => Candidate.at(k).atMost(1).and(Parent.at(k).atMost(1))),
    covered: everyKey(k => Candidate.has(k).implies(Parent.has(k))),
  }))
  .flags(({op, parentLive, covered, live, name, Grants}) => ({
    issued: op.is('issue'),
    derived: op.is('derive').and(bug ? parentLive : parentLive.and(covered)),
    allowed: op.is('use').and(live.eq(1).and(Grants.has(name))),
  }))
  .assume(({bits}) => bits)
  .step(({op, live, issued, derived, allowed, Candidate, Grants}) => ({
    live: when(issued.or(derived), 1, when(op.is('use'), live, 0)),
    granted: when(allowed, 1, 0),
    Grants: Grants.each(k => when(issued.or(derived), Candidate.at(k), when(op.is('use'), Grants.at(k), 0))),
  }))
export const childUseLaws = (r = childUse()): Law[] => [r.law('the grants are a set', ({Grants}) => everyKey(k => Grants.at(k).atMost(1)))]
export const childUseSteps = (r = childUse()): StepLaw[] => [
  r.stepsLaw('a derived child\'s granted use names a grant of its parent', 2, ({Parent}, last, [, use]) => last.granted.eq(1).implies(Parent.has(use!.name)),
    ({op}, j) => (j === 0 ? op.is('derive') : op.is('use'))),
]

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
  for (const bug of [undefined, 'rechecks without the lengths'] as const) {
    const a = normalForm(), v = proveStepLaws(a.machine, normalFormLaws(a), normalFormSteps(bug, a))
    results.push([`normal form${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'derives without the cover'] as const) {
    const a = childUse(bug), v = proveStepLaws(a.machine, childUseLaws(a), childUseSteps(a))
    results.push([`derived child${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
