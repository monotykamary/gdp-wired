// Sets of names: maps with cells 0 or 1, a request carrying a whole set, conditions about every key as flags, and writes
// at every key. For the suite (`bun examples/sets.ts`) and kernel/sets.test.ts.
//
// An authority derives a child from its grants: a request carries a candidate set of names; the child is accepted only
// if every candidate name is granted (the candidate is covered), and then holds exactly the candidate; otherwise it is
// released, empty. A use of a name succeeds only while the child is live and holds the name.
import {type Law} from '../core/machine.ts'
import {everyKey, nat, oneOf, rule, when, yes} from '../core/dsl.ts'
import type {StepLaw} from '../kernel/kernel.ts'
import {proveStepLaws} from '../kernel/prove.ts'

export type AuthorityBug = 'checks only the named grant' | 'keeps the child on refusal'
export const authority = (bug?: AuthorityBug) => rule('derived authority')
  .inputs({op: oneOf('issue', 'derive', 'use', 'release'), name: nat})
  .state({issued: 0, live: 0})
  .maps({Grants: 0, Child: 0})
  .carries('Candidate')
  .flags(({op, name, issued, Candidate, Grants}) => ({
    // Every cell of a set the request carries is 0 or 1.
    bits: everyKey(k => Candidate.at(k).atMost(1)),
    covered: bug === 'checks only the named grant' ? Candidate.has(name).implies(Grants.has(name)) : Candidate.subsetOf(Grants),
    issuing: op.is('issue').and(issued.eq(0)),
  }))
  .flags(({op, issued, covered}) => ({accepted: op.is('derive').and(issued.eq(1), covered), refused: op.is('derive').and(issued.eq(1).and(covered).not())}))
  .flags(({op, name, live, Child}) => ({granted: op.is('use').and(live.eq(1), Child.has(name))}))
  .assume(({bits}) => bits)
  .step(({op, issued, live, issuing, accepted, refused, Candidate, Grants, Child}) => ({
    issued: when(issuing, 1, issued),
    live: when(accepted, 1, when(refused.or(op.is('release')), bug === 'keeps the child on refusal' ? when(op.is('release'), 0, live) : 0, live)),
    Grants: Grants.each(k => when(issuing, Candidate.at(k), Grants.at(k))),
    Child: Child.each(k => when(accepted, Candidate.at(k), when(bug === 'keeps the child on refusal' ? op.is('release') : refused.or(op.is('release')), 0, Child.at(k)))),
  }))

const ok = authority()
export const authorityLaws = (a = ok): Law[] => [
  a.law('the child is within the grants', ({Child, Grants}) => ({forall: k => Child.at(k).atMost(Grants.at(k))})),
  a.law('a live child was derived after the grants were issued', ({live, issued}) => live.atMost(issued)),
  a.law('nothing is derived before the grants are issued', ({Child, issued}) => ({forall: k => Child.at(k).atMost(issued)})),
  a.law('the grants are a set', ({Grants}) => ({forall: k => Grants.at(k).atMost(1)})),
]
export const authoritySteps = (a = ok): StepLaw[] => [
  a.stepLaw('an accepted child holds exactly the candidate', ({Candidate}, after) => ({forall: k => after.Child.at(k).eq(Candidate.at(k))}), ({accepted}) => accepted),
  a.stepLaw('a refused derivation leaves no live child', (_, after) => after.live.eq(0), ({refused}) => refused),
  a.stepLaw('a granted use names a granted name', ({name, Grants}) => Grants.has(name), ({granted}) => granted),
  a.stepLaw('the grants never change once issued', ({issued, Grants}, after) => ({forall: k => issued.eq(1).implies(after.Grants.at(k).eq(Grants.at(k)))})),
]
// Two steps in a row: the second request is read by its own names (its inputs, its flags' values and witnesses, its set).
export const authorityPairs = (a = ok): StepLaw[] => [
  a.stepsLaw('a refused derivation after an accepted one leaves no live child', 2, (_, after) => after.live.eq(0), ({accepted, refused}, j) => (j === 0 ? accepted : refused)),
  a.stepsLaw('two accepted derivations leave the child within the grants', 2, ({Grants}, after) => ({forall: k => after.Child.at(k).atMost(Grants.at(k))}), ({accepted}) => accepted),
]
void yes

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'checks only the named grant', 'keeps the child on refusal'] as const) {
    const a = authority(bug), v = proveStepLaws(a.machine, authorityLaws(a), [...authoritySteps(a), ...authorityPairs(a)])
    results.push([`derived authority${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
    if (!bug && !(v.proven && v.checked)) console.log(JSON.stringify(v.failed))
  }
  for (const [what, got, want] of results) console.log(`${what.padEnd(48)} ${got ? 'proven, kernel accepts' : 'not proven'}${got === want ? '' : '   UNEXPECTED'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
