// proveRule and proveSteps search for what the laws need where the prover alone doesn't prove them and no run breaks
// them: lemmas (core/discover.ts), then invariants (core/infer.ts). `{search: false}` is the prover alone.
import {expect, test} from 'bun:test'
import {nat, oneOf, proveRule, proveSteps, rule, when} from './dsl.ts'
import {bucket, bucketLaw, pool, poolLaw} from '../examples/infer.ts'
import {retries, retryLaws, retrySteps} from '../examples/lemmas.ts'

test('an invariant nobody wrote is found and proven, and said as a law', () => {
  const r = bucket(), law = bucketLaw(r)
  expect(proveRule(r, [law], {search: false}).proven).toBe(false)
  const v = proveRule(r, [law])
  expect(v).toMatchObject({proven: true, checked: true})
  expect(v.found?.laws?.length).toBeGreaterThan(0)
  // The proof rests on the invariants found, each proven from init: the verdict says so.
  expect(v.assumes).toEqual({states: 'reachable', laws: v.found!.laws!.map(f => f.text)})
  // What was found, given back with the law, is a proof by the prover alone.
  expect(proveRule(r, [law, ...v.found!.laws!.map(f => f.law)], {search: false})).toMatchObject({proven: true, checked: true})
})

test('lemmas nobody stated are found and proven, as source to paste', () => {
  const r = retries('states no lemma'), v = proveSteps(r, retryLaws(r), retrySteps(r))
  expect(v).toMatchObject({proven: true, checked: true})
  expect(v.found?.lemmas?.delay?.lemmas?.length).toBeGreaterThan(0)
})

test('no search where the prover alone proves the laws or a run breaks them', () => {
  const ok = pool(), proven = proveRule(ok, [poolLaw(ok), ok.law('in use + released <= acquired', ({inUse, released, acquired}) => inUse.plus(released).atMost(acquired))])
  expect(proven.found).toBeUndefined()
  const bad = pool('release unchecked'), t = performance.now(), refuted = proveRule(bad, [poolLaw(bad)])
  expect(refuted.proven).toBe(false)
  expect(refuted.run).toBeDefined()
  expect(refuted.found).toBeUndefined()
  expect(performance.now() - t).toBeLessThan(5000)
})

test('a search that finds nothing says so, within its time', () => {
  // False, but past where a few random runs go: nothing proves it.
  const r = rule('counter').inputs({}).state({n: 0}).step(({n}) => ({n: n.plus(1)})), law = r.law('n stays within a million', ({n}) => n.atMost(1_000_000))
  const t = performance.now(), v = proveRule(r, [law], {search: {ms: 2000}})
  expect(v.proven).toBe(false)
  expect(performance.now() - t).toBeLessThan(8000)
})

test('a law broken only past where random runs go is refuted by a bounded run, which the interpreter takes', () => {
  // A lock of five codes: each step's code must be the next one (37, 512, 9, 1000, 77). No random run guesses them; the
  // model of the kernel's 5-step goal from the start (core/bmc.ts) names them.
  const codes = [37, 512, 9, 1000, 77]
  const r = rule('lock').inputs({code: nat}).state({stage: 0})
    .step(({stage, code}) => ({stage: codes.reduceRight((rest, c, i) => when(stage.eq(i).and(code.eq(c)), stage.plus(1), rest), stage)}))
  const law = r.law('the lock stays shut', ({stage}) => stage.atMost(4))
  const v = proveRule(r, [law], {search: {ms: 4000}})
  expect(v.proven).toBe(false)
  expect(v.goal).toContain('a run of 5 steps')
  expect(v.run?.trace.map(t => t.code)).toEqual(codes)
})

test('a deterministic loop broken only after thousands of steps is refuted by its forced run', () => {
  // No request: every run is the one run, 10,000 steps to the break, past any k-step goal (the kernel's k is at most 64).
  const r = rule('ticker').inputs({}).state({n: 0, m: 0}).step(({n, m}) => ({n: n.plus(1), m: when(n.atLeast(5000), m.plus(1), m)}))
  const law = r.law('m stays below 5,000', ({m}) => m.atMost(4999))
  const v = proveRule(r, [law], {search: {ms: 4000}})
  expect(v.proven).toBe(false)
  expect(v.run?.trace.length).toBe(10_000)
})

// A step law false from a state no run reaches: the search proves it with an invariant that holds only in reachable
// states. Up to 0.30.0 the verdict was a plain proven, and a caller that steps the rule from states it is handed (a
// host's) read it as a proof for those too: 3 of one such caller's 50 broken variants came back proven so.
const ticket = (bug?: 'payload is swapped') => rule('ticket').inputs({op: oneOf('take', 'revoke')})
  .state({active: 1, expected: 0, payload: 0, value: 0})
  .flags(({op, active}) => ({takes: op.is('take').and(active.eq(1))}))
  .step(({payload, expected, takes}) => ({active: 0, value: when(takes, bug ? expected : payload, 0)}))
const binding = (bug?: 'failed admits work') => rule('binding').inputs({op: oneOf('fail', 'work')})
  .state({phase: oneOf('Active', 'Failed').from('Active'), revoked: 0, admitted: 0})
  .flags(({op, phase, revoked}) => ({admits: op.is('work').and(bug ? phase.is('Active').or(revoked.eq(0)) : phase.is('Active'))}))
  .step(({op, phase, revoked, admits}) => ({phase: when(op.is('fail'), 'Failed', phase), revoked: when(op.is('fail'), revoked.plus(1), revoked), admitted: when(admits, 1, 0)}))
type AnyRule = Parameters<typeof proveSteps>[0]
type AnyStepLaw = Parameters<typeof proveSteps>[2][number]
const reachableOnly = (b: AnyRule, sl: AnyStepLaw, ok: AnyRule, okLaw: AnyStepLaw) => {
  const v = proveSteps(b, [], [sl])
  // proven, never plainly: it rests on the invariants found
  expect(v).toMatchObject({proven: true, checked: true, assumes: {states: 'reachable'}})
  expect(v.assumes!.laws.length).toBeGreaterThan(0)
  expect(v.assumes!.laws).toEqual(v.found!.laws!.map(f => f.text))
  // from any state the laws allow: refuted, with the state
  for (const opts of [{from: 'any' as const}, {search: false}]) {
    const a = proveSteps(b, [], [sl], opts)
    expect(a).toMatchObject({proven: false, stuck: 'sat'})
    expect(a.witness).toBeDefined()
  }
  // the rule as it ships: proven from any state, with nothing assumed
  const okv = proveSteps(ok, [], [okLaw], {from: 'any'})
  expect(okv).toMatchObject({proven: true, checked: true})
  expect(okv.assumes).toBeUndefined()
}
test('a step law proven only in reachable states says so; {from: \'any\'} refutes it with the state', () => {
  const handsOver = (r: ReturnType<typeof ticket>) => r.stepLaw('a take hands over the payload', ({payload}, a) => a.value.eq(payload), ({takes}) => takes)
  const tb = ticket('payload is swapped'), t = ticket()
  reachableOnly(tb, handsOver(tb), t, handsOver(t))
  const nothing = (r: ReturnType<typeof binding>) => r.stepLaw('a failed binding admits nothing', (_b, a) => a.admitted.eq(0), ({phase}) => phase.is('Failed'))
  const bb = binding('failed admits work'), b = binding()
  reachableOnly(bb, nothing(bb), b, nothing(b))
})
