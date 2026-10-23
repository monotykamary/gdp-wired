// Invariants nobody wrote (core/infer.ts): a law that holds but isn't inductive alone is proven with the laws the search
// finds, checked by the kernel as laws of the same rule; what it found reads as a builder call that states the same law;
// a false law is answered with the run that breaks it; a law already proven needs nothing found.
import {expect, test} from 'bun:test'
import {forall, proveRule} from './dsl.ts'
import {inferLaws} from './infer.ts'
import {inflight, inflightLoss} from './models.ts'
import {proveLaws} from '../kernel/prove.ts'
import {accounts, accountsLaw, bucket, bucketLaw, lease, leaseLaw, pool, poolLaw} from '../examples/infer.ts'

test('a law that needs an invariant: not proven alone, proven with what the search finds, and the set checks', () => {
  for (const [r, law] of [[pool(), poolLaw()], [bucket(), bucketLaw()], [lease(), leaseLaw()]] as const) {
    expect(proveRule(r as never, [law], {search: false}).proven).toBe(false)
    const v = inferLaws(r as never, [law], [], {ms: 15000})
    expect(v).toMatchObject({proven: true, checked: true})
    expect(v.found.length).toBeGreaterThan(0)
    // Ended by its counted budgets, never by its wall-clock stop: what it found is the same on any machine.
    expect(v.stats.stopped).toBe(false)
    // The rule's own prover, on the law and what was found: the same verdict.
    expect(proveRule(r as never, [law, ...v.found.map(f => f.law)])).toMatchObject({proven: true, checked: true})
  }
})

test('what was found reads as the builder call that states it, and that call, written out, proves the law again', () => {
  const r = pool(), v = inferLaws(r, [poolLaw(r)], [], {ms: 15000})
  expect(v.found.map(f => f.source)).toEqual(["r.law('inUse + released <= acquired', ({inUse, acquired, released}) => inUse.plus(released).atMost(acquired))"])
  const pasted = r.law('inUse + released <= acquired', ({inUse, acquired, released}) => inUse.plus(released).atMost(acquired))
  expect(proveRule(r, [poolLaw(r), pasted])).toMatchObject({proven: true, checked: true})
  const l = lease(), w = inferLaws(l, [leaseLaw(l)], [], {ms: 15000})
  expect(w.found.map(f => f.source)).toEqual(["r.law('every k: Expiry[k] <= until', ({until, Expiry}) => forall(k => Expiry.at(k).atMost(until)))"])
  const leased = l.law('every k: Expiry[k] <= until', ({until, Expiry}) => forall(k => Expiry.at(k).atMost(until)))
  expect(proveRule(l, [leaseLaw(l), leased])).toMatchObject({proven: true, checked: true})
})

test('an invariant over four values (the join: the samples\' hull, made inductive): one account within the total paid in', () => {
  const r = accounts(), law = accountsLaw(r)
  expect(proveRule(r, [law], {search: false}).proven).toBe(false)
  const v = inferLaws(r, [law], [], {ms: 15000})
  expect(v).toMatchObject({proven: true, checked: true, stats: {stopped: false}})
  expect(v.found.map(f => f.source)).toEqual(["r.law('a + b + c <= total', ({a, b, c, total}) => a.plus(b).plus(c).atMost(total))"])
  expect(proveRule(r, [law, ...v.found.map(f => f.law)])).toMatchObject({proven: true, checked: true})
})

test('a machine with no rule: the in-flight bound needs s + 50·p <= b + 150 or tighter', () => {
  expect(proveLaws(inflight, [inflightLoss]).proven).toBe(false)
  const v = inferLaws(inflight, [inflightLoss], [], {ms: 15000})
  expect(v).toMatchObject({proven: true, checked: true, stats: {stopped: false}})
  expect(proveLaws(inflight, [inflightLoss, ...v.found.map(f => f.law)])).toMatchObject({proven: true, checked: true})
})

test('a false law is answered with the run that breaks it; a law proven alone needs nothing found', () => {
  const bad = pool('release unchecked'), v = inferLaws(bad, [poolLaw(bad)])
  expect(v.proven).toBe(false)
  expect(v.run).toBeDefined()
  expect(v.found).toEqual([])
  const r = pool(), alone = r.law('in use <= size', ({inUse, size}) => inUse.atMost(size)), w = inferLaws(r, [alone])
  expect(w).toMatchObject({proven: true, checked: true, found: []})
})
