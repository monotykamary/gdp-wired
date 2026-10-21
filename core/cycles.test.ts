// Cycles found (core/cycles.ts): what the search builds the kernel checks again on its own; a tampered proof found is
// refused; the broken variants are refused; the ranks are the small ones the runs give.
import {expect, test} from 'bun:test'
import {refuseCyclic} from '../kernel/cyclic.ts'
import {findCycles, findRank, linE, showE} from './cycles.ts'
import {proveLoop, proveRule} from './dsl.ts'
import {accumulator, ackermann, claimCases, euclid, loopCases, mccarthy, phases, ruleCases} from '../examples/cycles.ts'

test('claims over functions: each proven and checked by the kernel again, each broken variant refused', () => {
  for (const [c, want] of claimCases()) {
    const out = findCycles(c.facts, c.claims)
    expect([c.name, out.proven && out.checked]).toEqual([c.name, want])
    if (want) expect(refuseCyclic(out.proof!)).toBeUndefined()
    // The claims are nodes of the proof as given.
    if (want) for (const cl of c.claims) expect(out.proof!.nodes.find(n => n.name === cl.name)).toMatchObject({hyps: cl.hyps ?? [], concl: cl.concl})
  }
}, 60_000)

test('ranks from the runs: 101 − n, (m, n) in order, a companion below its claim', () => {
  const mc = findCycles(mccarthy().facts, mccarthy().claims)
  expect(mc.found?.ranks['f(n) = 91 for n <= 101']).toBe('(101 − n)')
  expect(findCycles(ackermann().facts, ackermann().claims).found?.ranks['ack(m, n) > n']).toBe('(m, n)')
  const acc = findCycles(accumulator().facts, accumulator().claims)
  expect(acc.found?.companions).toEqual(['g(x, g1$0) = g1$0 + 2·x'])
  expect(showE(linE({n: -1}, 101))).toBe('101 − n')
})

test('a proof found, tampered, is refused', () => {
  const p = findCycles(mccarthy().facts, mccarthy().claims).proof!
  expect(refuseCyclic({...p, nodes: p.nodes.map(n => ({...n, rank: n.rank.map(() => ({op: 'var', name: 'n'}))}))})).toBeDefined()
  expect(refuseCyclic({...p, nodes: p.nodes.map(n => ({...n, uses: n.uses.map(u => ({...u, guard: {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}}))}))})).toBeDefined()
})

test('loops with no rank: the rank and the invariants found, the broken ones refused', () => {
  expect(findRank(phases().loop).found?.rank).toBe('(x, y)')
  expect(findRank(euclid().loop)).toMatchObject({proven: true, checked: true, found: {rank: '(a + b)'}})
  for (const [l, want] of loopCases()) expect([l.loop.name, proveLoop(l, []).proven]).toEqual([l.loop.name, want])
}, 60_000)

test('rules reading functions known by their facts: the lemma found in the search, not without it', () => {
  for (const [{r, laws}, want] of ruleCases()) {
    expect([r.machine.name, proveRule(r, laws).proven]).toEqual([r.machine.name, want])
    expect(proveRule(r, laws, {search: {cycles: false}}).proven).toBe(false)
  }
}, 60_000)
