// Cycles found (core/cycles.ts): what the search builds the kernel checks again on its own; a tampered proof found is
// refused; the broken variants are refused; the ranks are the small ones the runs give.
import {expect, test} from 'bun:test'
import {refuseCyclic} from '../kernel/cyclic.ts'
import {findCycles, findRank, linE, showE} from './cycles.ts'
import {proveLeadsTo, proveLoop, proveRule} from './dsl.ts'
import {accumulator, ackermann, claimCases, countUp, euclid, exchange, exchangeLoop, liveCases, loopCases, mccarthy, phases, ruleCases, toProduct, triangle} from '../examples/cycles.ts'

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

test('past linear ranks with coefficients up to 4: the exact LP, products of two variables, ranks in order', () => {
  expect(findCycles(exchange().facts, exchange().claims).found?.ranks['ex(x, y) <= 5']).toBe('(11·x + 2·y)')
  expect(findCycles(countUp().facts, countUp().claims).found?.ranks['up(i, n) >= n·n']).toBe('(n·n − i)')
  expect(findRank(exchangeLoop().loop)).toMatchObject({proven: true, checked: true, found: {rank: '(11·x + 2·y)'}})
  expect(findRank(toProduct().loop)).toMatchObject({proven: true, checked: true, found: {rank: '(M·N − (i + 1))'}})
  // A rank the runs' size bounds (32·x + y where x reaches 33) is refused: the triangle's is (x, y).
  expect(findRank(triangle().loop).found?.rank).toBe('(x, y)')
}, 60_000)

test('liveness with no rank: the rank found, the broken ones refused', () => {
  for (const [c, want] of liveCases()) expect([c.name, proveLeadsTo(c.r, c.laws, c.live).proven]).toEqual([c.name, want])
  expect(proveLeadsTo(liveCases()[2]![0].r, [], liveCases()[2]![0].live).found?.rank).toBe('(2·inbox + outbox)')
}, 60_000)
