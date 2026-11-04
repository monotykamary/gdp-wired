import {expect, test} from 'bun:test'
import {get, n, x, same, not} from '../../core/machine.ts'
import {tuple} from '../../kernel/kernel.ts'
import {refuseCyclic} from '../../kernel/cyclic.ts'
import {EGraph, Exhausted, Meter} from './match.ts'
import {voteExperiment} from './vote.ts'

const f = (name: string, ...args: ReturnType<typeof x>[]) => get(name, tuple(args))
const graph = () => new EGraph(new Meter(1_000_000))
test('vote clause: instance is necessary, kernel checked, and not a substitute for the vote premise', () => {
  const baseline = voteExperiment(false), enabled = voteExperiment(true), missing = voteExperiment(true, true)
  expect(baseline.checked).toBe(false)
  expect(enabled.checked).toBe(true)
  expect(enabled.instances).toBe(1)
  expect(missing.checked).toBe(false)
  const p = structuredClone(enabled.proof!)
  p.nodes[0]!.insts = []
  expect(refuseCyclic(p)).toBeDefined()
  const wrong = structuredClone(enabled.proof!)
  wrong.nodes[0]!.insts[0]!.at[1] = x('unrelatedBallot')
  expect(refuseCyclic(wrong)).toBeDefined()
})
test('matching modulo congruence binds a repeated variable consistently', () => {
  const g = graph()
  g.seed([same(x('a'), x('b')), same(f('R', f('F', x('a')), f('F', x('b'))), n(1))])
  expect(g.match([f('R', x('z'), x('z'))], ['z'])).toHaveLength(1)
})
test('without equality, repeated variables cannot match different classes', () => {
  const g = graph(); g.seed([same(f('R', x('a'), x('b')), n(1))])
  expect(g.match([f('R', x('z'), x('z'))], ['z'])).toHaveLength(0)
})
test('multi-pattern joins correlate tuples rather than taking a Cartesian product', () => {
  const g = graph()
  g.seed([same(f('R', x('a'), x('b')), n(1)), same(f('S', x('a'), x('c')), n(1)), same(f('S', x('d'), x('b')), n(1))])
  expect(g.match([f('R', x('u'), x('v')), f('S', x('u'), x('v'))], ['u', 'v'])).toHaveLength(0)
  g.seed([same(f('S', x('a'), x('b')), n(1))])
  expect(g.match([f('R', x('u'), x('v')), f('S', x('u'), x('v'))], ['u', 'v'])).toHaveLength(1)
})
test('negated and disjunctive equalities are never merged', () => {
  for (const equality of [not(same(x('a'), x('b'))), {op: 'or' as const, xs: [same(x('a'), x('b')), same(x('a'), x('c'))]}]) {
    const g = graph(); g.seed([equality, same(f('R', x('a'), x('b')), n(1))])
    expect(g.match([f('R', x('z'), x('z'))], ['z'])).toHaveLength(0)
  }
})
test('unbound keys, zero result cap, and differing symbols cannot invent instances', () => {
  const g = graph(); g.add(f('F', x('a')))
  expect(g.match([f('F', x('u'))], ['u', 'v'])).toEqual([])
  expect(g.match([f('F', x('u'))], ['u'], 0)).toEqual([])
  expect(g.match([f('G', x('u'))], ['u'])).toEqual([])
})
test('work, node, and expired-wall limits stop search without a success verdict', () => {
  const m = new Meter(2), g = new EGraph(m)
  expect(() => g.add(f('F', x('a')))).toThrow(Exhausted)
  expect(m.used).toBe(2)
  expect(() => new EGraph(new Meter(100), 0).add(x('a'))).toThrow(Exhausted)
  expect(() => new EGraph(new Meter(100, performance.now() - 1)).add(x('a'))).toThrow(Exhausted)
  expect(() => new Meter(-1)).toThrow()
})
test('cyclic classes terminate within fuel; deterministic result cap is enforced', () => {
  const g = graph(); g.seed([same(x('a'), f('F', x('a')))])
  expect(g.match([f('F', f('F', x('u')))], ['u'], 1)).toHaveLength(1)
  const h = graph(); h.add(f('F', x('a'))); h.add(f('F', x('b')))
  expect(h.match([f('F', x('u'))], ['u'], 1)).toHaveLength(1)
})
