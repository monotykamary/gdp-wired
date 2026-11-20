import {expect, test} from 'bun:test'
import {quietly} from '../core/cyclic.ts'
import type {C, E, Law, Machine} from '../core/machine.ts'
import {check, checkLaws, obligations, substC, substE} from './kernel.ts'
import {proveLaws} from './prove.ts'
import {hasWordDivision, wordDivisionFacts, wordDivisionKey, wordDivisionName} from './word-division.ts'

const k = (value: number): E => ({op: 'const', value})
const v = (name: string): E => ({op: 'var', name})

// Build a DAG of depth `depth` whose unfolded tree has 2^(depth+1) - 1 nodes
// but only depth + 1 distinct objects, while remaining semantically equal to `leaf`.
function sharedMaxDag(leaf: E, depth: number): E {
  let e = leaf
  for (let i = 0; i < depth; i++) e = {op: 'max', a: e, b: e}
  return e
}

function countDistinct(root: unknown): number {
  const seen = new Set<object>()
  const stack: unknown[] = [root]
  while (stack.length) {
    const x = stack.pop()
    if (!x || typeof x !== 'object' || seen.has(x)) continue
    seen.add(x)
    if (Array.isArray(x)) for (let i = x.length - 1; i >= 0; i--) stack.push(x[i])
    else for (const child of Object.values(x)) if (child && typeof child === 'object') stack.push(child)
  }
  return seen.size
}

function countTreeNodesCapped(root: unknown, cap: number): number {
  const memo = new WeakMap<object, number>()
  const go = (x: unknown): number => {
    if (!x || typeof x !== 'object') return 0
    const hit = memo.get(x)
    if (hit !== undefined) return hit
    memo.set(x, cap + 1)
    let n = 1
    for (const child of Array.isArray(x) ? x : Object.values(x)) {
      n += go(child)
      if (n > cap) return cap + 1
    }
    memo.set(x, n)
    return n
  }
  return go(root)
}

// Build a flag-chain machine whose raw AST has < 200 nodes, while flag inlining
// + each-write substitution produces > 2^25 (~33M+) unfolded tree nodes from
// < 400 distinct objects. Mirrors CCF's crash path in obligations -> goal -> wordDivisionFacts.
function flagFanoutMachine(depth: number, value: E): Machine {
  const flags: Record<string, C> = {f0: {op: '<=', a: v('x'), b: v('x')}}
  for (let i = 1; i <= depth; i++) {
    flags[`f${i}`] = {op: 'and', xs: [{op: 'flag', name: `f${i - 1}`}, {op: 'flag', name: `f${i - 1}`}]}
  }
  return {
    name: `flag-fanout-${depth}`,
    params: [],
    inputs: ['idx', 'a', 'b'],
    state: {x: k(0)},
    maps: {M: 0},
    step: {
      flags,
      maps: {
        M: {
          each: 'k',
          value: {
            op: 'if',
            c: {op: 'and', xs: [{op: '=', a: v('k'), b: v('idx')}, {op: 'flag', name: `f${depth}`}]},
            then: value,
            else: {op: 'get', map: 'M', key: v('k')},
          },
        },
      },
    },
  }
}

test('heavy sharing (> 2^25 tree nodes, few distinct) without word-division matches unshared verdicts', () => {
  // depth 21 in flags + 16 map reads -> > 33,554,432 (> 2^25) unfolded tree nodes in @step goal.
  const hugeM = flagFanoutMachine(21, k(1))
  const smallM = flagFanoutMachine(0, k(1))
  const ks = Array.from({length: 16}, (_, i) => i + 1)
  const reads = ks.map((i): C => ({op: '<=', a: {op: 'get', map: 'M', key: k(i)}, b: k(1)}))
  const trueLaw: Law = {name: 'bounded', holds: {op: 'and', xs: reads}}
  const falseLaw: Law = {name: 'too-tight', holds: {op: 'and', xs: ks.map((i): C => ({op: '=', a: {op: 'get', map: 'M', key: k(i)}, b: k(0)}))}}

  const hugeGoals = obligations(hugeM, [trueLaw])
  expect(countDistinct(hugeGoals)).toBeLessThan(1500)
  expect(countTreeNodesCapped(hugeGoals, 20_000_000)).toBeGreaterThan(20_000_000)
  expect(hugeGoals.every(g => !g.wordDivision)).toBe(true)

  const smallTrue = quietly(() => proveLaws(smallM, [trueLaw]))
  const hugeTrue = quietly(() => proveLaws(hugeM, [trueLaw]))
  expect(smallTrue.proven).toBe(true)
  expect(hugeTrue.proven).toBe(true)
  expect(hugeTrue.checked).toBe(true)
  expect(checkLaws(hugeM, [trueLaw], hugeTrue.proof!)).toBe(true)
  expect(checkLaws(hugeM, [falseLaw], hugeTrue.proof!)).toBe(false)

  const smallFalse = quietly(() => proveLaws(smallM, [falseLaw]))
  const hugeFalse = quietly(() => proveLaws(hugeM, [falseLaw]))
  expect(smallFalse.proven).toBe(false)
  expect(hugeFalse.proven).toBe(false)
  expect(hugeFalse.checked).toBe(false)
})

test('heavy sharing (> 2^25 tree nodes) with word-division preserves exact facts and verdicts', () => {
  const key = wordDivisionKey([v('a'), v('b')])
  const q0: E = {op: 'get', map: wordDivisionName(8, 'q', 0), key}
  const hugeDag = sharedMaxDag(q0, 25)
  expect(countDistinct(hugeDag)).toBeLessThan(40)
  expect(countTreeNodesCapped(hugeDag, 20_000_000)).toBeGreaterThan(20_000_000)
  expect(hasWordDivision([hugeDag])).toBe(true)

  // Direct word-division pass on > 2^25 tree nodes must produce identical facts without Set overflow.
  const smallFacts = wordDivisionFacts([q0])
  const hugeFacts = wordDivisionFacts([hugeDag])
  expect(hugeFacts.length).toBeGreaterThan(0)
  expect(hugeFacts).toEqual(smallFacts)

  // End-to-end obligation + kernel checkLaws on > 2^25 unfolded tree nodes with word-division.
  const hugeM = flagFanoutMachine(21, q0)
  const smallM = flagFanoutMachine(0, q0)
  const ks = Array.from({length: 16}, (_, i) => i + 1)
  const okLaw: Law = {name: 'quotient-bound', holds: {op: 'and', xs: ks.map((i): C => ({op: '<', a: {op: 'get', map: 'M', key: k(i)}, b: k(256)}))}}
  const badLaw: Law = {name: 'too-small', holds: {op: 'and', xs: ks.map((i): C => ({op: '<', a: {op: 'get', map: 'M', key: k(i)}, b: k(1)}))}}

  const smallGoals = obligations(smallM, [okLaw])
  const hugeGoals = obligations(hugeM, [okLaw])
  expect(countDistinct(hugeGoals)).toBeLessThan(2000)
  expect(countTreeNodesCapped(hugeGoals, 20_000_000)).toBeGreaterThan(20_000_000)
  expect(hugeGoals.some(g => g.wordDivision)).toBe(true)
  expect(hugeGoals.map(g => g.hyps.length)).toEqual(smallGoals.map(g => g.hyps.length))

  const smallOk = quietly(() => proveLaws(smallM, [okLaw]))
  expect(smallOk.proven).toBe(true)
  expect(smallOk.checked).toBe(true)
  expect(checkLaws(hugeM, [okLaw], smallOk.proof!)).toBe(true)
  expect(checkLaws(hugeM, [badLaw], smallOk.proof!)).toBe(false)
  expect(quietly(() => proveLaws(smallM, [badLaw])).proven).toBe(false)
})

test('word-free shared DAG (> 2^25 tree nodes) skips wordDivisionFacts and checks identically', () => {
  const leaf: E = {op: 'add', a: v('x'), b: k(1)}
  const huge = sharedMaxDag(leaf, 25)
  expect(countDistinct(huge)).toBeLessThan(40)
  expect(hasWordDivision([huge])).toBe(false)
  expect(wordDivisionFacts([huge])).toHaveLength(0)

  const smallGoal = {name: 'small', hyps: [{op: '<', a: leaf, b: v('x')} as C]}
  const hugeGoal = {name: 'huge', hyps: [{op: '<', a: huge, b: v('x')} as C]}
  // x + 1 < x is refuted directly by linear arithmetic (1 <= 0 from fact 0).
  const proof = {leaf: [{kind: 'input' as const, index: 0}]}
  expect(check(smallGoal, proof)).toBe(true)
  expect(check(hugeGoal, proof)).toBe(true)
  expect(check({name: 'sat', hyps: [{op: '<=', a: v('x'), b: huge} as C]}, proof)).toBe(false)
})

test('substE/substC preserve sharing, unchanged references, quantifier shadowing, and cyclic guard', () => {
  const unchanged: E = {op: 'add', a: v('y'), b: k(1)}
  const shared: E = {op: 'add', a: v('x'), b: unchanged}
  const root: E = {op: 'add', a: shared, b: shared}
  const out = substE(root, {vars: {x: k(7)}, maps: {}, flags: {}})
  expect(out.op === 'add' && out.a === out.b).toBe(true)
  expect(out.op === 'add' && out.a.op === 'add' && out.a.b === unchanged).toBe(true)

  const q: C = {op: 'all', key: 'x', c: {op: '=', a: v('x'), b: v('y')}}
  const qOut = substC(q, {vars: {x: k(99), y: k(2)}, maps: {}, flags: {}})
  expect(qOut).toEqual({op: 'all', key: 'x', c: {op: '=', a: v('x'), b: k(2)}})

  const cyc: Record<string, unknown> = {op: 'const', value: 0}
  cyc.self = cyc
  expect(hasWordDivision([cyc])).toBe(false)
  expect(wordDivisionFacts([cyc])).toHaveLength(0)
})
