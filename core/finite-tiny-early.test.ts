import {expect, test} from 'bun:test'
import {type Law, type Machine, all, atMost, get, ite, n, plus, same, x} from './machine.ts'
import {finiteTinyHoudini, type FiniteDrop} from './finite-houdini.ts'
import {tinySeedCandidates, type TinyFiniteSeed, type TinyFiniteStatistics, type TinySeedStatistics} from './finite-tiny.ts'
import {withWall} from '../kernel/prove.ts'
import {WallExpired} from './wall.ts'

const counter = (): Machine => ({name: 'early seed fixture', params: [], inputs: ['delta'], state: {value: n(0), other: n(0)},
  counts: {unused: {j: 'row', key: 'member', below: n(2), body: n(0)}}, assume: atMost(x('delta'), n(2)),
  step: {state: {value: plus(x('value'), x('delta')), other: x('value')}}})
const seed: TinyFiniteSeed = {params: {}, pre: {scalars: {value: 0, other: 0}, maps: {}}, request: {delta: 1}}
const zero: Law = {name: 'zero', holds: same(x('value'), n(0))}

test('seed-only enumeration does not compile native steps or claim exhaustion', () => {
  const source = counter(); source.step = {state: {value: get('not compiled here', x('value'))}}
  let calls = 0
  const stats = tinySeedCandidates(source, source, {}, (pre, request) => {
    expect(pre.scalars.value === 0 || pre.scalars.value === 1).toBe(true)
    expect(typeof request.delta === 'number' && [0, 1, 2].includes(request.delta)).toBe(true)
    calls++; return false
  }, {seedTransitions: [seed]})
  expect(calls).toBeGreaterThan(0)
  expect(stats.completed).toBe(true)
  expect(stats.accepted).toBe(0)
  expect(stats.phase).toBe('seed-only')
  expect('exhausted' in stats).toBe(false)
})

test('seed-only enumeration has the same 256-model cap and finite domains', () => {
  const source = counter(); source.assume = atMost(x('delta'), n(16))
  source.state = {...source.state, ...Object.fromEntries(Array.from({length: 32}, (_, i) => [`cell${i}`, n(0)]))}
  const seeds: TinyFiniteSeed[] = Array.from({length: 12}, (_, j) => ({params: {}, request: {delta: 2}, pre: {scalars: {value: 0, other: 0,
    ...Object.fromEntries(Array.from({length: 32}, (_, i) => [`cell${i}`, i < 4 ? (j >> i) & 1 : 0]))}, maps: {}}}))
  const stats = tinySeedCandidates(source, source, {}, () => false, {seedTransitions: seeds, seedUniformMaps: true})
  expect(stats.models).toBe(256)
  expect(stats.accepted).toBe(0)
  expect(stats.scope.scalarValues).toEqual([0, 1])
  expect(stats.completed).toBe(true)
  expect(tinySeedCandidates(source, source, {}, () => true, {valueDomain: [NaN], seedTransitions: seeds}).models).toBe(0)
})

test('front-loaded seeds certify before native work and never get a second allowance', () => {
  const source = counter(), events: string[] = [], early: TinySeedStatistics[] = [], native: TinyFiniteStatistics[] = []
  const seeds = [{...seed, pre: {scalars: {value: 1, other: 0}, maps: {}}}]
  const bounded: Law = {name: 'bounded', holds: atMost(x('value'), n(1))}
  expect(finiteTinyHoudini(source, source, [], [bounded], [{}], {rounds: 1, seedTransitions: seeds, seedBeforeCompile: true,
    onDrop: () => events.push('drop'), onSeed: (_round, stats) => { early.push(stats); events.push('seed') },
    onTiny: (_round, stats) => { native.push(stats); events.push('native') },
  })).toEqual([])
  expect(events.indexOf('drop')).toBeLessThan(events.indexOf('native'))
  expect(events.indexOf('seed')).toBeLessThan(events.indexOf('native'))
  expect(early[0]!.accepted).toBe(1)
  expect(early[0]!.models).toBeLessThanOrEqual(256)
  expect(native.every(stats => stats.seedModels === 0 && !stats.scope.seedNeighborhood)).toBe(true)
})

test('early and native phases share one frozen whole family per round', () => {
  const source = counter(); source.inputs = []; source.assume = undefined
  source.step = {state: {value: plus(x('value'), n(1)), other: x('value')}}
  const a: Law = {name: 'first', holds: same(x('value'), n(0))}, b: Law = {name: 'next', holds: same(x('other'), n(0))}
  const drops: FiniteDrop[] = [], seeds = [{...seed, request: {}}]
  expect(finiteTinyHoudini(source, source, [], [a, b], [{}], {rounds: 2, seedTransitions: seeds, seedBeforeCompile: true,
    onDrop: drop => drops.push(drop),
  })).toEqual([])
  expect(drops.map(drop => [drop.round, drop.law.name])).toEqual([[0, 'first'], [1, 'next']])
})

test('front-loaded seeds preserve callers, source preconditions and unknown facts', () => {
  const source = counter(), options = {seedTransitions: [seed], seedBeforeCompile: true}
  expect(finiteTinyHoudini(source, source, [zero], [zero], [{}], options)).toEqual([zero])
  expect(finiteTinyHoudini(source, {...source, facts: [{name: 'impossible', holds: same(n(0), n(1))}]}, [], [zero], [{}], options)).toEqual([zero])
  const forbidden = {...source, pre: same(n(0), n(1))}
  expect(finiteTinyHoudini(forbidden, source, [], [zero], [{}], options)).toEqual([zero])
  const unknown: Law = {name: 'unknown', holds: {op: 'all', key: 'member', c: same(n(0), n(0))}}
  expect(finiteTinyHoudini(source, {...source, facts: [unknown]}, [], [zero], [{}], options)).toEqual([zero])
})

test('ordinary search still runs after front-loaded seeds find nothing', () => {
  const source: Machine = {name: 'two-coordinate guard', params: [], inputs: [], state: {a: n(0), b: n(0), value: n(0)},
    counts: {unused: {j: 'row', key: 'member', below: n(1), body: n(0)}},
    step: {state: {value: ite(all(same(x('a'), n(1)), same(x('b'), n(1))), n(1), x('value'))}}}
  const seeds = [{params: {}, pre: {scalars: {a: 0, b: 0, value: 0}, maps: {}}, request: {}}]
  let accepted = -1, native = 0
  expect(finiteTinyHoudini(source, source, [], [zero], [{}], {rounds: 1, seedTransitions: seeds, seedBeforeCompile: true,
    onSeed: (_round, stats) => { accepted = stats.accepted }, onTiny: () => { native++ },
  })).toEqual([])
  expect(accepted).toBe(0)
  expect(native).toBe(1)
})

test('seed-only and front-loaded paths preserve expiration and pending survivors', () => {
  const source = counter()
  const stats = withWall(performance.now() - 1, () => tinySeedCandidates(source, source, {}, () => true, {seedTransitions: [seed]}))
  expect(stats.timedOut).toBe(true)
  expect(stats.completed).toBe(false)
  expect(stats.accepted).toBe(0)
  expect(finiteTinyHoudini(source, source, [], [zero], [{}], {seedTransitions: [seed], seedBeforeCompile: true, wallMs: 0})).toEqual([zero])
  expect(() => withWall(performance.now() - 1, () => finiteTinyHoudini(source, source, [], [zero], [{}], {seedTransitions: [seed], seedBeforeCompile: true}))).toThrow(WallExpired)
})
