import {expect, test} from 'bun:test'
import {type Law, type Machine, type State, type Request, atMost, get, interpret, ite, n, plus, same, x} from './machine.ts'
import {finiteEvaluator, finiteTinyHoudini, type FiniteDrop} from './finite-houdini.ts'
import {tinyFiniteCandidates, type TinyFiniteSeed, type TinyFiniteStatistics} from './finite-tiny.ts'
import {withWall} from '../kernel/prove.ts'
import {WallExpired} from './wall.ts'

const counter = (): Machine => ({name: 'seed fixture', params: [], inputs: ['delta'], state: {value: n(0), other: n(0)},
  counts: {unused: {j: 'row', key: 'member', below: n(2), body: n(0)}}, assume: atMost(x('delta'), n(2)),
  step: {state: {value: plus(x('value'), x('delta')), other: x('value')}}})
const seed: TinyFiniteSeed = {params: {}, pre: {scalars: {value: 0, other: 1}, maps: {}}, request: {delta: 1}}
const key = (pre: State, post: State, laws: Law[]) => JSON.stringify([pre.scalars, post.scalars, laws.map(law => law.name).sort()])

test('seed neighborhoods retain every concrete transition in the unchanged finite grids', () => {
  const source = counter(), run = interpret(source), evaluate = finiteEvaluator(source)
  const family: Law[] = [{name: 'value bounded', holds: atMost(x('value'), n(1))}, {name: 'other bounded', holds: atMost(x('other'), n(1))}]
  const original = JSON.stringify(seed)
  for (const domain of [[0, 1], [0, 1, 2]]) {
    const expected = new Set<string>()
    for (const value of domain) for (const other of domain) for (const delta of [0, 1, 2]) {
      const pre = {scalars: {value, other}, maps: {}}
      if (!family.every(law => evaluate(law, {}, pre) === true)) continue
      const post = run.step({}, pre, {delta}), violated = family.filter(law => evaluate(law, {}, post) === false)
      if (violated.length) expected.add(key(pre, post, violated))
    }
    for (const [postTargetPruning, postTargetIntervals] of [[false, false], [true, false], [true, true]] as const) {
      const actual = new Set<string>()
      const stats = tinyFiniteCandidates(source, source, family, {}, (pre, request, proposed) => {
        expect(Object.values(pre.scalars).every(value => domain.includes(value))).toBe(true)
        expect(family.every(law => evaluate(law, {}, pre) === true)).toBe(true)
        const post = run.step({}, pre, request), violated = family.filter(law => evaluate(law, {}, post) === false)
        expect(proposed.map(law => law.name).sort()).toEqual(violated.map(law => law.name).sort())
        actual.add(key(pre, post, violated)); return false
      }, {valueDomain: domain, postTargetPruning, postTargetIntervals, seedTransitions: [seed]})
      expect([...actual].sort()).toEqual([...expected].sort())
      expect(stats.completed).toBe(true)
      expect(stats.seedModels).toBeGreaterThan(0)
      expect(stats.seedCandidates).toBeGreaterThan(0)
      expect(stats.scope.seedNeighborhood).toBe(true)
      expect(stats.scope.scalarValues).toEqual(domain)
    }
  }
  expect(JSON.stringify(seed)).toBe(original)
})

test('seed attempts stop at 256 and keep only the last eight seed projections', () => {
  const source = counter()
  source.assume = atMost(x('delta'), n(16))
  source.state = {...source.state, ...Object.fromEntries(Array.from({length: 32}, (_, i) => [`cell${i}`, n(0)]))}
  const seeds: TinyFiniteSeed[] = Array.from({length: 12}, (_, j) => ({params: {}, request: {delta: 2}, pre: {scalars: {value: 0, other: 0,
    ...Object.fromEntries(Array.from({length: 32}, (_, i) => [`cell${i}`, i < 4 ? (j >> i) & 1 : 0]))}, maps: {}}}))
  const law: Law = {name: 'bounded', holds: atMost(x('value'), n(1))}
  const stats = tinyFiniteCandidates(source, source, [law], {}, () => {}, {postTargetPruning: true, seedTransitions: seeds})
  expect(stats.completed).toBe(true)
  expect(stats.seedModels).toBe(256)
  expect(stats.seedCandidates).toBe(1)
  const rejected = Array.from({length: 8}, () => ({...seed, params: {different: 1}, pre: {scalars: {value: 9, other: 9}, maps: {}}}))
  const lastEight = tinyFiniteCandidates(counter(), counter(), [law], {}, () => {}, {postTargetPruning: true, seedTransitions: [seed, ...rejected]})
  expect(lastEight.seedModels).toBe(0)
})

test('wrong parameters and out-of-grid seed coordinates are ignored, not clamped', () => {
  const source = counter(); source.params = ['width']
  const invalid: TinyFiniteSeed[] = [
    {...seed, params: {width: 2}},
    {...seed, params: {width: 1}, pre: {scalars: {value: 2, other: 0}, maps: {}}},
    {...seed, params: {width: 1}, request: {delta: 3}},
  ]
  const stats = tinyFiniteCandidates(source, source, [{name: 'bounded', holds: atMost(x('value'), n(1))}], {width: 1}, () => false, {seedTransitions: invalid})
  expect(stats.seedModels).toBe(0)
  expect(stats.completed).toBe(true)
  expect(stats.scope.scalarValues).toEqual([0, 1])
  expect(stats.scope.inputValues.delta).toEqual([0, 1, 2])
})

test('seeded proposals still require the whole family, callers and supported declarations', () => {
  const source = counter(), zero: Law = {name: 'zero', holds: same(x('value'), n(0))}
  const options = {seedTransitions: [seed], postTargetPruning: true}
  expect(finiteTinyHoudini(source, source, [zero], [zero], [{}], options)).toEqual([zero])
  expect(finiteTinyHoudini(source, {...source, pre: same(n(0), n(1))}, [], [zero], [{}], options)).toEqual([zero])
  const unsupported: Law = {name: 'unknown declaration', holds: {op: 'all', key: 'member', c: same(n(0), n(0))}}
  expect(finiteTinyHoudini(source, {...source, facts: [unsupported]}, [], [zero], [{}], options)).toEqual([zero])
  const records: TinyFiniteStatistics[] = []
  expect(finiteTinyHoudini(source, source, [], [zero], [{}], {...options, onTiny: (_round, stats) => records.push(stats)})).toEqual([])
  expect(records.some(stats => stats.seedCandidates > 0)).toBe(true)
})

test('certified drops can seed later rounds without mutating earlier witnesses', () => {
  const source = counter(); source.inputs = []; source.assume = undefined
  source.step = {state: {value: plus(x('value'), n(1)), other: x('value')}}
  const a: Law = {name: 'first', holds: same(x('value'), n(0))}, b: Law = {name: 'next', holds: same(x('other'), n(0))}
  const seeds: TinyFiniteSeed[] = [], drops: FiniteDrop[] = [], stats: {round: number, row: TinyFiniteStatistics}[] = []
  expect(finiteTinyHoudini(source, source, [], [a, b], [{}], {postTargetPruning: true, seedTransitions: seeds,
    onDrop: drop => { drops.push(drop); seeds.push(drop) }, onTiny: (round, row) => stats.push({round, row}),
  })).toEqual([])
  expect(drops.map(drop => [drop.round, drop.law.name])).toEqual([[0, 'first'], [1, 'next']])
  expect(stats.find(row => row.round === 1)!.row.seedCandidates).toBeGreaterThan(0)
  expect(seeds[0]!.pre.scalars).toEqual({value: 0, other: 0})
})

test('seed neighborhoods cover carried request cells without changing their domain', () => {
  const source: Machine = {name: 'carried seed fixture', params: [], inputs: ['select'], inputMaps: ['bits'], state: {value: n(0)},
    counts: {unused: {j: 'row', key: 'member', below: n(1), body: n(0)}}, assume: atMost(x('select'), n(1)),
    step: {state: {value: ite(same(x('select'), n(1)), get('bits', n(0)), x('value'))}}}
  const law: Law = {name: 'zero', holds: same(x('value'), n(0))}, request: Request = {select: 1, bits: new Map([[0, 0]])}
  let hits = 0
  const stats = tinyFiniteCandidates(source, source, [law], {}, (pre, input) => {
    expect(pre.scalars.value).toBe(0)
    expect(interpret(source).step({}, pre, input).scalars.value).toBe(1)
    expect((input.bits as Map<number, number>).get(0)).toBe(1)
    hits++; return false
  }, {seedTransitions: [{params: {}, pre: {scalars: {value: 0}, maps: {}}, request}]})
  expect(stats.seedCandidates).toBeGreaterThan(0)
  expect(hits).toBeGreaterThan(0)
  expect(stats.scope.inputCells.bits).toEqual([0])
  expect((request.bits as Map<number, number>).get(0)).toBe(0)
})

test('seed processing never extends the finite wall or swallows an outer expiration', () => {
  const source = counter(), law: Law = {name: 'zero', holds: same(x('value'), n(0))}
  let timedOut = false
  expect(finiteTinyHoudini(source, source, [], [law], [{}], {seedTransitions: [seed], wallMs: 0, onFinish: row => { timedOut = row.timedOut }})).toEqual([law])
  expect(timedOut).toBe(true)
  expect(() => withWall(performance.now() - 1, () => finiteTinyHoudini(source, source, [], [law], [{}], {seedTransitions: [seed]}))).toThrow(WallExpired)
})
