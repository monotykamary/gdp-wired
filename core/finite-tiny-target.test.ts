import {test, expect} from 'bun:test'
import {type C, type Law, type Machine, type Request, type State, all, any, atMost, get, interpret, ite, less, n, not, plus, same, x} from './machine.ts'
import {finiteEvaluator, finiteTinyHoudini} from './finite-houdini.ts'
import {tinyFiniteCandidates} from './finite-tiny.ts'
import {withWall} from '../kernel/prove.ts'

const sourcePair = (): Machine => ({name: 'partial target fixture', params: [], inputs: ['amount'],
  state: {left: n(0), right: n(0)},
  counts: {unused: {j: 'countRow', key: 'member', below: n(2), body: n(0)}},
  assume: atMost(x('amount'), n(2)),
  step: {flags: {take: less(x('right'), x('amount'))}, state: {
    left: ite({op: 'flag', name: 'take'}, plus(x('left'), x('amount')), x('right')),
    right: ite(less(x('left'), x('right')), x('right'), x('left')),
  }}})
const pairStates = (domain: number[]): State[] => domain.flatMap(left => domain.map(right => ({scalars: {left, right}, maps: {}})))
// Compare concrete transitions, not raw requests: the existing screen may
// quotient inputs which do not affect a particular operation. Keep ALL state
// coordinates and the exact violated-law set, so no real transition is hidden.
const stateKey = (source: Machine, state: State): unknown[] => [
  Object.keys(source.state).sort().map(key => [key, state.scalars[key]]),
  Object.keys(source.maps ?? {}).sort().map(key => [key, [0, 1, 2].map(i => state.maps[key]?.get(i) ?? state.defaults?.[key] ?? source.maps![key])]),
]
const transitionKey = (source: Machine, pre: State, post: State, violated: Law[]): string => JSON.stringify([stateKey(source, pre), stateKey(source, post), violated.map(law => law.name).sort()])
function differential(source: Machine, family: Law[], states: State[], requests: Request[], params: Record<string, number>, domain: number[]): void {
  const evaluate = finiteEvaluator(source), run = interpret(source), expected = new Set<string>()
  for (const pre of states) {
    if (!family.every(law => evaluate(law, params, pre) === true)) continue
    for (const request of requests) {
      const post = run.step(params, pre, request), violated = family.filter(law => evaluate(law, params, post) === false)
      if (violated.length) expected.add(transitionKey(source, pre, post, violated))
    }
  }
  for (const [postTargetPruning, postTargetIntervals] of [[false, false], [true, false], [true, true]] as const) {
    const actual = new Set<string>()
    const stats = tinyFiniteCandidates(source, source, family, params, (pre, request, proposed) => {
      expect(family.every(law => evaluate(law, params, pre) === true)).toBe(true)
      const post = run.step(params, pre, request), violated = family.filter(law => evaluate(law, params, post) === false)
      expect(proposed.map(law => law.name).sort()).toEqual(violated.map(law => law.name).sort())
      expect(violated.length).toBeGreaterThan(0)
      actual.add(transitionKey(source, pre, post, violated)); return false
    }, {valueDomain: domain, postTargetPruning, postTargetIntervals})
    expect(stats.unsupported).toEqual([])
    expect(stats.completed).toBe(true)
    expect(stats.scope.postTargetPruning).toBe(postTargetPruning)
    expect(stats.scope.postTargetIntervals).toBe(postTargetIntervals)
    expect([...actual].sort()).toEqual([...expected].sort())
  }
}
const forms: [string, C][] = [
  ['atom', atMost(x('left'), n(1))],
  ['negated atom', not(same(x('left'), x('right')))],
  ['disjunction', any(same(x('left'), n(0)), same(x('right'), n(1)))],
  ['conjunction', all(atMost(x('left'), n(1)), atMost(x('right'), n(1)))],
  ['negated conjunction', not(all(same(x('left'), n(1)), same(x('right'), n(1))))],
  ['negated disjunction', not(any(same(x('left'), n(0)), same(x('right'), n(0))))],
  ['nested polarity', any(not(atMost(x('left'), n(1))), all(same(x('right'), n(0)), not(same(x('left'), n(0)))))],
  ['conditional term', same(ite(same(x('right'), n(1)), x('left'), x('right')), n(1))],
  ['interval sum', atMost(plus(x('left'), x('right')), n(2))],
  ['interval truncated subtraction', not(same({op: 'sub', a: x('right'), b: x('left')}, n(1)))],
  ['interval product', less({op: 'prod', a: x('left'), b: x('right')}, n(3))],
  ['interval minimum', same({op: 'min', a: x('left'), b: x('right')}, n(1))],
  ['interval maximum', not(less({op: 'max', a: x('left'), b: x('right')}, n(1)))],
]
for (const [title, holds] of forms) test(`post-target pruning preserves all concrete transitions: ${title}`, () => {
  for (const domain of [[0, 1], [0, 1, 2]]) differential(sourcePair(), [{name: title, holds}], pairStates(domain), [0, 1, 2].map(amount => ({amount})), {}, domain)
})
test('partial post coordinates retain their own source readiness after a swap', () => {
  const source = sourcePair()
  source.step = {state: {left: x('right'), right: plus(x('left'), x('amount'))}}
  const family: Law[] = [{name: 'swapped disjunction', holds: any(less(x('right'), n(1)), same(x('left'), n(1)))}]
  differential(source, family, pairStates([0, 1, 2]), [0, 1, 2].map(amount => ({amount})), {}, [0, 1, 2])
})
test('a target unaffected by another output is not made to depend on that output', () => {
  const source = sourcePair()
  source.step = {state: {left: x('left'), right: plus(x('right'), x('amount'))}}
  const family: Law[] = [{name: 'left is zero', holds: same(x('left'), n(0))}]
  differential(source, family, pairStates([0, 1, 2]), [0, 1, 2].map(amount => ({amount})), {}, [0, 1, 2])
})
test('post-target pruning retains unknown late request dependencies', () => {
  const source = sourcePair()
  source.step = {state: {left: plus(x('left'), x('amount')), right: x('right')}}
  const law: Law = {name: 'left bounded', holds: atMost(x('left'), n(1))}
  differential(source, [law], pairStates([0, 1]), [0, 1, 2].map(amount => ({amount})), {}, [0, 1])
  let late = false
  const stats = tinyFiniteCandidates(source, source, [law], {}, (pre, request) => {
    if (pre.scalars.left === 0 && request.amount === 2) late = true
    return false
  }, {postTargetPruning: true})
  expect(late).toBe(true)
  expect(stats.postRequestPrunes).toBeGreaterThan(0)
})
test('a definitely holding postcondition prunes states without claiming universal proof', () => {
  const source = sourcePair(); source.step = {state: {left: n(0), right: x('right')}}
  const law: Law = {name: 'nonpositive left', holds: atMost(x('left'), n(0))}
  const plain = tinyFiniteCandidates(source, source, [law], {}, () => { throw Error('no violation') })
  const pruned = tinyFiniteCandidates(source, source, [law], {}, () => { throw Error('no violation') }, {postTargetPruning: true})
  expect(plain.states).toBeGreaterThan(0)
  expect(pruned.states).toBe(0)
  expect(pruned.postStatePrunes).toBeGreaterThan(0)
  expect(pruned.completed).toBe(true)
  expect(pruned.scope.scalarValues).toEqual([0, 1])
})
test('whole-family and multiple-target transitions survive post-target pruning', () => {
  const source = sourcePair(), family: Law[] = [
    {name: 'bounded left', holds: atMost(x('left'), n(1))},
    {name: 'equal pair or zero', holds: any(same(x('left'), x('right')), same(x('left'), n(0)))},
    {name: 'right remains binary', holds: atMost(x('right'), n(1))},
  ]
  differential(source, family, pairStates([0, 1, 2]), [0, 1, 2].map(amount => ({amount})), {}, [0, 1, 2])
})
test('source map writes and recomputed lifted counts preserve every transition', () => {
  const source: Machine = {name: 'map target fixture', params: ['width'], inputs: ['row', 'bit'], state: {}, maps: {table: 0},
    counts: {total: {j: 'outer', key: 'member', below: x('width'), body: get('table', x('member'))}},
    assume: all(less(x('row'), x('width')), atMost(x('bit'), n(1))),
    step: {maps: {table: {key: x('row'), value: x('bit')}}}}
  const law: Law = {name: 'not full', holds: atMost(get('total', n(0)), n(1))}
  const states: State[] = [0, 1].flatMap(a => [0, 1].map(b => ({scalars: {}, maps: {table: new Map([[0, a], [1, b]])}})))
  differential(source, [law], states, [0, 1].flatMap(row => [0, 1].map(bit => ({row, bit}))), {width: 2}, [0, 1])
})
test('interval counts prune before every unchanged post cell is exact', () => {
  const source: Machine = {name: 'interval count fixture', params: [], inputs: [], state: {}, maps: {table: 0},
    counts: {total: {j: 'outer', key: 'member', below: n(3), body: get('table', x('member'))}},
    step: {maps: {table: {key: n(0), value: n(0)}}}}
  const law: Law = {name: 'at most one cell', holds: atMost(get('total', n(0)), n(1))}
  const states: State[] = [0, 1].flatMap(a => [0, 1].flatMap(b => [0, 1].map(c => ({scalars: {}, maps: {table: new Map([[0, a], [1, b], [2, c]])}}))))
  differential(source, [law], states, [{}], {}, [0, 1])
  const reject = () => { throw Error('zeroing a cell cannot violate its sum bound') }
  const point = tinyFiniteCandidates(source, source, [law], {}, reject, {postTargetPruning: true})
  const interval = tinyFiniteCandidates(source, source, [law], {}, reject, {postTargetPruning: true, postTargetIntervals: true})
  expect(interval.postStatePrunes).toBeGreaterThan(0)
  expect(interval.nodes).toBeLessThan(point.nodes)
  expect(interval.completed).toBe(true)
  expect(interval.postIntervalFallbacks).toBe(0)
})
test('oversize interval predicates fall back to bounded readiness screens', () => {
  const source = sourcePair(); source.step = {state: {left: plus(x('left'), x('amount')), right: x('right')}}
  const law: Law = {name: 'large repeated bound', holds: all(...Array.from({length: 4096}, () => atMost(x('left'), n(1))))}
  differential(source, [law], pairStates([0, 1]), [0, 1, 2].map(amount => ({amount})), {}, [0, 1])
  const stats = tinyFiniteCandidates(source, source, [law], {}, () => false, {postTargetPruning: true, postTargetIntervals: true})
  expect(stats.postIntervalFallbacks).toBeGreaterThan(0)
  expect(stats.unsupported).toEqual([])
  expect(stats.completed).toBe(true)
})
test('accepted targets may stop but rejected proposals do not consume a target', () => {
  const source = sourcePair(); source.step = {state: {left: plus(x('left'), n(1)), right: x('right')}}
  const family: Law[] = [{name: 'zero', holds: same(x('left'), n(0))}, {name: 'bounded', holds: atMost(x('left'), n(0))}]
  let accepted = 0, rejected = 0
  const yes = tinyFiniteCandidates(source, source, family, {}, () => { accepted++ }, {postTargetPruning: true})
  const no = tinyFiniteCandidates(source, source, family, {}, () => { rejected++; return false }, {postTargetPruning: true})
  expect(accepted).toBe(1)
  expect(rejected).toBeGreaterThan(accepted)
  expect(yes.completed && no.completed).toBe(true)
})
test('post-target pruning cannot drop callers or bypass declared facts', () => {
  const source = sourcePair(); source.step = {state: {left: plus(x('left'), n(1)), right: x('right')}}
  const caller: Law = {name: 'right zero', holds: same(x('right'), n(0))}, candidate: Law = {name: 'left zero', holds: same(x('left'), n(0))}
  expect(finiteTinyHoudini(source, source, [caller], [candidate], [{}], {postTargetPruning: true, postTargetIntervals: true})).toEqual([])
  const forbidden: Machine = {...source, facts: [{name: 'impossible', holds: same(n(0), n(1))}]}
  expect(finiteTinyHoudini(source, forbidden, [caller], [candidate], [{}], {postTargetPruning: true, postTargetIntervals: true})).toEqual([candidate])
})
test('unsupported syntax and expired walls remain unknown with target pruning', () => {
  const source = {...sourcePair(), fns: {opaque: {js: 'x => x'}}}, law: Law = {name: 'opaque', holds: same(get('opaque', x('left')), n(0))}
  const stats = tinyFiniteCandidates(source, source, [law], {}, () => { throw Error('unsupported') }, {postTargetPruning: true, postTargetIntervals: true})
  expect(stats.unsupported).toContain('external function')
  expect(stats.exhausted).toBe(false)
  const expired = withWall(performance.now() - 1, () => tinyFiniteCandidates(source, source, [law], {}, () => {}, {postTargetPruning: true, postTargetIntervals: true}))
  expect(expired.timedOut).toBe(true)
  expect(expired.completed).toBe(false)
})
