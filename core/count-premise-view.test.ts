import {expect, test} from 'bun:test'
import {type Law, type Machine, all, any, get, n, not, same, x} from './machine.ts'
import {countPremiseMaps, countPremiseView} from './count-premise-view.ts'
import {clock, counted, fullRate} from '../kernel/prove.ts'
function fixture(prefix: string) {
  const name = (s: string) => prefix + s, op = x('operation')
  const m: Machine = {name: 'renamed containment', params: [], inputs: ['operation', 'source', 'dest'], inputMaps: ['inactive'].map(name), state: {}, maps: Object.fromEntries(['rows', 'payload', 'inactive', 'guard', 'extra'].map(s => [name(s), 0])),
    assume: all(any(same(op, n(0)), same(op, n(1)), same(op, n(2))), same(op, n(2)), any(not(same(op, n(2))), {op: '<=', a: n(1), b: get(name('guard'), x('source'))})),
    step: {flags: {copy: all(same(op, n(2)), {op: '<=', a: n(1), b: get(name('guard'), x('source'))})}, maps: {[name('rows')]: {each: 'row', value: {op: 'if', c: same(op, n(1)), then: get(name('inactive'), x('row')), else: {op: 'if', c: {op: 'flag', name: 'copy'}, then: get(name('payload'), x('row')), else: get(name('rows'), x('row'))}}}}}}
  const law: Law = {name: 'arbitrary row claim', forall: 'a', keys: ['b'], holds: same(get(name('rows'), x('a')), get(name('rows'), x('b')))}
  return {m, law, name}
}
test('containment follows the active operation and target writes, not map spelling', () => counted(fullRate, () => {
  for (const prefix of ['alpha_', 'other_']) {
    const {m, law, name} = fixture(prefix), before = JSON.stringify(m)
    const maps = countPremiseMaps(m, law, clock() + 1000)
    expect(maps).toEqual(new Set(['map:' + name('rows'), 'map:' + name('guard'), 'map:' + name('payload')]))
    expect(JSON.stringify(m)).toBe(before)
  }
}, true))
test('a shared cell cannot admit a hypothesis with an extra uncontained map', () => counted(fullRate, () => {
  const {m, law, name} = fixture('test_'), row = get(name('rows'), x('a'))
  const root = {op: '<' as const, a: n(0), b: row}, kept = {op: '<=' as const, a: row, b: get(name('payload'), x('a'))}
  const extra = {op: '<=' as const, a: row, b: get(name('extra'), x('a'))}, bridge = same(get(name('payload'), x('a')), get(name('extra'), x('a')))
  const goal = {name: 'full', hyps: [kept, extra, bridge, root]}, view = countPremiseView(goal, m, law, root, [], clock() + 1000)
  expect(view?.selected).toEqual([0, 3]); expect(view?.omitted).toEqual([1, 2])
  expect(view?.goal.hyps).toEqual([kept, root]); expect(goal.hyps).toEqual([kept, extra, bridge, root])
}, true))
test('data-first containment distinguishes opaque Boolean control from copied data', () => counted(fullRate, () => {
  const {m, law, name} = fixture('guard_'), control = name('control')
  m.maps![control] = 0
  m.step.maps![control] = {each: 'k', value: {op: 'if', c: same(x('operation'), n(0)), then: n(1), else: n(0)}}
  m.step.flags!.copy = all(m.step.flags!.copy!, same(get(control, x('dest')), n(1)))
  expect(countPremiseMaps(m, law, clock() + 1000, false)?.has('map:' + control)).toBe(false)
  expect(countPremiseMaps(m, law, clock() + 1000, true)?.has('map:' + control)).toBe(true)
}, true))
test('derived count vocabulary requires every underlying read', () => counted(fullRate, () => {
  const {m, law, name} = fixture('count_')
  m.counts = {local: {j: 'r', key: 'k', below: n(4), body: get(name('rows'), x('k'))}, foreign: {j: 'r', key: 'k', below: n(4), body: get(name('extra'), x('k'))}}
  const maps = countPremiseMaps(m, law, clock() + 1000, false)
  expect(maps?.has('map:local')).toBe(true)
  expect(maps?.has('map:foreign')).toBe(false)
}, true))
test('expired or structurally unsupported containment does not manufacture a view', () => counted(fullRate, () => {
  const {m, law} = fixture('expired_'), goal = {name: 'full', hyps: [law.holds]}
  expect(countPremiseView(goal, m, law, law.holds, [], clock() - 1)).toBeUndefined()
  delete m.assume
  expect(countPremiseMaps(m, law, clock() + 1000)).toBeUndefined()
}, true))
