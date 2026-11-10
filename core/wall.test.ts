import {expect, spyOn, test} from 'bun:test'
import {proveRule, rule} from './dsl.ts'
import {searchCounted} from './counts.ts'
import {smallOf, holdsAt} from './exists.ts'
import {type Machine, interpret, n, plus, same, x} from './machine.ts'
import {watch, watchWork} from './watch.ts'
import {counted, clock, fullRate, fullWork, withWall} from '../kernel/prove.ts'
import {WallExpired, checkWall, searchWall} from './wall.ts'
const machine = (): Machine => ({name: 'deadline counter', params: [], inputs: [], state: {n: n(0)}, step: {state: {n: plus(x('n'), n(1))}}})
test('completion headroom is bounded, protocol independent, and leaves counted fuel unchanged', () => {
  const now = spyOn(performance, 'now').mockReturnValue(100)
  try {
    expect(searchWall(60_000)).toBe(59_100)
    expect(searchWall(100)).toBe(195)
    expect(searchWall(-1)).toBe(99)
    expect(counted(fullRate, () => { const t = clock(); searchWall(60_000); return clock() - t }, true)).toBe(0)
  } finally { now.mockRestore() }
})
test('an expired counted call stops before generation and spends no counted work', () => {
  const m = machine(), before = fullWork()
  const result = withWall(-Infinity, () => searchCounted(m, [], 1000))
  expect(result).toMatchObject({proven: false, why: 'time (guards)'})
  expect(result.m).toBe(m)
  expect(fullWork()).toBe(before)
})
test('the public rule deadline includes preflight and cannot be extended by a nested budget', () => {
  const r = rule('deadline identity').state({x: 0}).step(({x}) => ({x})), law = r.law('zero', ({x}) => x.eq(0))
  const params = spyOn(r, 'randomParams')
  try {
    expect(withWall(-Infinity, () => proveRule(r, [law], {search: {ms: 1000}}))).toMatchObject({proven: false, checked: false, stuck: 'unknown'})
    expect(params).not.toHaveBeenCalled()
    expect(proveRule(r, [law], {search: {ms: -1}})).toMatchObject({proven: false, checked: false, stuck: 'unknown'})
  } finally { params.mockRestore() }
  expect(proveRule(r, [law], {search: false})).toMatchObject({proven: true, checked: true})
})
test('interrupted sampling never caches a partial graph or an empty success', () => {
  const m = machine(), before = fullWork()
  let ticks = 0
  const now = spyOn(performance, 'now').mockImplementation(() => ++ticks < 20 ? 0 : 100)
  try { expect(() => withWall(10, () => smallOf(m))).toThrow(WallExpired) }
  finally { now.mockRestore() }
  expect(fullWork()).toBe(before)
  expect(smallOf(m)[0]!.sts.length).toBeGreaterThan(20)
  expect(smallOf(m)).toEqual(smallOf(machine()))
})
test('preflight binding enumeration checks the wall before charging another tuple', () => {
  const m = machine(), before = watchWork.n, run = interpret(m)
  const watching = watch(m, run, {name: 'keys', forall: 'a', keys: ['b'], holds: same(n(0), n(0))}, {}, 3)
  expect(() => withWall(-Infinity, () => watching.start(run.init({})))).toThrow(WallExpired)
  expect(watchWork.n).toBe(before)
})
test('binding enumeration observes the wall, and checkpoints do not debit the counted clock', () => {
  const m = machine(), st = smallOf(m)[0]!.sts[0]!, law = {name: 'many bindings', forall: 'a', keys: ['b', 'c', 'd', 'e', 'f'], holds: same(n(0), n(0))}
  let ticks = 0
  const now = spyOn(performance, 'now').mockImplementation(() => ++ticks < 20 ? 0 : 100)
  try { expect(() => withWall(10, () => holdsAt(m, law, {}, st, 4))).toThrow(WallExpired) }
  finally { now.mockRestore() }
  expect(holdsAt(m, law, {}, st, 4)).toBe(true)
  expect(counted(fullRate, () => { const t = clock(); checkWall('test'); return clock() - t }, true)).toBe(0)
})
