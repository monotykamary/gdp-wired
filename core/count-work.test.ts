import {expect, spyOn, test} from 'bun:test'
import {admitCountedFamily} from './counts.ts'
import {type Law, type Machine, all, any, atMost, get, n, same, x} from './machine.ts'
import {checkCountedLaws} from '../kernel/kernel.ts'
import {clock, counted, fullRate, withWall} from '../kernel/prove.ts'

const machine = (broken = false): Machine => ({name: 'counted supported family', params: [], inputs: ['action'], inputMaps: ['Input'], state: {value: n(0)},
  counts: {Rows: {j: 'row', key: 'member', below: n(2), body: n(1)}},
  assume: all(any(...[0, 1, 2].map(i => same(x('action'), n(i))))), step: {state: {value: broken ? n(3) : get('Rows', n(0))}}})
const bounded: Law = {name: 'bounded', holds: atMost(x('value'), n(2))}
function admission(jump: number, broken = false, allowance = 3000) {
  let wall = 1_000_000
  const mock = spyOn(performance, 'now').mockImplementation(() => (wall += jump))
  try {
    return withWall(Infinity, () => counted(fullRate, () => {
      const m = machine(broken), result = admitCountedFamily(m, [bounded], [bounded], new Set([bounded]), clock() + allowance)
      return {proven: result.proven, laws: result.laws.map(l => l.name), checked: !!result.proof && checkCountedLaws(m, result.laws, result.proof)}
    }, true))
  } finally { mock.mockRestore() }
}

test('supported admission is unchanged by a slow or jumping telemetry clock', () => {
  const expected = {proven: true, laws: ['bounded'], checked: true}
  for (const jump of [0, 10_000, 1_000_000]) expect(admission(jump)).toEqual(expected)
})

test('clock independence cannot admit a false caller', () => {
  for (const jump of [0, 10_000, 1_000_000]) expect(admission(jump, true)).toEqual({proven: false, laws: ['bounded'], checked: false})
})

test('supported admission cannot revive an exhausted counted allowance', () => {
  for (const jump of [0, 10_000]) expect(admission(jump, false, 0)).toEqual({proven: false, laws: ['bounded'], checked: false})
})
