import {expect, test} from 'bun:test'
import {type Law, type Machine, type State, n, plus, same, x} from './machine.ts'
import {finiteHoudini, type FiniteOptions} from './finite-houdini.ts'
import {WallExpired} from './wall.ts'
import {withWall} from '../kernel/prove.ts'

const machine: Machine = {name: 'work-bounded counter', params: [], inputs: [], state: {value: n(0)}, step: {state: {value: plus(x('value'), n(1))}}}
const zero: Law = {name: 'zero', holds: same(x('value'), n(0))}
const state = (value: number): State => ({scalars: {value}, maps: {}})
const samples = [{p: {}, sts: [state(0)]}]

test('work prefixes are deterministic and spend no more than their shared limit', () => {
  for (let limit = 0; limit <= 40; limit++) {
    const results: unknown[] = []
    for (let repeat = 0; repeat < 3; repeat++) {
      let finish: Parameters<NonNullable<FiniteOptions['onFinish']>>[0] | undefined
      const drops: string[] = []
      const survivors = finiteHoudini(machine, machine, [], [zero], samples, {workLimit: limit, wallMs: 0,
        targeted: false, randomStates: 0, requests: 1, onDrop: drop => drops.push(drop.law.name), onFinish: row => { finish = row }})
      expect(finish!.work!.used).toBeLessThanOrEqual(limit)
      expect(finish!.work!.used).toBeGreaterThanOrEqual(0)
      expect(finish!.timedOut).toBe(false)
      expect(survivors).toEqual(limit < 2 ? [zero] : [])
      results.push({survivors, drops, work: finish!.work})
    }
    expect(results[1]).toEqual(results[0])
    expect(results[2]).toEqual(results[0])
  }
})

test('frontiers and rejected neighbors consume the same invocation-wide allowance', () => {
  const impossible: Law = {name: 'impossible', holds: same(n(0), n(1))}
  for (const targeted of [false, true]) {
    let work: {used: number, limit: number, exhausted: boolean} | undefined
    const result = finiteHoudini(machine, machine, [impossible], [zero], samples, {workLimit: 17, targeted, randomStates: 1000,
      onFinish: row => { work = row.work }})
    expect(result).toEqual([zero])
    expect(work).toEqual({used: 17, limit: 17, exhausted: true})
  }
})

test('work exhaustion preserves only fully certified drops and protects callers', () => {
  const unknown: Law = {name: 'unknown', forall: 'k', holds: same({op: 'mul', k: 2, a: x('k')}, x('k'))}
  const options = {workLimit: 20, targeted: false, randomStates: 0, requests: 1}
  expect(finiteHoudini(machine, machine, [zero], [zero], samples, options)).toEqual([zero])
  expect(finiteHoudini(machine, machine, [], [zero, unknown], samples, options)).toEqual([zero, unknown])
  expect(finiteHoudini(machine, machine, [], [zero], [{p: {}, sts: [state(1)]}], options)).toEqual([zero])
})

test('work mode never converts enclosing wall cancellation into a partial family', () => {
  expect(() => withWall(-Infinity, () => finiteHoudini(machine, machine, [], [zero], samples, {workLimit: 0}))).toThrow(WallExpired)
  let dropped = false
  expect(() => finiteHoudini(machine, machine, [], [zero], samples, {workLimit: 20, targeted: false, randomStates: 0, requests: 1,
    onDrop: () => { dropped = true; throw new WallExpired('enclosing cancellation after a certified drop') }})).toThrow(WallExpired)
  expect(dropped).toBe(true)
})

test('invalid work limits are refused instead of silently becoming unbounded', () => {
  for (const workLimit of [-1, NaN, Infinity, 0.5, Number.MAX_SAFE_INTEGER + 1]) {
    expect(() => finiteHoudini(machine, machine, [], [zero], samples, {workLimit})).toThrow('nonnegative safe integer')
  }
})
