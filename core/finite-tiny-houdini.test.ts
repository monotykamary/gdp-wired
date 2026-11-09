import {expect, test} from 'bun:test'
import {type Law, type Machine, atMost, n, plus, same, x} from './machine.ts'
import {finiteTinyHoudini, type FiniteDrop} from './finite-houdini.ts'
import {withWall} from '../kernel/prove.ts'
import {WallExpired} from './wall.ts'
const counter = (): Machine => ({name: 'anonymous', params: [], inputs: [], state: {value: n(0)}, counts: {unused: {j: 'row', key: 'k', below: n(1), body: n(0)}}, step: {state: {value: plus(x('value'), n(1))}}})
const zero: Law = {name: 'zero', holds: same(x('value'), n(0))}
test('tiny Houdini certifies drops independently and never drops a caller', () => {
  expect(finiteTinyHoudini(counter(), counter(), [], [zero], [{}])).toEqual([])
  expect(finiteTinyHoudini(counter(), counter(), [zero], [zero], [{}])).toEqual([zero])
})
test('tiny Houdini repeats under the surviving family after certified drops', () => {
  const source: Machine = {...counter(), name: 'cascade', state: {value: n(0), other: n(0)}, step: {state: {value: plus(x('value'), n(1)), other: x('value')}}}
  const a: Law = {name: 'a', holds: same(x('value'), n(0))}, b: Law = {name: 'b', holds: same(x('other'), n(0))}, drops: FiniteDrop[] = []
  expect(finiteTinyHoudini(source, source, [], [a, b], [{}], {onDrop: d => drops.push(d)})).toEqual([])
  expect(drops.map(d => [d.round, d.law.name])).toEqual([[0, 'a'], [1, 'b']])
})
test('tiny Houdini checks declared facts and parameter preconditions', () => {
  const source: Machine = {...counter(), params: ['p']}
  const fact: Law = {name: 'p zero', holds: same(x('p'), n(0))}
  const m = {...source, facts: [fact]}
  expect(finiteTinyHoudini(source, m, [], [zero], [{p: 1}])).toEqual([zero])
  expect(finiteTinyHoudini(source, m, [], [zero], [{p: 0}])).toEqual([])
  expect(finiteTinyHoudini(source, {...source, pre: fact.holds}, [], [zero], [{p: 1}])).toEqual([zero])
})
test('unsupported declarations cannot authorize tiny Houdini drops', () => {
  const source = counter(), unsupported: Law = {name: 'unsupported', holds: {op: 'all', key: 'k', c: same(n(0), n(0))}}
  expect(finiteTinyHoudini(source, {...source, facts: [unsupported]}, [], [zero], [{}])).toEqual([zero])
  expect(finiteTinyHoudini(source, {...source, sums: {derived: {key: 'k', term: n(0)}}}, [], [zero], [{}])).toEqual([zero])
})
test('tiny Houdini preserves survivors on its own timeout and propagates an outer wall', () => {
  let timedOut = false
  expect(finiteTinyHoudini(counter(), counter(), [], [zero], [{}], {wallMs: 0, onFinish: r => { timedOut = r.timedOut }})).toEqual([zero])
  expect(timedOut).toBe(true)
  expect(() => withWall(performance.now() - 1, () => finiteTinyHoudini(counter(), counter(), [], [zero], [{}]))).toThrow(WallExpired)
})
test('an explicit round cap retains untested later-round helpers', () => {
  const source = counter(), one: Law = {name: 'at most one', holds: atMost(x('value'), n(1))}
  expect(finiteTinyHoudini(source, source, [], [zero, one], [{}], {rounds: 1})).toEqual([one])
  expect(finiteTinyHoudini(source, source, [], [zero, one], [{}], {rounds: 2})).toEqual([])
})
test('an explicit richer state domain can expose a new real violation', () => {
  const source = counter(), bound: Law = {name: 'at most two', holds: atMost(x('value'), n(2))}
  expect(finiteTinyHoudini(source, source, [], [bound], [{}])).toEqual([bound])
  expect(finiteTinyHoudini(source, source, [], [bound], [{}], {valueDomain: [0, 1, 2]})).toEqual([])
  expect(finiteTinyHoudini(source, source, [], [bound], [{}], {valueDomain: [NaN]})).toEqual([bound])
})
test('an unsupported count grid retains every candidate', () => {
  const source = {...counter(), counts: undefined}
  expect(finiteTinyHoudini(source, source, [], [zero], [{}])).toEqual([zero])
})
test('tiny Houdini does not confuse a true natural bound with a witnessed violation', () => {
  const source = counter(), law: Law = {name: 'natural', holds: atMost(n(0), x('value'))}
  expect(finiteTinyHoudini(source, source, [], [law], [{}])).toEqual([law])
})
