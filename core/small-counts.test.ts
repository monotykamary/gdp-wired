import {expect, test} from 'bun:test'
import {smallOf, holdsAt} from './exists.ts'
import {type Machine, get, n, same, x} from './machine.ts'
const machine = (): Machine => ({name: 'sample counts', params: [], inputs: [], state: {}, maps: {M: 0}, step: {}})
test('fresh unused counts reuse exactly the original sampled graph', () => {
  const source = machine(), m: Machine = {...source, counts: {fresh: {j: 'j', key: 'k', below: n(2), body: n(1)}}}
  expect(smallOf(m, source)).toBe(smallOf(source))
  const st = smallOf(source)[0]!.sts[0]!
  expect(holdsAt(source, {name: 'base', holds: same(get('M', x('k')), n(0)), forall: 'k'}, {}, st, 2)).toBe(true)
  expect(holdsAt(m, {name: 'added count', holds: same(get('fresh', x('k')), n(2)), forall: 'k'}, {}, st, 2)).toBe(true)
})
test('changed steps, changed definitions and shadowed reads are sampled independently', () => {
  const source = machine(), body = {j: 'j', key: 'k', below: n(2), body: n(1)}
  const changed: Machine = {...source, step: {maps: {M: {key: n(0), value: n(1)}}}, counts: {fresh: body}}
  expect(smallOf(changed, source)).not.toBe(smallOf(source))
  const shadow: Machine = {...source, counts: {M: body}}
  // A fresh count sharing an existing map name is not a fresh definition.
  expect(smallOf(shadow, source)).not.toBe(smallOf(source))
  const counted: Machine = {...source, counts: {fresh: body}}, replaced: Machine = {...counted, counts: {fresh: {...body, body: n(0)}}}
  expect(smallOf(replaced, counted)).not.toBe(smallOf(counted))
})
