import {expect, test} from 'bun:test'
import {type Machine, get, n, same, x} from '../../core/machine.ts'
import {symbolicStutter} from './t14-stutter.ts'
const m: Machine = {name: 'conditional write', params: [], inputs: ['action'], state: {phase: n(0)}, maps: {Cell: 0}, step: {flags: {go: same(x('action'), n(1))}, state: {phase: {op: 'if', c: {op: 'flag', name: 'go'}, then: n(2), else: x('phase')}}, maps: {Cell: {each: 'key', value: {op: 'if', c: {op: 'flag', name: 'go'}, then: n(7), else: get('Cell', x('key'))}}}}}
test('disabled updates are identities for every completion of unread cells', () => expect(symbolicStutter(m, {action: 0}).unchanged).toBe(true))
test('an active or unresolved write is not certified as an identity', () => {
  expect(symbolicStutter(m, {action: 1}).unchanged).toBe(false)
  expect(symbolicStutter(m, {}).unchanged).toBe(false)
})
test('model flag columns cannot override a flag definition', () => expect(symbolicStutter(m, {action: 1, '?go': 0}).unchanged).toBe(false))
test('a map binder shadows identically named scalar inputs', () => {
  const shadow: Machine = {...m, step: {maps: {Cell: {each: 'action', value: x('action')}}}}
  expect(symbolicStutter(shadow, {action: 0}).unchanged).toBe(false)
})
test('history effects are not covered by this algebraic check', () => {
  const history: Machine = {...m, history: {keep: {op: 'and', xs: []}, record: [], sums: {}, queries: {}}}
  expect(symbolicStutter(history, {action: 0}).unchanged).toBe(false)
})
