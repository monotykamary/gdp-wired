import {expect, test} from 'bun:test'
import {traceError} from './trace-error.ts'
test('trace error text preserves real errors and stays bounded', () => {
  expect(traceError(new TypeError('bad input'))).toBe('TypeError: bad input')
  expect(traceError('x'.repeat(300))).toHaveLength(200)
  expect(traceError(null)).toBe('null')
  expect(traceError(7)).toBe('7')
  expect(traceError(undefined)).toBe('undefined')
})
test('trace errors never stringify or traverse arbitrary objects', () => {
  const value = {self: undefined as unknown, toString() {throw Error('must not run')}, toJSON() {throw Error('must not run')}}
  value.self = value
  expect(traceError(value)).toBe('<non-Error object>')
  expect(traceError(() => {})).toBe('<non-Error object>')
})
