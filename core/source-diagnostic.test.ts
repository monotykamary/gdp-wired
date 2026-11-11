import {expect, test} from 'bun:test'
import {sourceDiagnostic} from './source-diagnostic.ts'

test('native diagnostics retain absence, NaN, maps and cycles without invoking accessors', () => {
  let calls = 0
  const value: Record<string, unknown> = {missing: undefined, number: NaN, map: new Map([['a', undefined]])}
  Object.defineProperty(value, 'getter', {get() { calls++; return 1 }, enumerable: true})
  value.self = value
  expect(sourceDiagnostic(value)).toEqual({missing: {$undefined: true}, number: {$number: 'NaN'}, map: {$map: [['a', {$undefined: true}]]}, getter: {$accessor: true}, self: {$circular: true}})
  expect(calls).toBe(0)
  expect(() => JSON.stringify(sourceDiagnostic(value))).not.toThrow()
})
