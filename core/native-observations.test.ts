import {expect, test} from 'bun:test'
import {parse} from './laws.ts'
import {nativeLaw} from './native-law.ts'
import {nativeObservationSequence, validateNativeObservations, type NativeReading} from './native-observations.ts'
import type {NativeObservation} from './source-check.ts'

const readings: NativeReading[] = [
  {code: 'Quota.ttl', key: 'Quota.ttl', kind: 'answer'},
  {code: 'Quota.ttl.raises', key: 'Quota.ttl', kind: 'raises'},
  {code: 'now', key: 'now', kind: 'clock'},
]
const observation = (): NativeObservation => ({where: 'actual-observation control', method: 'grant', before: {expires: 0}, after: {expires: 16}, params: {}, inputs: {ttl: 999, now: 999}, bindings: {}, args: [], result: undefined, failed: false,
  observed: {invocation: 1, calls: {'Quota.ttl': {kind: 'returned', value: 6}}, clock: 10}})
const evaluate = (text: string, row = observation(), bindings = readings) => nativeLaw(parse(text), {}, parse, {}, new Set(['Quota', 'now', 'expires']), bindings)(row)

test('observed answers and clock reads are independent of requested inputs', () => {
  const text = 'old(expires) <= now implies expires == Quota.ttl(...) + now'
  expect(evaluate(text)).toBe(true)
  expect(evaluate(text, {...observation(), after: {expires: 1998}})).toBe(false)
  const missing = observation(); missing.observed = undefined
  expect(() => evaluate(text, missing)).toThrow('unobserved native clock')
  const noAnswer = observation(); noAnswer.observed!.calls = {}
  expect(() => evaluate(text, noAnswer)).toThrow('unobserved native call')
  noAnswer.before = {expires: 20}
  expect(evaluate(text, noAnswer)).toBe(true) // source guard did not call the answer
})
test('actual raised outcomes have their own explicit reading, never a fabricated returned value', () => {
  const row = observation(); row.observed!.calls['Quota.ttl'] = {kind: 'raised', raised: 'QuotaError'}
  expect(evaluate('Quota.ttl.raises == "QuotaError"', row)).toBe(true)
  expect(() => evaluate('Quota.ttl(...) == 6', row)).toThrow('raised instead of returning')
  expect(evaluate('Quota.ttl.raises is null')).toBe(true)
  const absent = observation(); absent.observed!.calls = {}
  expect(() => evaluate('Quota.ttl.raises is null', absent)).toThrow('unobserved native call')
})
test('native readings remain method-scoped and cannot rename another call into the expression', () => {
  expect(() => evaluate('Quota.ttl(...) == 6', observation(), [{code: 'Quota.ttl', key: 'Other.ttl', kind: 'answer'}])).toThrow('original call')
  expect(() => evaluate('Quota.ttl(...) == 6', observation(), [{code: 'Quota.ttl', key: 'Quota.ttl', kind: 'answer', method: 'other'}])).toThrow()
  expect(() => evaluate('ttl(...) == 6', observation(), [...readings, {code: 'Other.ttl', key: 'Other.ttl', kind: 'answer'}])).toThrow('ambiguous')
})
test('the native observation sequence rejects stale, undeclared and inexact values', () => {
  const accept = nativeObservationSequence(new Set(['Quota.ttl']))
  expect(accept(observation().observed).invocation).toBe(1)
  expect(() => accept(observation().observed)).toThrow('stale or repeated')
  const second = {...observation().observed!, invocation: 2, calls: {}}
  expect(accept(second).calls).toEqual({})
  expect(() => validateNativeObservations({invocation: 3, calls: {'Wrong.ttl': {kind: 'returned', value: 6}}}, new Set(['Quota.ttl']))).toThrow('unbound call')
  for (const value of [NaN, Infinity, 0.5, Number.MAX_SAFE_INTEGER + 1]) {
    expect(() => validateNativeObservations({invocation: 3, calls: {}, clock: value}, new Set())).toThrow('exact integer')
    expect(() => validateNativeObservations({invocation: 3, calls: {'Quota.ttl': {kind: 'returned', value}}}, new Set(['Quota.ttl']))).toThrow('exact integer')
  }
})
test('foreign structural equality is refused instead of evaluated as JS identity', () => {
  const row = {...observation(), nativeEquality: 'scalar' as const, after: {a: {}, b: {}, n: 1}}
  expect(() => evaluate('a != b', row)).toThrow('foreign container equality')
  expect(evaluate('n == 1', row)).toBe(true)
})
