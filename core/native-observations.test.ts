import {expect, test} from 'bun:test'
import {parse} from './laws.ts'
import {sandbox} from './extract-check.ts'
import {nativeLaw} from './native-law.ts'
import {nativeObservationSequence, validateNativeObservations, type NativeReading} from './native-observations.ts'
import type {NativeObservation} from './source-check.ts'
import type {Name} from './extract.ts'

const readings: NativeReading[] = [
  {code: 'Quota.ttl', key: 'Quota.ttl', kind: 'answer'},
  {code: 'Quota.ttl.raises', key: 'Quota.ttl', kind: 'raises'},
  {code: 'now', key: 'now', kind: 'clock'},
]
const observation = (): NativeObservation => ({where: 'actual-observation control', method: 'grant', before: {expires: 0}, after: {expires: 16}, params: {}, inputs: {ttl: 999, now: 999}, bindings: {}, args: [], result: undefined, failed: false,
  observed: {invocation: 1, calls: {'Quota.ttl': {kind: 'returned', value: 6}}, clock: 10}})
const evaluate = (text: string, row = observation(), bindings = readings) => nativeLaw(parse(text), {}, parse, {}, new Set(['Quota', 'now', 'expires']), bindings)(row)

test('declared source names take precedence over native pseudo values', () => {
  const names: Name[] = [{code: 'failed', rule: 'failed', role: 'state'}, {code: 'refunded', rule: 'refunded', role: 'state'}]
  const row: NativeObservation = {...observation(), before: {failed: 1, refunded: 1}, after: {failed: 0, refunded: 0}, failed: false}
  const check = (text: string, o = row, ns = names) => nativeLaw(parse(text), {}, parse, {}, new Set(), [], ns)(o)
  expect(check('refunded == failed')).toBe(true)
  expect(check('refunded != failed')).toBe(false)
  expect(check('old(failed) == 1 and failed == 0')).toBe(true)
  expect(() => check('failed == 0', {...row, after: {refunded: 0}})).toThrow('unavailable')
  const input: Name[] = [...names, {code: 'failed', rule: 'arg', role: 'input', method: 'grant'}]
  expect(check('failed == 3', {...row, bindings: {failed: 3}}, input)).toBe(true)
  expect(check('failed == 2', {...row, bindings: {failed: 3}}, input)).toBe(false)
  expect(() => check('failed == 3', {...row, bindings: {}, inputs: {failed: 3}}, input)).toThrow('unavailable')
  const param: Name[] = [{code: 'result', rule: 'p', role: 'param'}]
  expect(check('result == 4', {...row, params: {result: 4}, result: 9}, param)).toBe(true)
  expect(() => check('result == 9', {...row, params: {}, result: 9}, param)).toThrow('unavailable')
  const members: Name[] = [...param, {code: 'result.value', rule: 'v', role: 'result', method: 'grant'}]
  expect(check('result.value == 8', {...row, params: {result: {value: 4}}, result: {value: 8}}, members)).toBe(true)
  expect(check('result.value == 4', {...row, params: {result: {value: 4}}, result: {value: 8}}, members)).toBe(false)
  expect(() => check('result.value == 4', {...row, params: {result: {value: 4}}, result: {}}, members)).toThrow('unavailable')
  const pseudo: Name[] = [{code: 'failed', rule: 'f', role: 'failed'}, {code: 'result', rule: 'r', role: 'result'}]
  expect(check('failed == false and result == 9', {...row, bindings: {failed: true, result: 4}, result: 9}, pseudo)).toBe(true)
  expect(check('failed == true', {...row, bindings: {failed: true}}, pseudo)).toBe(false)
})
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
test('the JS sandbox records only actual per-invocation clock reads', () => {
  const box = sandbox('export function readClock() { return Date.now() } export function dated() { return new Date().getTime() } export function quiet() { return 0 } export function $get() { return Date.now() }', 'clock.ts', ['readClock', 'dated', 'quiet', '$get'])
  box.setNow(12)
  expect(box.call('readClock', undefined, [])).toEqual({ok: true, value: 12})
  const first = box.observations()
  expect(first.clock).toBe(12)
  box.setNow(999)
  expect(box.call('$get', undefined, [], true)).toEqual({ok: true, value: 999})
  expect(box.observations()).toEqual(first) // harness inspection is not a new source read
  expect(box.call('$get', undefined, [])).toEqual({ok: true, value: 999})
  expect(box.observations().clock).toBe(999) // a user function with that name is still source code
  expect(box.call('quiet', undefined, [])).toEqual({ok: true, value: 0})
  const second = box.observations()
  expect(second.invocation).toBeGreaterThan(first.invocation)
  expect(second.clock).toBeUndefined() // setting/requesting a clock did not observe it
  box.setNow(23)
  expect(box.call('dated', undefined, [])).toEqual({ok: true, value: 23})
  expect(box.observations().clock).toBe(23)
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
test('constant-argument answers require the exact executed key, never another stub or a requested answer', () => {
  const bindings: NativeReading[] = ['check', 'check_x_1', 'check_x_2'].map(key => ({code: key, key, kind: 'answer'}))
  const row = {...observation(), inputs: {check_x_1: true}, observed: {invocation: 1, calls: {
    check: {kind: 'returned' as const, value: true}, check_x_2: {kind: 'returned' as const, value: false},
  }}}
  const check = (text: string) => nativeLaw(parse(text), {}, parse, {LEFT: 1, RIGHT: 2}, new Set(), bindings)(row)
  expect(check('check(input, RIGHT) == false')).toBe(true)
  expect(() => check('check(input, LEFT) == true')).toThrow('unobserved native call check_x_1')
  expect(() => check('check(input, 3) == true')).toThrow('specific arguments')
})

test('external suffix aliases do not shadow reserved results, constants or the primary method', () => {
  const aliases: NativeReading[] = ['result', 'failed', 'method', 'limit', 'grant'].map(name => ({code: `Provider.${name}`, key: `Provider.${name}`, kind: 'answer'}))
  const row: NativeObservation = {...observation(), result: 41, failed: true, observed: {invocation: 1, calls: {
    'Provider.result': {kind: 'returned', value: -1}, 'Provider.failed': {kind: 'returned', value: false},
    'Provider.method': {kind: 'returned', value: 'other'}, 'Provider.limit': {kind: 'returned', value: 0},
    'Provider.grant': {kind: 'returned', value: 0},
  }}}
  const check = (text: string) => nativeLaw(parse(text), {}, parse, {limit: 7}, new Set(), aliases)(row)
  expect(check('result == 41 and failed == true and method == "grant" and limit == 7')).toBe(true)
  expect(check('grant(...) == 41')).toBe(true)
  expect(check('Provider.result(...) == -1 and Provider.failed(...) == false and Provider.method(...) == "other" and Provider.limit(...) == 0 and Provider.grant(...) == 0')).toBe(true)
})
test('quantified binders retain lexical priority over external aliases and the clock', () => {
  const row = {...observation(), after: {ids: new Set([3, 7])}}
  for (const name of ['ttl', 'now']) expect(evaluate(`forall ${name} in ids: ${name} != 6 and ${name} < 8`, row)).toBe(true)
  expect(evaluate('Quota.ttl(...) == 6 and now == 10', row)).toBe(true)
})
test('the native observation sequence rejects stale, undeclared and inexact values', () => {
  const accept = nativeObservationSequence(new Set(['Quota.ttl']))
  expect(accept(observation().observed).invocation).toBe(1)
  expect(() => accept(observation().observed)).toThrow('stale or repeated')
  expect(() => validateNativeObservations({...observation().observed, error: 'conflicting actual reads'}, new Set(['Quota.ttl']))).toThrow('native observation unavailable')
  for (const error of [false, 0, {}, []])
    expect(() => validateNativeObservations({...observation().observed, error}, new Set(['Quota.ttl']))).toThrow('invalid non-string error payload')
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
  expect(() => evaluate('a == b', {...row, after: {a: new Set([1]), b: new Set([1])}})).toThrow('foreign container equality')
  expect(evaluate('n == 1', row)).toBe(true)
  expect(evaluate('a != nil and nil != b', row)).toBe(true)
  expect(evaluate('a == nil or nil == b', row)).toBe(false)
  expect(evaluate('empty == nil and nil == empty', {...row, after: {...row.after as object, empty: null}})).toBe(true)
})
