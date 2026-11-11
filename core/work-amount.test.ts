import {expect, test} from 'bun:test'
import {compareWork, exactRaw, integerQuotient, workAdd, workAmount, workFromExact, workFromNumber, workShare, workToNumber} from './work-amount.ts'

test('work decodes the supplied binary value, not shortest decimal text', () => {
  expect(exactRaw(workFromNumber(0.1))).toEqual({numerator: '3602879701896397', denominator: '36028797018963968'})
  expect(compareWork(workFromNumber(0.1), workAmount(1n, 10n))).toBe(1)
  expect(exactRaw(workFromNumber(-0))).toEqual({numerator: '0', denominator: '1'})
})
test('every representative finite IEEE value round trips, including subnormals', () => {
  for (const value of [0, 1, -1, 0.02, 2.33, 0.0123, 2500000000, Number.MIN_VALUE, -Number.MIN_VALUE, 2 ** -1022, Number.MAX_VALUE, Number.MAX_SAFE_INTEGER]) {
    expect(workToNumber(workFromNumber(value))).toBe(value)
  }
  expect(() => workFromNumber(Infinity)).toThrow(RangeError)
  expect(() => workFromNumber(NaN)).toThrow(RangeError)
})
test('shares and discrete grants are exact at fractional boundaries', () => {
  const third = workShare(workAmount(10n), 1n, 3n)
  expect(exactRaw(third)).toEqual({numerator: '10', denominator: '3'})
  expect(integerQuotient(third, workAmount(1n))).toBe(3n)
  expect(integerQuotient(workAmount(9n, 10n), workAmount(1n))).toBe(0n)
  expect(compareWork(workAdd(third, third), workAmount(20n, 3n))).toBe(0)
  expect(() => workShare(third, 1n, 0n)).toThrow(RangeError)
  expect(() => workFromExact({numerator: '1', denominator: '-1'})).toThrow(RangeError)
})
test('telemetry rounds ties to even and cannot grant work', () => {
  const one = 1n << 53n
  expect(workToNumber(workAmount(one + 1n, one))).toBe(1)
  expect(workToNumber(workAmount(one + 3n, one))).toBe(1 + 2 ** -51)
  const halfSubnormal = workAmount(1n, 1n << 1075n)
  expect(workToNumber(halfSubnormal)).toBe(0)
  expect(integerQuotient(halfSubnormal, workFromNumber(Number.MIN_VALUE))).toBe(0n)
})
