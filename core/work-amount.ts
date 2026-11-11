// Exact work arithmetic. Numbers enter by their IEEE value, not decimal text.
// Clock displays are never decoded again to construct an authoritative root.
import {type Rat, Q0, bgcd, q, qadd, qcmp, qdiv, qmul, qsub} from './q.ts'
export type WorkAmount = Readonly<Rat>
export type ExactRaw = Readonly<{numerator: string, denominator: string}>
export const zeroWork: WorkAmount = Object.freeze(Q0)
export function workAmount(num: bigint, den = 1n): WorkAmount { return Object.freeze(q(num, den)) }
export function workFromNumber(value: number): WorkAmount {
  if (!Number.isFinite(value)) throw new RangeError('work amount must be finite')
  if (value === 0) return zeroWork
  const bits = new DataView(new ArrayBuffer(8))
  bits.setFloat64(0, value, false)
  const hi = bits.getUint32(0, false), lo = bits.getUint32(4, false)
  const exponent = (hi >>> 20) & 0x7ff
  let mantissa = (BigInt(hi & 0xfffff) << 32n) | BigInt(lo)
  if (exponent) mantissa |= 1n << 52n
  if (hi >>> 31) mantissa = -mantissa
  const shift = exponent ? exponent - 1075 : -1074
  return shift >= 0 ? workAmount(mantissa << BigInt(shift)) : workAmount(mantissa, 1n << BigInt(-shift))
}
export function workAdd(a: WorkAmount, b: WorkAmount): WorkAmount { return Object.freeze(qadd(a, b)) }
export function workSub(a: WorkAmount, b: WorkAmount): WorkAmount { return Object.freeze(qsub(a, b)) }
export function workMultiply(a: WorkAmount, b: WorkAmount): WorkAmount { return Object.freeze(qmul(a, b)) }
export function workShare(a: WorkAmount, numerator: bigint, denominator: bigint): WorkAmount {
  if (numerator < 0n || denominator <= 0n) throw new RangeError('work share requires a nonnegative numerator and positive denominator')
  return Object.freeze(qmul(a, q(numerator, denominator)))
}
export function workDivide(a: WorkAmount, b: WorkAmount): WorkAmount {
  if (b.num <= 0n) throw new RangeError('work divisor must be positive')
  return Object.freeze(qdiv(a, b))
}
export const compareWork = (a: WorkAmount, b: WorkAmount): number => qcmp(a, b)
export const minWork = (a: WorkAmount, b: WorkAmount): WorkAmount => compareWork(a, b) <= 0 ? a : b
export function exactRaw(a: WorkAmount): ExactRaw { return Object.freeze({numerator: String(a.num), denominator: String(a.den)}) }
export function workFromExact(a: ExactRaw): WorkAmount {
  const n = BigInt(a.numerator), d = BigInt(a.denominator)
  if (d <= 0n) throw new RangeError('work denominator must be positive')
  return workAmount(n, d)
}
export function integerQuotient(a: WorkAmount, b: WorkAmount): bigint {
  if (a.num < 0n || b.num <= 0n) throw new RangeError('work quotient requires nonnegative work and a positive quantum')
  return (a.num * b.den) / (a.den * b.num)
}
// Correct round-to-nearest/even conversion for TELEMETRY only, including
// subnormals and values whose numerator or denominator does not fit a Number.
export function workToNumber(a: WorkAmount): number {
  if (a.num === 0n) return 0
  const negative = a.num < 0n, n = negative ? -a.num : a.num, d = a.den
  if (d <= 0n) throw new RangeError('work denominator must be positive')
  let exponent = n.toString(2).length - d.toString(2).length
  if (exponent >= 0 ? n < (d << BigInt(exponent)) : (n << BigInt(-exponent)) < d) exponent--
  if (exponent > 1023) return negative ? -Infinity : Infinity
  const shift = exponent < -1022 ? 1074 : 52 - exponent
  const dividend = shift >= 0 ? n << BigInt(shift) : n
  const divisor = shift >= 0 ? d : d << BigInt(-shift)
  let rounded = dividend / divisor
  const remainder = dividend % divisor, twice = remainder * 2n
  if (twice > divisor || twice === divisor && (rounded & 1n) !== 0n) rounded++
  const value = exponent < -1022 ? Number(rounded) * Number.MIN_VALUE : Number(rounded) * 2 ** (exponent - 52)
  return negative ? -value : value
}
// The ledger uses an integer lattice for its frozen dyadic coefficients. Exact
// rational endpoints (including thirds) are compared without rounding to it.
export function commonWorkDenominator(values: readonly WorkAmount[]): bigint {
  let denominator = 1n
  for (const value of values) denominator = denominator / bgcd(denominator, value.den) * value.den
  return denominator
}
