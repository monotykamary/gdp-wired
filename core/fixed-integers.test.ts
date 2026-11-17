import {expect, test} from 'bun:test'
import {Term} from './dsl.ts'
import {fixedInt, fixedFailure, fixedSelect, type FixedWord, type FixedWidth, type Overflow} from './fixed-integers.ts'

const value = (w: FixedWord): bigint => {
  const radix = BigInt(w.width === 8 ? 256 : 65536)
  let n = 0n
  for (const limb of [...w.limbs].reverse()) {
    expect(limb.val).toBeDefined()
    n = n * radix + BigInt(limb.val!)
  }
  if (w.signed && n >= 1n << BigInt(w.width - 1)) n -= 1n << BigInt(w.width)
  return n
}
const failure = (w: FixedWord) => fixedFailure(w)?.ok ?? false
const expected = (n: bigint, width: FixedWidth, signed: boolean, mode: Overflow) => {
  const mod = 1n << BigInt(width)
  const lo = signed ? -(mod / 2n) : 0n
  const hi = signed ? mod / 2n - 1n : mod - 1n
  const overflow = n < lo || n > hi
  return {result: mode === 'SATURATE' ? n < lo ? lo : n > hi ? hi : n : ((n % mod + mod) % mod >= (signed ? mod / 2n : mod) ? ((n % mod + mod) % mod) - mod : ((n % mod + mod) % mod)), overflow}
}

test('narrowing to 8 bits checks every discarded higher limb', () => {
  for (const width of [16, 32, 64] as const) {
    const source = fixedInt(width, false)
    for (const n of [256n, 65535n, ...(width > 16 ? [65536n, 4294967295n] : []), ...(width === 64 ? [4294967296n, 18446744073709551615n] : [])]) {
      const x = source.lift(n)
      expect(failure(x.cast(8, false, 'TRAP'))).toBe(true)
      expect(value(x.cast(8, false, 'SATURATE'))).toBe(255n)
      expect(value(x.cast(8, false, 'WRAP'))).toBe(n % 256n)
    }
  }
})

test('encoding is little endian, 64-bit raw values use decimal strings and reject unsafe numbers', () => {
  const u64 = fixedInt(64, false)
  expect(u64.encode('x', '18446744073709551615')).toEqual({'x$0': 65535, 'x$1': 65535, 'x$2': 65535, 'x$3': 65535})
  expect(u64.decode('x', u64.encode('x', '18446744073709551615'))).toBe('18446744073709551615')
  expect(() => u64.encode('x', 1)).toThrow()
  expect(() => u64.encode('x', Number.MAX_SAFE_INTEGER + 1)).toThrow()
  expect(() => fixedInt(8, false).encode('x', -1)).toThrow()
  expect(fixedInt(16, true).decode('x', fixedInt(16, true).encode('x', -32768))).toBe(-32768)
  expect(u64.empty()).toBe('0')
})

test('concrete limb arithmetic agrees with a separate BigInt oracle at edge cases', () => {
  for (const width of [8, 16, 32, 64] as const) for (const signed of [false, true]) {
    const k = fixedInt(width, signed)
    const mod = 1n << BigInt(width)
    const lo = signed ? -mod / 2n : 0n, hi = signed ? mod / 2n - 1n : mod - 1n
    const inputs = [...new Set([lo, lo + 1n, -1n, 0n, 1n, 2n, hi - 1n, hi].filter(x => x >= lo && x <= hi))]
    for (const a of inputs) for (const b of inputs) for (const mode of ['WRAP', 'SATURATE', 'TRAP'] as const) {
      const x = k.lift(a), y = k.lift(b)
      for (const [result, integer] of [[x.plus(y, mode), a + b], [x.minus(y, mode), a - b], [x.mul(y, mode), a * b]] as const) {
        const want = expected(integer, width, signed, mode)
        expect(value(result)).toBe(want.result)
        expect(failure(result)).toBe(mode === 'TRAP' && want.overflow)
      }
      expect(x.lt(y).ok).toBe(a < b)
      expect(x.eq(y).ok).toBe(a === b)
    }
  }
})

test('casts, negation, selected-branch failure, and symbolic division refusal', () => {
  const s16 = fixedInt(16, true), u8 = fixedInt(8, false)
  expect(value(s16.lift(-32768n).negate('WRAP'))).toBe(-32768n)
  expect(failure(s16.lift(-32768n).negate('TRAP'))).toBe(true)
  expect(value(s16.lift(-1n).cast(8, false, 'SATURATE'))).toBe(0n)
  expect(value(s16.lift(256n).cast(8, false, 'WRAP'))).toBe(0n)
  expect(failure(s16.lift(256n).cast(8, false, 'TRAP'))).toBe(true)
  const bad = u8.lift(255n).plus(u8.lift(1n), 'TRAP')
  expect(failure(fixedSelect(u8.lift(0n).eq(u8.lift(1n)), bad, u8.lift(5n)))).toBe(false)
  expect(failure(fixedSelect(u8.lift(1n).eq(u8.lift(1n)), bad, u8.lift(5n)))).toBe(true)
  const symbolic = u8.build('x', name => new Term({op: 'var', name}))
  expect(() => symbolic.div(u8.lift(2n), 'TRUNCATING', 'TRAP')).toThrow('symbolic fixed integer division')
})

test('high limb dominates low limb in unsigned and same-sign signed comparisons', () => {
  for (const signed of [false, true]) {
    const k = fixedInt(32, signed)
    expect(k.decode('left', {'left$0': 0, 'left$1': 1})).toBe(65536)
    expect(k.decode('right', {'right$0': 65535, 'right$1': 0})).toBe(65535)
    const lowGreater = k.lift(0x00010000n), lowSmaller = k.lift(0x0000ffffn)
    expect(lowGreater.lt(lowSmaller).ok).toBe(false)
    expect(lowSmaller.lt(lowGreater).ok).toBe(true)
    const highGreater = k.lift(0x00020000n), highSmaller = k.lift(0x0001ffffn)
    expect(highGreater.lt(highSmaller).ok).toBe(false)
    expect(highSmaller.lt(highGreater).ok).toBe(true)
  }
  const k64 = fixedInt(64, false)
  expect(k64.lift(0x1000000000000n).lt(k64.lift(0xffffffffffffn)).ok).toBe(false)
})

test('unsigned saturation borrows to zero and inherited failures cannot silently become predicates', () => {
  for (const width of [8, 16, 32, 64] as const) {
    const k = fixedInt(width, false), zero = k.lift(0n), one = k.lift(1n)
    expect(value(zero.minus(one, 'SATURATE'))).toBe(0n)
    expect(value(one.minus(zero, 'SATURATE'))).toBe(1n)
    const failed = zero.minus(one, 'TRAP')
    expect(() => failed.eq(zero)).toThrow('failure')
    expect(() => zero.lt(failed)).toThrow('failure')
    expect(() => failed.ne(zero)).toThrow('failure')
    expect(() => failed.atLeast(zero)).toThrow('failure')
    const symbolic = k.build('x', name => new Term({op: 'var', name}))
    expect(() => symbolic.plus(one, 'TRAP').eq(zero)).toThrow('failure')
    expect(() => zero.eq(symbolic.plus(one, 'TRAP'))).toThrow('failure')
    expect(() => zero.eq(one.minus(zero, 'TRAP'))).not.toThrow()
  }
})

test('store preserves word failure on fresh limb wrappers without contaminating shared terms', () => {
  const k = fixedInt(32, false), untrapped = k.lift(0n)
  const trapped = untrapped.minus(k.lift(1n), 'TRAP')
  const stored = k.store('x', trapped)
  for (const [index, limb] of Object.values(stored).entries()) {
    expect(limb).not.toBe(trapped.limbs[index])
    expect((limb as Term).e).toBe(trapped.limbs[index]!.e)
    expect(fixedFailure(limb)?.ok).toBe(true)
  }
  expect(fixedFailure(trapped.limbs[0])).toBeUndefined()
  expect(fixedFailure(untrapped.limbs[0])).toBeUndefined()
  for (const limb of Object.values(k.store('y', untrapped))) expect(fixedFailure(limb)).toBeUndefined()
  const symbolic = k.build('z', name => new Term({op: 'var', name}))
  const symbolicStored = k.store('s', symbolic.minus(k.lift(1n), 'TRAP'))
  for (const limb of Object.values(symbolicStored)) expect(fixedFailure(limb)).toBeDefined()
})

test('runtime kinds and modes are checked rather than falling through to wrap', () => {
  expect(() => fixedInt(24 as FixedWidth, false)).toThrow(RangeError)
  expect(() => fixedInt(8, 'yes' as unknown as boolean)).toThrow(TypeError)
  const k = fixedInt(8, true), a = k.lift(2n), b = k.lift(1n)
  for (const op of [() => a.plus(b, 'BOGUS' as Overflow), () => a.minus(b, 'BOGUS' as Overflow),
    () => a.mul(b, 'BOGUS' as Overflow), () => a.negate('BOGUS' as Overflow),
    () => a.cast(16, true, 'BOGUS' as Overflow), () => a.div(b, 'TRUNCATING', 'BOGUS' as Overflow),
    () => a.rem(b, 'TRUNCATING', 'BOGUS' as Overflow)]) expect(op).toThrow(RangeError)
  expect(() => a.cast(8, 'yes' as unknown as boolean, 'WRAP')).toThrow(TypeError)
  expect(() => a.div(b, 'CEILING' as never, 'WRAP')).toThrow(RangeError)
})

test('signed 8-bit sampling remains encodable even at large bounds', () => {
  const k = fixedInt(8, true)
  for (const bound of [0, 1, 127, 128, 255, 1e9]) {
    const raw = k.sample(n => n - 1, bound)
    expect(raw).toBeGreaterThanOrEqual(-128)
    expect(raw).toBeLessThanOrEqual(127)
    expect(() => k.encode('x', raw)).not.toThrow()
  }
})

test('division modes and division-pair failures include remainder on MIN / -1', () => {
  const k = fixedInt(8, true), x = k.lift(-7n), y = k.lift(3n)
  expect(value(x.div(y, 'TRUNCATING', 'WRAP'))).toBe(-2n)
  expect(value(x.rem(y, 'TRUNCATING', 'WRAP'))).toBe(-1n)
  expect(value(x.div(y, 'FLOOR', 'WRAP'))).toBe(-3n)
  expect(value(x.rem(y, 'FLOOR', 'WRAP'))).toBe(2n)
  expect(value(x.div(y, 'EUCLIDEAN', 'WRAP'))).toBe(-3n)
  expect(value(x.rem(y, 'EUCLIDEAN', 'WRAP'))).toBe(2n)
  expect(failure(k.lift(-128n).rem(k.lift(-1n), 'TRUNCATING', 'TRAP'))).toBe(true)
  expect(value(k.lift(-128n).rem(k.lift(-1n), 'TRUNCATING', 'SATURATE'))).toBe(0n)
  expect(failure(k.lift(3n).div(k.lift(0n), 'FLOOR', 'WRAP'))).toBe(true)
})
