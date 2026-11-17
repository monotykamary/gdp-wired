import {expect, test} from 'bun:test'
import {FixedWord, fixedInt, type FixedWidth, type DivisionRounding} from './fixed-integers.ts'
import {captureFixed, divideFixed} from './fixed-division.ts'
import {Cond} from './dsl.ts'

const value = (limbs: readonly {val?: number}[], width: FixedWidth, signed: boolean) => {
  const base = width === 8 ? 256n : 65536n
  let result = 0n
  for (let i = limbs.length - 1; i >= 0; i--) result = result * base + BigInt(limbs[i]!.val!)
  return signed && result >= 1n << BigInt(width - 1) ? result - (1n << BigInt(width)) : result
}
function expected(a: bigint, b: bigint, rounding: DivisionRounding): [bigint, bigint] {
  let q = a / b, r = a % b
  if (r && rounding === 'FLOOR' && (a < 0n) !== (b < 0n)) { q--; r += b }
  if (r < 0n && rounding === 'EUCLIDEAN') { q += b < 0n ? 1n : -1n; r += b < 0n ? -b : b }
  return [q, r]
}
for (const width of [8, 16, 32, 64] as const) for (const signed of [false, true]) {
  test(`capture fixed division ` + width + (signed ? ' signed' : ' unsigned'), () => {
    const kind = fixedInt(width, signed)
    const max = (1n << BigInt(width - (signed ? 1 : 0))) - 1n
    const min = signed ? -(1n << BigInt(width - 1)) : 0n
    const inputs: [bigint, bigint][] = signed
      ? width === 64 ? [[-13n, 5n], [min, -1n], [13n, -5n]] : [[-13n, 5n], [-13n, -5n], [13n, -5n], [min, -1n], [min, 1n], [max, 2n], [0n, -1n]]
      : width === 64 ? [[max, 3n], [13n, 5n]] : [[max, 1n], [max, max], [max, 3n], [0n, 1n], [13n, 5n]]
    for (const [av, bv] of inputs) for (const rounding of ['TRUNCATING', 'FLOOR', 'EUCLIDEAN'] as const)
      for (const mode of ['WRAP', 'SATURATE', 'TRAP'] as const) {
        const a = kind.lift(av), b = kind.lift(bv)
        const {value: [q, r], flags} = captureFixed(() => [divideFixed(a, b, rounding, mode, false), divideFixed(a, b, rounding, mode, true)])
        expect(Object.keys(flags)).toHaveLength(0)
        const overflow = signed && av === min && bv === -1n
        const [eq, er] = overflow ? [mode === 'SATURATE' ? max : min, 0n] : expected(av, bv, rounding)
        expect(value(q.limbs, width, signed)).toBe(eq)
        expect(value(r.limbs, width, signed)).toBe(er)
        expect(q.failure?.ok).toBe(overflow && mode === 'TRAP')
        expect(r.failure?.ok).toBe(overflow && mode === 'TRAP')
      }
  }, 120_000)
}
test('division captures need no flags and scopes restore on throws', () => {
  const u8 = fixedInt(8, false)
  const a = u8.lift(100), b = u8.lift(7)
  const {value, flags} = captureFixed(() => divideFixed(a, b, 'TRUNCATING', 'WRAP', false))
  expect(value.limbs[0]!.val).toBe(14)
  expect(Object.keys(flags)).toHaveLength(0)
  expect(() => captureFixed(() => { throw Error('abort') })).toThrow('abort')
  expect(() => divideFixed(a, b, 'TRUNCATING', 'WRAP', false)).toThrow('captureFixed')
  const outer = captureFixed(() => {
    const first = divideFixed(a, b, 'TRUNCATING', 'WRAP', false)
    const inner = captureFixed(() => divideFixed(a, b, 'TRUNCATING', 'WRAP', true))
    const last = divideFixed(a, b, 'TRUNCATING', 'WRAP', false)
    return {first, inner, last}
  })
  expect(Object.keys(outer.flags)).toHaveLength(0)
  expect(Object.keys(outer.value.inner.flags)).toHaveLength(0)
})
test('captured empty flags are deterministic across independent machine assemblies', () => {
  const kind = fixedInt(8, false)
  const build = () => captureFixed(() => divideFixed(kind.lift(100), kind.lift(7), 'TRUNCATING', 'WRAP', false))
  expect(JSON.stringify(build().flags)).toBe(JSON.stringify(build().flags))
})

test('zero divisor and inherited failure remain failure conditions', () => {
  const kind = fixedInt(8, false)
  const inherited = new Cond({op: '<', a: {op: 'const', value: 0}, b: {op: 'const', value: 1}}, true)
  const a = kind.lift(7)
  const failed = new FixedWord(8, false, a.limbs, inherited)
  expect(captureFixed(() => divideFixed(a, kind.lift(0), 'FLOOR', 'WRAP', true)).value.failure?.ok).toBe(true)
  expect(captureFixed(() => divideFixed(failed, kind.lift(3), 'FLOOR', 'WRAP', false)).value.failure?.ok).toBe(true)
})
