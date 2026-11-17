import {describe, expect, test} from 'bun:test'
import {checkWrapCase, evaluatePrimitive, evaluatePrimitiveReceipt, type DivisionMode, type OverflowMode, type PrimitiveOperation, type PrimitiveSpec, type PrimitiveResult, type Width} from './integer-primitives.ts'

const widths: Width[] = [8, 16, 32, 64]
const overflows: OverflowMode[] = ['WRAP', 'SATURATE', 'TRAP']
const divisions: DivisionMode[] = ['FLOOR', 'TRUNCATING', 'EUCLIDEAN']
const operations: PrimitiveOperation[] = ['add', 'sub', 'mul', 'neg', 'cast', 'div', 'rem']
const bounds = (width: Width, signed: boolean) => {
  const modulus = 1n << BigInt(width)
  return {modulus, min: signed ? -(modulus / 2n) : 0n, max: signed ? modulus / 2n - 1n : modulus - 1n}
}
const mod = (x: bigint, n: bigint) => (x % n + n) % n
// A deliberately separate, mathematical oracle: enumerate the quotient satisfying each remainder convention.
function exact(spec: PrimitiveSpec, a: bigint, b?: bigint): {raw: bigint, quotient?: bigint, remainder?: bigint} | undefined {
  const {operation, division} = spec
  if (operation === 'add') return {raw: a + b!}
  if (operation === 'sub') return {raw: a - b!}
  if (operation === 'mul') return {raw: a * b!}
  if (operation === 'neg') return {raw: -a}
  if (operation === 'cast') return {raw: a}
  if (b === 0n) return undefined
  let q = a / b!
  // At most one neighbouring quotient can have the demanded sign of remainder.
  for (const candidate of [q - 1n, q, q + 1n]) {
    const r = a - candidate * b!
    if (r <= -abs(b!) || r >= abs(b!)) continue
    if (division === 'TRUNCATING' && r !== 0n && (r < 0n) !== (a < 0n)) continue
    if (division === 'FLOOR' && r !== 0n && (r < 0n) !== (b! < 0n)) continue
    if (division === 'EUCLIDEAN' && r < 0n) continue
    q = candidate
    return {raw: operation === 'div' ? q : r, quotient: q, remainder: r}
  }
  throw new Error('oracle quotient missing')
}
const abs = (x: bigint) => x < 0n ? -x : x
function oracle(spec: PrimitiveSpec, a: bigint, b?: bigint): PrimitiveResult {
  const {min, max, modulus} = bounds(spec.width, spec.signed)
  if (spec.operation !== 'cast' && (a < min || a > max)) return {ok: false, reason: 'a out of bounds'}
  if (b !== undefined && (b < min || b > max)) return {ok: false, reason: 'b out of bounds'}
  const e = exact(spec, a, b)
  if (!e) return {ok: false, reason: 'division by zero'}
  if (spec.operation === 'rem' && spec.overflow === 'TRAP' && (e.quotient! < min || e.quotient! > max)) return {ok: false, reason: 'overflow'}
  if (e.raw >= min && e.raw <= max) return {ok: true, value: e.raw}
  if (spec.overflow === 'TRAP') return {ok: false, reason: 'overflow'}
  if (spec.overflow === 'SATURATE') return {ok: true, value: e.raw < min ? min : max}
  const u = mod(e.raw, modulus)
  return {ok: true, value: spec.signed && u > max ? u - modulus : u}
}
let seed = 0x9e3779b97f4a7c15n
function random(): bigint {
  seed = (seed * 6364136223846793005n + 1442695040888963407n) & ((1n << 64n) - 1n)
  return seed
}
function operands(width: Width, signed: boolean): bigint[] {
  const {min, max, modulus} = bounds(width, signed)
  const corners = [min, min + 1n, -1n, 0n, 1n, 2n, max - 1n, max].filter(x => x >= min && x <= max)
  return [...corners, ...Array.from({length: 96}, () => {
    const u = random() % modulus
    return signed && u > max ? u - modulus : u
  })]
}

describe('fixed-width exact BigInt primitives', () => {
  for (const width of widths) for (const signed of [false, true]) test(`width=${width} signed=${signed}`, () => {
    const {min, max, modulus} = bounds(width, signed)
    const values = operands(width, signed)
    const large = [min - modulus * 3n - 1n, max + modulus * 3n + 1n, -(1n << 130n), 1n << 130n]
    for (const operation of operations) for (const overflow of overflows) for (const division of operation === 'div' || operation === 'rem' ? divisions : [undefined]) {
      const spec: PrimitiveSpec = {width, signed, operation, overflow, ...(division ? {division} : {})}
      for (let i = 0; i < values.length; i++) {
        const a = operation === 'cast' && i % 8 === 0 ? large[(i / 8) % large.length]! : values[i]!
        const b = operation === 'div' || operation === 'rem' ? values[(i * 31 + 5) % values.length]! : operation === 'neg' || operation === 'cast' ? undefined : values[(i * 17 + 3) % values.length]!
        const expected = oracle(spec, a, b)
        const actual = evaluatePrimitive(spec, a, b)
        expect(actual).toEqual(expected)
        const receipt = evaluatePrimitiveReceipt(spec, a, b)
        expect(receipt.a).toBe(a.toString())
        expect(receipt.b).toBe(b?.toString())
        expect(receipt.result).toEqual(expected.ok ? {ok: true, value: expected.value.toString()} : expected)
        if (!actual.ok) continue
        expect(actual.value >= min && actual.value <= max).toBe(true)
        const e = exact(spec, a, b)!
        if (e.raw >= min && e.raw <= max) expect(actual.value).toBe(e.raw)
        if (e.raw >= min && e.raw <= max && operation === 'add') expect(actual.value - b!).toBe(a)
        if (e.raw >= min && e.raw <= max && operation === 'sub') expect(actual.value + b!).toBe(a)
        if (e.raw >= min && e.raw <= max && operation === 'mul' && b !== 0n) expect(actual.value / b!).toBe(a)
        if (e.raw >= min && e.raw <= max && operation === 'neg') expect(-actual.value).toBe(a)
        if (overflow === 'WRAP') {
          expect(mod(actual.value - e.raw, modulus)).toBe(0n)
          if (operation !== 'div' && operation !== 'rem') {
            const residue = mod(e.raw, modulus), quotient = (e.raw - residue) / modulus
            const certificate = {quotient, residue, value: actual.value}
            expect(checkWrapCase(spec, a, b, certificate)).toBe(true)
            expect(checkWrapCase(spec, a, b, {...certificate, quotient: quotient + 1n})).toBe(false)
            expect(checkWrapCase(spec, a, b, {...certificate, residue: residue + 1n})).toBe(false)
            expect(checkWrapCase(spec, a, b, {...certificate, value: actual.value + 1n})).toBe(false)
          }
        }
        if (overflow === 'SATURATE') expect(actual.value).toBe(e.raw < min ? min : e.raw > max ? max : e.raw)
        if (e.remainder !== undefined) {
          expect(a).toBe(e.quotient! * b! + e.remainder)
          expect(abs(e.remainder) < abs(b!)).toBe(true)
          if (division === 'FLOOR' && e.remainder !== 0n) expect(e.remainder < 0n).toBe(b! < 0n)
          if (division === 'TRUNCATING' && e.remainder !== 0n) expect(e.remainder < 0n).toBe(a < 0n)
          if (division === 'EUCLIDEAN') expect(e.remainder >= 0n).toBe(true)
          // Both operations must agree on the same exact quotient/remainder pair.
          const paired = evaluatePrimitive({...spec, operation: operation === 'div' ? 'rem' : 'div'}, a, b)
          expect(paired).toEqual(oracle({...spec, operation: operation === 'div' ? 'rem' : 'div'}, a, b))
        }
      }
    }
  })

  test('boundary and negative controls distinguish rounding, overflow and zero quotient pair', () => {
    for (const width of widths) {
      const {min, max, modulus} = bounds(width, true)
      for (const division of divisions) {
        for (const operation of ['div', 'rem'] as const) {
          const spec: PrimitiveSpec = {width, signed: true, operation, overflow: 'TRAP', division}
          expect(evaluatePrimitive(spec, min, -1n)).toEqual({ok: false, reason: 'overflow'})
          expect(evaluatePrimitive(spec, 1n, 0n)).toEqual({ok: false, reason: 'division by zero'})
          expect(evaluatePrimitive({...spec, overflow: 'WRAP'}, min, -1n)).toEqual({ok: true, value: operation === 'div' ? min : 0n})
          expect(evaluatePrimitive({...spec, overflow: 'SATURATE'}, min, -1n)).toEqual({ok: true, value: operation === 'div' ? max : 0n})
        }
      }
      for (const division of divisions) {
        // -5 / -2: floor and truncation coincide; Euclidean differs.
        const expected: readonly [bigint, bigint] = division === 'EUCLIDEAN' ? [3n, 1n] : [2n, -1n]
        expect(evaluatePrimitive({width, signed: true, operation: 'div', overflow: 'TRAP', division}, -5n, -2n)).toEqual({ok: true, value: expected[0]})
        expect(evaluatePrimitive({width, signed: true, operation: 'rem', overflow: 'TRAP', division}, -5n, -2n)).toEqual({ok: true, value: expected[1]})
      }
      expect(evaluatePrimitive({width, signed: true, operation: 'add', overflow: 'WRAP'}, max, 1n)).toEqual({ok: true, value: min})
      expect(evaluatePrimitive({width, signed: true, operation: 'add', overflow: 'SATURATE'}, max, 1n)).toEqual({ok: true, value: max})
      expect(evaluatePrimitive({width, signed: true, operation: 'add', overflow: 'TRAP'}, max, 1n)).toEqual({ok: false, reason: 'overflow'})
      expect(evaluatePrimitive({width, signed: false, operation: 'cast', overflow: 'WRAP'}, -1n)).toEqual({ok: true, value: modulus - 1n})
      for (const overflow of overflows) for (const division of divisions) for (const operation of ['div', 'rem'] as const)
        expect(evaluatePrimitive({width, signed: false, operation, overflow, division}, 1n, 0n)).toEqual({ok: false, reason: 'division by zero'})
    }
    const spec: PrimitiveSpec = {width: 8, signed: true, operation: 'div', overflow: 'TRAP', division: 'FLOOR'}
    for (const [a, b, floorQ, truncQ, euclidQ] of [[-5n, 2n, -3n, -2n, -3n], [5n, -2n, -3n, -2n, -2n], [-5n, -2n, 2n, 2n, 3n]] as const) {
      expect(evaluatePrimitive(spec, a, b)).toEqual({ok: true, value: floorQ})
      expect(evaluatePrimitive({...spec, division: 'TRUNCATING'}, a, b)).toEqual({ok: true, value: truncQ})
      expect(evaluatePrimitive({...spec, division: 'EUCLIDEAN'}, a, b)).toEqual({ok: true, value: euclidQ})
    }
  })

  test('reject malformed policies, forged objects and unsafe Number operands', () => {
    const base: PrimitiveSpec = {width: 8, signed: true, operation: 'add', overflow: 'TRAP'}
    const nullPrototype = Object.assign(Object.create(null), base) as PrimitiveSpec
    expect(evaluatePrimitive(nullPrototype, 1n, 2n)).toEqual({ok: true, value: 3n})
    const bad: unknown[] = [null, [], 4, Object.create({width: 8, signed: true, operation: 'add', overflow: 'TRAP'}),
      {...base, width: 7}, {...base, width: 24}, {...base, width: 8.5}, {...base, signed: 1}, {...base, operation: 'xor'},
      {...base, overflow: 'IGNORE'}, {...base, division: 'FLOOR'}, {...base, unknown: true},
      {...base, operation: 'div'}, {...base, operation: 'rem', division: 'SIDEWAYS'},
      {width: 8, signed: true, operation: 'add', overflow: 'TRAP', __proto__: {forged: true}},
      {width: 8, signed: true, operation: 'add'}, {width: 8, signed: true, operation: 'div', overflow: 'TRAP', division: undefined}]
    for (const s of bad) expect(evaluatePrimitive(s as PrimitiveSpec, 1n, 1n).ok).toBe(false)
    for (const a of [1, Number.MAX_SAFE_INTEGER + 1, NaN, Infinity, '1', null]) expect(evaluatePrimitive(base, a as unknown as bigint, 1n).ok).toBe(false)
    for (const b of [1, Number.MAX_SAFE_INTEGER + 1, NaN, Infinity, '1', null]) expect(evaluatePrimitive(base, 1n, b as unknown as bigint).ok).toBe(false)
    expect(evaluatePrimitive(base, 128n, 0n).ok).toBe(false)
    expect(evaluatePrimitive(base, 0n, 128n).ok).toBe(false)
    expect(evaluatePrimitive({...base, operation: 'neg'}, 1n, 2n).ok).toBe(false)
    expect(evaluatePrimitive({...base, operation: 'cast'}, 1n, 2n).ok).toBe(false)
  })
})
