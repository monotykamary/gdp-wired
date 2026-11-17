import {describe, expect, test} from 'bun:test'
import {checkWrapCase, evaluatePrimitive, evaluatePrimitiveReceipt, type DivisionMode, type OverflowMode, type PrimitiveOperation, type PrimitiveSpec, type Width} from './integer-primitives.ts'

const spec = (width: Width, signed: boolean, operation: PrimitiveOperation, overflow: OverflowMode = 'TRAP', division?: DivisionMode): PrimitiveSpec =>
  ({width, signed, operation, overflow, ...(division === undefined ? {} : {division})})
const ok = (value: bigint) => ({ok: true as const, value})
const failure = (reason: string) => ({ok: false as const, reason})

for (const width of [8, 16, 32, 64] as const) for (const signed of [false, true]) {
  const modulus = 1n << BigInt(width)
  const min = signed ? -(modulus >> 1n) : 0n
  const max = signed ? (modulus >> 1n) - 1n : modulus - 1n
  describe(`${signed ? 'signed' : 'unsigned'} ${width}`, () => {
    test('exact endpoints, overflow policies, cast and operand bounds', () => {
      expect(evaluatePrimitive(spec(width, signed, 'add'), max, 0n)).toEqual(ok(max))
      expect(evaluatePrimitive(spec(width, signed, 'add'), max, 1n)).toEqual(failure('overflow'))
      expect(evaluatePrimitive(spec(width, signed, 'add', 'WRAP'), max, 1n)).toEqual(ok(min))
      expect(evaluatePrimitive(spec(width, signed, 'add', 'SATURATE'), max, 1n)).toEqual(ok(max))
      expect(evaluatePrimitive(spec(width, signed, 'sub', 'WRAP'), min, 1n)).toEqual(ok(max))
      expect(evaluatePrimitive(spec(width, signed, 'sub', 'SATURATE'), min, 1n)).toEqual(ok(min))
      expect(evaluatePrimitive(spec(width, signed, 'mul'), 2n, max)).toEqual(failure('overflow'))
      expect(evaluatePrimitive(spec(width, signed, 'neg', 'WRAP'), min)).toEqual(ok(signed ? min : 0n))
      expect(evaluatePrimitive(spec(width, signed, 'cast', 'WRAP'), modulus * 2n + 1n)).toEqual(ok(1n))
      expect(evaluatePrimitive(spec(width, signed, 'cast', 'TRAP'), modulus)).toEqual(failure('overflow'))
      expect(evaluatePrimitive(spec(width, signed, 'add'), max + 1n, 0n)).toEqual(failure('a out of bounds'))
      expect(evaluatePrimitive(spec(width, signed, 'add'), 0n, min - 1n)).toEqual(failure('b out of bounds'))
    })
  })
}

for (const mode of ['TRUNCATING', 'FLOOR', 'EUCLIDEAN'] as const) {
  test(`${mode}: signed quotient and remainder identities with both divisor signs`, () => {
    const results: Record<DivisionMode, [bigint, bigint, bigint, bigint]> = {
      TRUNCATING: [-2n, -1n, 2n, -1n],
      FLOOR: [-3n, 2n, 2n, -1n],
      EUCLIDEAN: [-3n, 2n, 3n, 2n],
    }
    const [positiveQ, positiveR, negativeQ, negativeR] = results[mode]
    for (const [b, q, r] of [[3n, positiveQ, positiveR], [-3n, negativeQ, negativeR]] as const) {
      expect(evaluatePrimitive(spec(8, true, 'div', 'TRAP', mode), -7n, b)).toEqual(ok(q))
      expect(evaluatePrimitive(spec(8, true, 'rem', 'TRAP', mode), -7n, b)).toEqual(ok(r))
      expect(-7n).toBe(b * q + r)
    }
  })
  for (const overflow of ['TRAP', 'WRAP', 'SATURATE'] as const) test(`${mode}/${overflow}: MIN/-1 is a division pair`, () => {
    const div = evaluatePrimitive(spec(8, true, 'div', overflow, mode), -128n, -1n)
    const rem = evaluatePrimitive(spec(8, true, 'rem', overflow, mode), -128n, -1n)
    expect(div).toEqual(overflow === 'TRAP' ? failure('overflow') : ok(overflow === 'WRAP' ? -128n : 127n))
    expect(rem).toEqual(overflow === 'TRAP' ? failure('overflow') : ok(0n))
  })
  for (const overflow of ['TRAP', 'WRAP', 'SATURATE'] as const) for (const operation of ['div', 'rem'] as const)
    test(`${mode}/${overflow}/${operation}: zero division fails`, () => {
      expect(evaluatePrimitive(spec(64, true, operation, overflow, mode), 0n, 0n)).toEqual(failure('division by zero'))
    })
}

test('invalid runtime specs and operands fail closed', () => {
  const valid = spec(8, true, 'add')
  for (const bad of [null, {}, {...valid, width: 7}, {...valid, width: 8n}, {...valid, signed: 1},
    {...valid, overflow: 'oops'}, {...valid, operation: 'oops'}, {...valid, division: 'FLOOR'},
    {...valid, extra: true}, {...valid, width: 16.5}]) {
    expect(evaluatePrimitive(bad as PrimitiveSpec, 1n, 2n).ok).toBe(false)
  }
  expect(evaluatePrimitive(spec(8, true, 'div'), 1n, 1n)).toEqual(failure('invalid division mode'))
  expect(evaluatePrimitive(valid, 1 as unknown as bigint, 1n)).toEqual(failure('a must be bigint'))
  expect(evaluatePrimitive(valid, 1n, 1 as unknown as bigint)).toEqual(failure('b must be bigint'))
  expect(evaluatePrimitive(spec(8, true, 'neg'), 1n, 2n)).toEqual(failure('unexpected b'))
})

test('accessors are rejected without invocation; receipt never rereads a spec', () => {
  let reads = 0
  const hostile = {signed: true, operation: 'add', overflow: 'TRAP', get width() { reads++; return reads === 1 ? 8 : 64 }} as PrimitiveSpec
  expect(evaluatePrimitive(hostile, 127n, 1n)).toEqual(failure('invalid spec'))
  expect(evaluatePrimitiveReceipt(hostile, 127n, 1n)).toEqual({spec: null, a: '127', b: '1', result: failure('invalid spec')})
  expect(reads).toBe(0)
  const symbol = {...spec(8, true, 'add'), [Symbol('hidden')]: true}
  expect(evaluatePrimitive(symbol, 1n, 2n)).toEqual(failure('invalid spec'))
  const proxy = new Proxy(spec(8, true, 'add'), {getOwnPropertyDescriptor() { throw Error('hostile') }})
  expect(evaluatePrimitive(proxy, 1n, 2n)).toEqual(failure('invalid spec'))
  expect(evaluatePrimitiveReceipt(proxy, 1n, 2n).spec).toBeNull()
  const ownKeysProxy = new Proxy(spec(8, true, 'add'), {ownKeys() { throw Error('hostile') }})
  expect(evaluatePrimitive(ownKeysProxy, 1n, 2n)).toEqual(failure('invalid spec'))
  const data = spec(8, true, 'add')
  const receipt = evaluatePrimitiveReceipt(data, 127n, 1n)
  data.width = 64
  expect(receipt.spec?.width).toBe(8)
  expect(receipt.result).toEqual(failure('overflow'))
})

test('bounded wrap case checker validates identities and rejects tampering', () => {
  const s = spec(8, true, 'add', 'WRAP')
  const cert = {quotient: 0n, residue: 128n, value: -128n}
  expect(checkWrapCase(s, 127n, 1n, cert)).toBe(true)
  expect(checkWrapCase(s, 127n, 1n, {...cert, value: 128n})).toBe(false)
  expect(checkWrapCase(s, 127n, 1n, {...cert, quotient: 1n})).toBe(false)
  let reads = 0
  const accessor = {quotient: 0n, residue: 128n, get value() { reads++; return -128n }}
  expect(checkWrapCase(s, 127n, 1n, accessor)).toBe(false)
  expect(reads).toBe(0)
  expect(checkWrapCase(s, 127n, 2n, cert)).toBe(false)
  expect(checkWrapCase(spec(8, true, 'add', 'TRAP'), 127n, 1n, cert)).toBe(false)
  expect(checkWrapCase(spec(8, false, 'sub', 'WRAP'), 0n, 1n, {quotient: -1n, residue: 255n, value: 255n})).toBe(true)
})

test('wrap checker rejects non-bigint operands before arithmetic, without throwing', () => {
  const s = spec(8, true, 'mul', 'WRAP'), cert = {quotient: 0n, residue: 126n, value: 126n}
  for (const bad of [null, true, '1', {}, undefined]) {
    expect(checkWrapCase(s, bad as unknown as bigint, 1n, cert)).toBe(false)
    expect(checkWrapCase(s, 126n, bad as unknown as bigint, cert)).toBe(false)
  }
})

test('invalid supplied operands remain present in diagnostic receipts', () => {
  const unary = spec(8, true, 'neg', 'WRAP')
  expect(evaluatePrimitiveReceipt(unary, 1n, 42 as unknown as bigint)).toEqual({
    spec: unary, a: '1', b: '<invalid>', result: failure('unexpected b'),
  })
  expect(evaluatePrimitiveReceipt(spec(8, true, 'add'), 1n, 'bad' as unknown as bigint).b).toBe('<invalid>')
  expect(evaluatePrimitiveReceipt(unary, 'bad' as unknown as bigint).a).toBe('<invalid>')
})

test('receipt transports exact decimal strings and JSON serializes', () => {
  const s = spec(64, false, 'cast', 'WRAP')
  const receipt = evaluatePrimitiveReceipt(s, (1n << 128n) + 5n)
  expect(JSON.parse(JSON.stringify(receipt))).toEqual({spec: s, a: ((1n << 128n) + 5n).toString(), result: {ok: true, value: '5'}})
})
