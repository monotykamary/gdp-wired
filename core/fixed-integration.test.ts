import {expect, test} from 'bun:test'
import {fixedInt, rule, when} from './dsl.ts'
import {interpret, loadJs} from './machine.ts'
import {evaluatePrimitive} from '../kernel/integer-primitives.ts'

for (const width of [8, 16, 32, 64] as const) for (const signed of [false, true]) {
  const kind = fixedInt(width, signed)
  const modulus = 1n << BigInt(width), lo = signed ? -(modulus / 2n) : 0n, hi = signed ? modulus / 2n - 1n : modulus - 1n
  for (const overflow of ['WRAP', 'SATURATE', 'TRAP'] as const) for (const operation of ['add', 'sub', 'mul'] as const) {
    test(`fixed DSL interpreter/compileJs ${width} signed=${signed} ${operation}/${overflow}`, () => {
      const r = rule('fixed differential').inputs({a: kind, b: kind}).state({x: kind.from('0')})
        .step(({a, b}) => ({x: operation === 'add' ? a.plus(b, overflow) : operation === 'sub' ? a.minus(b, overflow) : a.mul(b, overflow)}))
      const machine = r.machine, engines = [interpret(machine), loadJs(machine)]
      const edges = [...new Set([lo, lo + 1n, 0n, 1n, hi - 1n, hi].filter(n => n >= lo && n <= hi))]
      for (const a of edges) for (const b of edges) {
        const expected = evaluatePrimitive({width, signed, operation, overflow}, a, b)
        const input = {...kind.encode('a', a.toString()), ...kind.encode('b', b.toString())}
        for (const engine of engines) {
          const before = engine.init({}), scalars = {...before.scalars}
          if (!expected.ok) {
            expect(() => engine.step({}, before, input)).toThrow('fixed-width primitive failed')
            expect(before.scalars).toEqual(scalars)
          } else {
            const after = engine.step({}, before, input)
            expect(BigInt(kind.decode('x', after.scalars) as string | number)).toBe(expected.value)
          }
        }
      }
    }, 120_000)
  }
}

test('TRAP preserves maps and unrelated scalars before any writes in both engines', () => {
  const u8 = fixedInt(8, false)
  const r = rule('atomic primitive trap').inputs({a: u8}).state({x: u8.from('255'), touched: 0}).maps({m: 7})
    .step(({x, a, touched, m}) => ({x: x.plus(a, 'TRAP'), touched: touched.plus(1), m: m.set(0, 99)}))
  for (const engine of [interpret(r.machine), loadJs(r.machine)]) {
    const before = engine.init({})
    expect(() => engine.step({}, before, u8.encode('a', 1))).toThrow('fixed-width primitive failed')
    expect(before.maps.m!.size).toBe(0)
    expect(before.scalars.touched).toBe(0)
    expect(u8.decode('x', before.scalars)).toBe(255)
  }
})

test('unselected TRAP branch does not fail', () => {
  const u8 = fixedInt(8, false)
  const r = rule('lazy fixed trap').inputs({a: u8}).state({x: u8.from('255')})
    .step(({x, a}) => ({x: when(a.eq(u8.lift(0)), x, x.plus(a, 'TRAP'))}))
  for (const engine of [interpret(r.machine), loadJs(r.machine)]) {
    const before = engine.init({})
    expect(u8.decode('x', engine.step({}, before, u8.encode('a', 0)).scalars)).toBe(255)
  }
})
