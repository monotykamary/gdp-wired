import {expect, test} from 'bun:test'
import {fixedInt, rule} from './dsl.ts'
import {interpret, loadJs} from './machine.ts'
import {evaluatePrimitive} from '../kernel/integer-primitives.ts'
for (const width of [8, 16, 32, 64] as const) for (const signed of [false, true]) {
  const k = fixedInt(width, signed), min = signed ? -(1n << BigInt(width - 1)) : 0n
  const max = (1n << BigInt(width - (signed ? 1 : 0))) - 1n
  const inputs = [...new Set([min, min + 1n, 0n, 1n, max - 1n, max, ...(signed ? [-1n] : [])])]
  const divisors = [0n, 1n, 2n, 3n, ...(signed ? [-1n, -3n] : []), ...(width >= 32 ? [(1n << 30n) + 3n] : []), ...(width === 64 ? [(1n << 37n) - 1n] : [])]
  for (const rounding of ['FLOOR', 'TRUNCATING', 'EUCLIDEAN'] as const) for (const mode of ['WRAP', 'SATURATE', 'TRAP'] as const)
    test(`${signed ? 'i' : 'u'}${width} literal division ${rounding} ${mode}`, () => {
      for (const d of divisors) {
        const r = rule('literal division').inputs({a: k}).state({q: k.from('0'), rem: k.from('0')})
          .step(({a}) => ({q: a.div(k.lift(d), rounding, mode), rem: a.rem(k.lift(d), rounding, mode)}))
        expect(Object.keys(r.machine.step.flags ?? {})).toHaveLength(0)
        const params = {}, runtimes = [interpret(r.machine), loadJs(r.machine)]
        for (const a of inputs) for (const rt of runtimes) {
          const before = rt.init(params), request = k.encode('a', a.toString())
          const q = evaluatePrimitive({width, signed, operation: 'div', overflow: mode, division: rounding}, a, d)
          const rem = evaluatePrimitive({width, signed, operation: 'rem', overflow: mode, division: rounding}, a, d)
          if (!q.ok || !rem.ok) {
            expect(() => rt.step(params, before, request)).toThrow('fixed-width primitive failed')
            expect(BigInt(k.decode('q', before.scalars) as string | number)).toBe(0n); expect(BigInt(k.decode('rem', before.scalars) as string | number)).toBe(0n)
          } else {
            const after = rt.step(params, before, request)
            expect(BigInt(k.decode('q', after.scalars) as string | number)).toBe(q.value); expect(BigInt(k.decode('rem', after.scalars) as string | number)).toBe(rem.value)
          }
        }
      }
    }, 30_000)
}
