import {expect, test} from 'bun:test'
import {fixedInt, rule} from './dsl.ts'
import {interpret, loadJs} from './machine.ts'
import {evaluatePrimitive} from '../kernel/integer-primitives.ts'

for (const width of [8, 16, 32, 64] as const) for (const signed of [false, true]) {
  const k = fixedInt(width, signed)
  const m = 1n << BigInt(width), min = signed ? -(m / 2n) : 0n, max = signed ? m / 2n - 1n : m - 1n
  const configurations = width === 8
    ? (['FLOOR', 'TRUNCATING', 'EUCLIDEAN'] as const).flatMap(division => (['WRAP', 'SATURATE', 'TRAP'] as const).map(overflow => ({division, overflow})))
    : [{division: 'EUCLIDEAN' as const, overflow: 'TRAP' as const}, {division: 'TRUNCATING' as const, overflow: 'WRAP' as const}]
  for (const {division, overflow} of configurations) test(`symbolic ${width} signed=${signed} ${division}/${overflow}`, () => {
    const r = rule('symbolic division').inputs({a: k, b: k}).state({q: k.from('0'), rem: k.from('0')})
      .step(({a, b}) => ({q: a.div(b, division, overflow), rem: a.rem(b, division, overflow)}))
    const machine = r.machine, engines = [interpret(machine), loadJs(machine)]
    const pairs: [bigint, bigint][] = signed ? [[-13n, 5n], [-13n, -5n], [13n, -5n], [min, -1n], [max, 0n], [min, 1n], [-13n, min], [max, min], [min, min], [min, max], [0n, min]]
      : [[max, 3n], [max, max], [0n, 1n], [max, 0n], [1n, max]]
    for (const [a, b] of pairs) {
      const quotient = evaluatePrimitive({width, signed, operation: 'div', overflow, division}, a, b)
      const remainder = evaluatePrimitive({width, signed, operation: 'rem', overflow, division}, a, b)
      const input = {...k.encode('a', a.toString()), ...k.encode('b', b.toString())}
      for (const engine of engines) {
        const before = engine.init({})
        if (!quotient.ok || !remainder.ok) expect(() => engine.step({}, before, input)).toThrow('fixed-width primitive failed')
        else {
          const after = engine.step({}, before, input)
          expect(BigInt(k.decode('q', after.scalars) as string | number)).toBe(quotient.value)
          expect(BigInt(k.decode('rem', after.scalars) as string | number)).toBe(remainder.value)
        }
      }
    }
  }, 180_000)
}
