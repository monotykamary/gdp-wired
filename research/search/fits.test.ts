// fitsU32: a space it accepts never computes a value past 2^32 - 1 (random machines, random candidates from the space,
// replayed by the interpreter, every scalar, map cell and term checked), and spaces that would are refused.
import {expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, type State, evalE, interpret, n, plus, times, x} from '../../core/machine.ts'
import {admit, capLaws} from '../../core/models.ts'
import {fitsU32} from './compile.ts'

let seed = Number(process.env.FUZZ_SEED ?? 777)
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const pick = <T>(xs: T[]): T => xs[rand(xs.length)]!
const term = (d: number): E => {
  const r = rand(d <= 0 ? 2 : 8)
  if (r === 0) return x(pick(['p', 'a', 'z', 'y']))
  if (r === 1) return n(rand(4))
  if (r === 2) return plus(term(d - 1), term(d - 1))
  if (r === 3) return {op: 'sub', a: term(d - 1), b: term(d - 1)}
  if (r === 4) return times(pick([2, 3, 1000, 65536]), term(d - 1))
  if (r === 5) return {op: 'prod', a: term(d - 1), b: term(d - 1)}
  if (r === 6) return {op: 'get', map: 'M', key: x('a')}
  return {op: 'if', c: {op: '<', a: term(d - 1), b: term(d - 1)}, then: term(d - 1), else: term(d - 1)}
}
const law: Law = {name: 'true', holds: {op: '<=', a: n(0), b: n(0)}}

test('an accepted space stays below 2^32', () => {
  let accepted = 0, refused = 0, steps = 0, biggest = 0
  for (let trial = 0; trial < 3000; trial++) {
    const m: Machine = {name: 'random', params: ['p'], inputs: ['a'], state: {z: n(rand(3)), y: n(0)}, maps: {M: rand(3)},
      step: {state: {z: term(2), y: term(2)}, maps: {M: {key: x('a'), value: term(2)}}}}
    const space = {depth: 1 + rand(8), bound: 1 + rand(3)}
    try { fitsU32(m, law, space); accepted++ } catch { refused++; continue }
    const run = interpret(m)
    const all = (st: State) => [...Object.values(st.scalars), ...Object.values(st.maps).flatMap(c => [...c.values()])]
    for (let k = 0; k < 20; k++) {
      const params = {p: rand(space.bound + 1)}
      let st = run.init(params)
      for (let t = 0; t < space.depth; t++) {
        const input = {a: rand(space.bound + 1)}
        // every term of the step, evaluated (the runtime throws past 2^53; below that, check 2^32)
        for (const e of [m.step.state!.z!, m.step.state!.y!, m.step.maps!.M!.value]) { const v = evalE(e, {...params, ...input}, st, m); biggest = Math.max(biggest, v); expect(v).toBeLessThan(2 ** 32) }
        st = run.step(params, st, input)
        for (const v of all(st)) expect(v).toBeLessThan(2 ** 32)
        steps++
      }
    }
  }
  console.log(`fitsU32: ${accepted} spaces accepted (${steps.toLocaleString()} steps replayed, largest value ${biggest.toLocaleString()}), ${refused} refused`)
  expect(accepted).toBeGreaterThan(300)
  expect(refused).toBeGreaterThan(30)
})

test('the searches in use fit, and a doubling counter is refused past depth 31', () => {
  for (const l of capLaws) expect(() => fitsU32(admit(), l, {depth: 9, bound: 2})).not.toThrow()
  const doubling: Machine = {name: 'doubling', params: [], inputs: [], state: {v: n(1)}, step: {state: {v: times(2, x('v'))}}}
  expect(() => fitsU32(doubling, law, {depth: 31, bound: 1})).not.toThrow()
  expect(() => fitsU32(doubling, law, {depth: 32, bound: 1})).toThrow()
  void ({} as C)
})
