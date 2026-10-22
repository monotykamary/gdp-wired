// The k-step fuzz's laws (kernel/steplaw.test.ts's 'k steps', the same seed and generator) proven again, each timed,
// with its certificate's `cyclic:` line under GDP_CYCLIC_LOG=1: `FUZZ_SCALE=10 bun research/cyclic/kstepfuzz.ts
// [trial.form ...]` (only those laws, where given: GDP_CYCLIC_DEBUG=1 then shows each goal grown).
import type {C, E, Machine} from '../../core/machine.ts'
import type {StepLaw} from '../../kernel/kernel.ts'
import {proveStepLaws} from '../../kernel/prove.ts'

let seed = Number(process.env.FUZZ_SEED ?? 31)
const scale = Number(process.env.FUZZ_SCALE ?? 1), only = new Set(process.argv.slice(2))
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const pick = <T>(xs: readonly T[]): T => xs[rand(xs.length)]!
const vv = (name: string): E => ({op: 'var', name}), cc = (value: number): E => ({op: 'const', value})
const term = (d: number): E => {
  const r = rand(d <= 0 ? 2 : 6)
  if (r === 0) return vv(pick(['a', 'b', 'p', 'x', 'y']))
  if (r === 1) return cc(rand(3))
  if (r === 2) return {op: 'add', a: term(d - 1), b: term(d - 1)}
  if (r === 3) return {op: 'sub', a: term(d - 1), b: term(d - 1)}
  if (r === 4) return {op: 'min', a: term(d - 1), b: term(d - 1)}
  return {op: 'if', c: {op: pick(['<', '<=', '='] as const), a: term(d - 1), b: term(d - 1)}, then: term(d - 1), else: term(d - 1)}
}
const x = vv('x'), y = vv('y'), x1 = vv("x'"), y1 = vv("y'"), a = vv('a'), a2 = vv('a@2')
const forms: C[] = [{op: '<=', a: x, b: x1}, {op: '<=', a: x1, b: {op: 'add', a: {op: 'add', a: x, b: a}, b: a2}}, {op: '=', a: x1, b: x},
  {op: '<=', a: {op: 'add', a: x, b: y}, b: {op: 'add', a: x1, b: y1}}, {op: '<=', a: {op: 'get', map: 'M', key: a}, b: {op: 'get', map: "M'", key: a}},
  {op: '<=', a: {op: 'get', map: "M'", key: a2}, b: {op: 'add', a: {op: 'get', map: 'M', key: a2}, b: {op: 'mul', k: 2, a: {op: 'add', a: vv('p'), b: cc(1)}}}}]
let proven = 0, total = 0
const t00 = performance.now()
for (let trial = 0; trial < 40 * scale; trial++) {
  const m: Machine = {name: 'random', params: ['p'], inputs: ['a', 'b'], state: {x: cc(0), y: cc(0)}, maps: {M: 0},
    step: {state: {x: rand(2) ? {op: 'add', a: vv('x'), b: term(1)} : term(2), y: term(2)}, maps: {M: {key: vv('a'), value: rand(2) ? {op: 'add', a: {op: 'get', map: 'M', key: vv('a')}, b: term(1)} : term(1)}}}}
  for (const [i, then] of forms.entries()) {
    const k = 2 + rand(2)
    const sl: StepLaw = {name: `form ${i}`, steps: k, then, ...(rand(3) === 0 ? {when: [{op: '<=', a: vv('a'), b: vv('b')} as C]} : {})}
    if (only.size && !only.has(`${trial}.${i}`)) continue
    if (only.size) console.log(`${trial}.${i}: ${k} steps, ${JSON.stringify(m.step)}, ${JSON.stringify(sl)}`)
    const t0 = performance.now(), ok = proveStepLaws(m, [], [sl])
    total++; if (ok.proven && ok.checked) proven++
    console.error(`law ${trial}.${i} (${k} steps): ${ok.proven && ok.checked ? 'proven' : 'refused'} in ${Math.round(performance.now() - t0)} ms`)
  }
}
console.log(`${proven} of ${total} proven in ${Math.round(performance.now() - t00)} ms`)
