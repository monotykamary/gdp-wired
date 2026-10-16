// The generated JavaScript (compileJs, which updates its maps in place) against the interpreter (which copies them), on
// random machines whose map values read the other map and whose scalars read both, so a write seen before every read
// is done would show; and branches made with fork stay apart. FUZZ_SEED and FUZZ_SCALE shard it as kernel.test.ts.
import {expect, test} from 'bun:test'
import {type C, type E, type Machine, type State, interpret, loadJs} from './machine.ts'

let seed = Number(process.env.FUZZ_SEED ?? 777)
const scale = Number(process.env.FUZZ_SCALE ?? 1)
const rand = (n: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * n) }
const pick = <T>(xs: T[]): T => xs[rand(xs.length)]!
const names = ['p', 'a', 'b', 'z', 'y']
const term = (d: number): E => {
  const r = rand(d <= 0 ? 3 : 8)
  if (r === 0) return {op: 'var', name: pick(names)}
  if (r === 1) return {op: 'const', value: rand(4)}
  if (r === 2) return {op: 'get', map: pick(['A', 'B']), key: d <= 0 ? {op: 'var', name: pick(['a', 'b'])} : term(d - 1)}
  if (r === 3) return {op: 'add', a: term(d - 1), b: term(d - 1)}
  if (r === 4) return {op: 'sub', a: term(d - 1), b: term(d - 1)}
  if (r === 5) return {op: 'min', a: term(d - 1), b: term(d - 1)}
  if (r === 6) return {op: 'mul', k: 2, a: term(d - 1)}
  return {op: 'if', c: cond(d - 1), then: term(d - 1), else: term(d - 1)}
}
const cond = (d: number): C => {
  const r = rand(5)
  if (r === 3) return {op: 'not', x: cond(d)}
  if (r === 4 && d > 0) return {op: rand(2) ? 'and' : 'or', xs: [cond(d - 1), cond(d - 1)]}
  return {op: (['<', '<=', '='] as const)[rand(3)]!, a: term(d), b: term(d)}
}
const withFlag = (e: E): E => (rand(3) ? e : {op: 'if', c: {op: 'flag', name: 'f'}, then: e, else: term(0)})
function machine(): Machine {
  return {
    name: 'random', params: ['p'], inputs: ['a', 'b'], state: {z: {op: 'var', name: 'p'}, y: {op: 'const', value: 0}}, maps: {A: 0, B: 1},
    step: {
      flags: {f: cond(1)},
      state: {z: withFlag(term(2)), y: withFlag(term(2))},
      maps: {A: {key: rand(2) ? {op: 'var', name: 'a'} : term(1), value: withFlag(term(2))}, B: {key: rand(2) ? {op: 'var', name: 'a'} : term(1), value: withFlag(term(2))}},
    },
  }
}
const load = (m: Machine) => loadJs(m)
const cells = (st: State) => JSON.stringify(Object.fromEntries(Object.entries(st.maps).map(([name, map]) => [name, [...map.entries()].sort((x, y) => x[0] - y[0])])))
const same = (a: State, b: State) => { expect(a.scalars).toEqual(b.scalars); expect(cells(a)).toBe(cells(b)) }

test('the generated JavaScript steps as the interpreter does', () => {
  let steps = 0, forks = 0
  for (let trial = 0; trial < 2000 * scale; trial++) {
    const m = machine(), gen = load(m), run = interpret(m)
    const params = {p: rand(4)}
    const input = () => ({a: rand(4), b: rand(4)})
    let st = run.init(params), g = gen.init(params)
    same(st, g)
    for (let i = 0; i < 1 + rand(30); i++) {
      const r = input()
      st = run.step(params, st, r), g = gen.step(params, g, r)
      same(st, g)
      steps++
    }
    // Two branches from one state: fork each, step them apart, then neither sees the other.
    const r1 = input(), r2 = input()
    const left = gen.step(params, gen.fork(g), r1), right = gen.step(params, gen.fork(g), r2)
    same(run.step(params, st, r1), left)
    same(run.step(params, st, r2), right)
    same(st, g)
    forks++
  }
  console.log(`compiled vs interpreted: ${steps.toLocaleString()} steps and ${forks.toLocaleString()} forks agree`)
}, 600_000)
