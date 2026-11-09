// The compiled step's key helpers ($keys, $breaks, $spread via $sorted) against the interpreter's keysAt/breakKeys:
// every-key writes whose values read other maps at offset keys and compare keys with inputs, from random states.
import {expect, test} from 'bun:test'
import {type Machine, type State, compileJs, fastStep, get, interpret, ite, lcg, less, n, plus, same, x} from './machine.ts'

const m: Machine = {name: 'dense writes', params: ['size'], inputs: ['i', 'j'], state: {t: n(0)}, maps: {A: 0, B: 0, C: 1},
  step: {state: {t: plus(x('t'), n(1))}, maps: {
    A: {each: 'k', value: ite(less(x('k'), x('i')), n(1), get('A', x('k')))},
    B: {each: 'k', value: ite(same(get('A', plus(x('k'), n(1))), n(1)), n(2), get('B', x('k')))},
    C: {each: 'k', value: ite(less(get('B', {op: 'sub', a: x('k'), b: n(1)}), n(2)), get('C', x('k')), plus(get('C', x('k')), n(1)))},
  }}}
let seed = 4242
const rand = (k: number) => { seed = lcg(seed); return Math.floor(seed / 2 ** 31 * k) }
const cell = (st: State, map: string, k: number) => st.maps[map]?.get(k) ?? st.defaults?.[map] ?? m.maps![map]!
const view = (st: State) => JSON.stringify([st.scalars, ['A', 'B', 'C'].map(map => [cell(st, map, 40), Array.from({length: 24}, (_, k) => cell(st, map, k))])])

test('the compiled key helpers are sorted arrays and agree with the interpreter on every-key writes', () => {
  const js = compileJs(m)
  expect(js).toContain('function $unique')
  expect(js).toContain('$breaks(')
  const run = interpret(m), fast = fastStep(m)!
  let steps = 0
  for (let trial = 0; trial < 400; trial++) {
    const params = {size: 1 + rand(5)}
    const st = run.init(params)
    for (const map of ['A', 'B', 'C']) { const cells = new Map<number, number>(); for (let q = rand(6); q > 0; q--) cells.set(rand(12), rand(3)); st.maps[map] = cells }
    let a: State = st, b: State = st
    for (let d = 0; d < 6; d++) {
      const input = {i: rand(10), j: rand(10)}
      const next = run.step(params, a, input), quick = fast(params, b, input)
      expect(view(quick)).toBe(view(next))
      a = next; b = quick; steps++
    }
  }
  expect(steps).toBe(2400)
})

test('an inherited enumerable member of the maps dictionary is not a map of the state', () => {
  const run = interpret(m), fast = fastStep(m)!
  const params = {size: 3}, st = run.init(params)
  // A dictionary whose prototype carries an enumerable Map: only own properties are the state's maps.
  st.maps = Object.assign(Object.create({Z: new Map([[7, 1]])}), st.maps) as State['maps']
  st.maps['A'] = new Map([[1, 1], [2, 1]])
  const own = {...st, maps: {A: st.maps['A']!, B: st.maps['B']!, C: st.maps['C']!}}
  for (const input of [{i: 2, j: 0}, {i: 9, j: 1}, {i: 0, j: 3}]) {
    const quick = fast(params, st, input), plain = fast(params, own, input), slow = run.step(params, own, input)
    expect(view(quick)).toBe(view(slow))
    expect(view(quick)).toBe(view(plain))
    expect(Object.keys(quick.maps).sort()).toEqual(['A', 'B', 'C'])
  }
})
