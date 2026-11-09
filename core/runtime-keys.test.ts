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

test('$unique cannot observe a stamp wrap: at 2^32 − 1 the buffer is zeroed and the stamps restart', () => {
  const src = compileJs(m), start = src.indexOf('function $unique('), end = src.indexOf('\n', start)
  const unique = new Function(`${src.slice(start, end)}; return $unique;`)() as ((vals: number[], top: number) => number[]) & {buf?: Uint32Array, stamp?: number}
  expect(unique([3, 1, 3, 0], 5)).toEqual([0, 1, 3])
  // Stale marks from an earlier cycle, and the counter one step from the wrap.
  unique.buf = new Uint32Array(8).fill(1)
  unique.stamp = 0xFFFFFFFE
  expect(unique([4, 2], 6)).toEqual([2, 4])
  expect(unique.stamp).toBe(1)
  expect([...unique.buf!]).toEqual([0, 0, 1, 0, 1, 0, 0, 0])
  expect(unique([6], 6)).toEqual([6])
  expect(unique.stamp).toBe(2)
  // A buffer grown for a larger dense range restarts its stamps too; a sparse range takes the Set path and leaves them.
  expect(unique([300, 2], 300)).toEqual([2, 300])
  expect(unique.stamp).toBe(2)
  const dense = Array.from({length: 80}, (_, i) => 3 * i)
  expect(unique(dense, 240)).toEqual(dense)
  expect(unique.stamp).toBe(1)
  expect(unique.buf!.length).toBeGreaterThan(240)
})

test('$breaks marks the stamp buffer directly and agrees with the Set path on dense and sparse inputs', () => {
  const src = compileJs(m), cut = (name: string) => { const start = src.indexOf(`function ${name}(`); return src.slice(start, src.indexOf('\n', start)) }
  const breaks = new Function(`${cut('$unique')}; ${cut('$breaks')}; return $breaks;`)() as (maps: Record<string, Map<number, number>>, reads: [string, number, boolean][], cmps: [number, number, boolean][]) => number[]
  // (the reference: every breakpoint's neighbours −1 .. +2, unique, sorted, then one past the last)
  const reference = (maps: Record<string, Map<number, number>>, reads: [string, number, boolean][], cmps: [number, number, boolean][]) => {
    const p = [0]
    for (const [n, d, minus] of reads) { for (const s of maps[n]!.keys()) { const q = minus ? s + d : s - d; if (q >= 0) p.push(q) } if (minus) p.push(d) }
    for (const [v, d, minus] of cmps) { if (minus) p.push(v + d, d); else if (v >= d) p.push(v - d) }
    const out = [...new Set(p.flatMap(q => [q - 1, q, q + 1, q + 2].filter(x => x >= 0)))].sort((a, b) => a - b)
    return [...out, out[out.length - 1]! + 1]
  }
  let sparse = 0
  for (let trial = 0; trial < 300; trial++) {
    const wide = trial % 5 === 0, maps: Record<string, Map<number, number>> = {}
    for (const name of ['A', 'B']) { const cells = new Map<number, number>(); for (let q = rand(5); q > 0; q--) cells.set(wide ? rand(5000) * 100 : rand(20), 1 + rand(2)); maps[name] = cells }
    const reads: [string, number, boolean][] = Array.from({length: 1 + rand(3)}, () => [rand(2) ? 'A' : 'B', rand(4), rand(2) === 1])
    const cmps: [number, number, boolean][] = Array.from({length: rand(3)}, () => [wide ? rand(100000) : rand(12), rand(4), rand(2) === 1])
    const want = reference(maps, reads, cmps)
    if (want[want.length - 2]! > 16 * (1 + reads.length * 5 + cmps.length * 2) + 64) sparse++
    expect(breaks(maps, reads, cmps)).toEqual(want)
  }
  expect(sparse).toBeGreaterThan(0)
  expect(breaks({A: new Map()}, [], [])).toEqual([0, 1, 2, 3])
  expect(breaks({A: new Map([[5, 1]])}, [['A', 2, false]], [[7, 1, true]])).toEqual([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
})
