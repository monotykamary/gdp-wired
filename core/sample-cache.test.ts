import {describe, expect, test} from 'bun:test'
import {samplePredicates, sampleStateText} from './sample-cache.ts'
import {type Machine, type State, atMost, get, interpret, n, tuple, x} from './machine.ts'
import {domainStep} from './infer.ts'

test('relational sampling shares unchanged maps and states without mutating earlier samples', () => {
  const m: Machine = {name: 'persistent relational samples', params: ['size'], inputs: ['a','b','v'], state: {phase: n(0)}, maps: {R: 0, P: 0, U: 2}, relations: {R: ['Node','Node']}, assume: atMost(n(0), x('v')),
    step: {state: {phase: x('v')}, maps: {R: {each: 'k', value: {op: 'if', c: {op: '=', a: x('k'), b: tuple([x('a'),x('b')])}, then: x('v'), else: get('R',x('k'))}}, P: {key: x('a'), value: x('v')}}}}
  const params = {size: 3}, run = interpret(m), step = domainStep(m)!, start = run.init(params), noop = {a: 0, b: 1, v: 0}
  const warm = step(params,start,noop)!
  expect(warm).not.toBe(start) // The first bulk step adds default metadata.
  expect(step(params,warm,noop)).toBe(warm)
  let a = warm, b = run.step(params,start,noop), reused = 0
  for (let i = 0; i < 128; i++) {
    const request = {a: i % 3, b: (i + 1) % 3, v: (i >> 2) % 2}, before = sampleStateText(params,a,m.maps!)
    const next = step(params,a,request)!
    if (next === a) reused++
    expect(sampleStateText(params,a,m.maps!)).toBe(before)
    expect(next.maps.U).toBe(a.maps.U)
    a = next; b = run.step(params,b,request)
    expect(sampleStateText(params,a,m.maps!)).toBe(sampleStateText(params,b,m.maps!))
  }
  expect(reused).toBeGreaterThan(0)
  expect(step(params,start,{...noop,v:-1})).toBeUndefined()
  const bulk: Machine = {...m, step: {maps: {R: {each: 'k', value: n(1)}}}}, old = {...start, defaults: {R: 0}}
  const changed = domainStep(bulk)!(params,old,noop)!
  expect(changed).not.toBe(old)
  expect(changed.defaults!.R).toBe(1)
  expect(old.defaults.R).toBe(0)
})

test('sample state keys preserve the nested-array oracle, defaults, ordering and unusual numbers', () => {
  const values = [0, -0, 1, -2, 1e21, NaN, Infinity, -Infinity], defaults = {A: 0, B: 1}
  for (let seed = 0; seed < 128; seed++) {
    const params = {size: seed % 5}, st: State = {scalars: {phase: seed % 2}, maps: {A: new Map(), B: new Map()}, ...(seed % 2 ? {defaults: {A: values[seed % values.length]!}} : {})}
    for (let i = 11; i >= 0; i--) { st.maps.A!.set(i - 3, values[(seed + i) % values.length]!); st.maps.B!.set(i * 2, values[(seed * 3 + i) % values.length]!) }
    const oracle = JSON.stringify([params, st.scalars, Object.entries(st.maps).map(([mp, cells]) => {
      const d = st.defaults?.[mp] ?? defaults[mp as keyof typeof defaults] ?? 0
      return [...cells].filter(([, v]) => v !== d).map(([k, v]) => [k, v]).sort((a, b) => a[0]! - b[0]!)
    }), st.defaults ?? null])
    expect(sampleStateText(params, st, defaults)).toBe(oracle)
  }
  expect(sampleStateText({}, {scalars: {}, maps: {}}, {})).toBe('[{},{},[],null]')
})

describe('sample predicate sharing', () => {
  test('equal literals share only evaluated rows, including false values', () => {
    let calls = 0
    const t = samplePredicates([[{n: 2}, {n: 3}], [{n: 2}]], p => `${p.n}`, (p, row: number) => { calls++; return row >= p.n })
    expect(t.groups).toEqual([[0, 1], [0]])
    const holds = t.on([1, 2, 3])
    expect(calls).toBe(0)
    expect(holds(0, 0)).toBe(false)
    expect(holds(0, 0)).toBe(false)
    expect(holds(0, 1)).toBe(true)
    expect(holds(0, 1)).toBe(true)
    expect(calls).toBe(2)
    expect(holds(1, 1)).toBe(false)
    expect(calls).toBe(3)
    expect(t.on([3])(0, 0)).toBe(true)
    expect(calls).toBe(4)
  })
  test('preserves first-hit and preceding near misses against direct evaluation', () => {
    const groups = [[0, 1], [0, 1, 2], [0, 2], [1, 2, 3], [], [3, 0, 2]]
    const rows = Array.from({length: 16}, (_, i) => i)
    const raw = (p: number, row: number) => !!(row & (1 << p))
    const table = samplePredicates(groups, String, raw), holds = table.on(rows)
    const scan = (ls: number[], f: (p: number, row: number) => boolean) => {
      let near = 0
      for (let ri = 0; ri < rows.length; ri++) {
        let off = 0
        for (const p of ls) if (!f(p, ri) && ++off > 1) break
        if (!off) return {hit: ri, near}
        if (off === 1) near++
      }
      return {hit: -1, near}
    }
    expect(table.groups.map(ls => scan(ls, holds))).toEqual(groups.map(ls => scan(ls, (p, ri) => raw(p, rows[ri]!))))
  })
})
