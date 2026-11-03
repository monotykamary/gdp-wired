import {expect, test} from 'bun:test'
import {bitIntersection, bitIntersects} from './bitsets.ts'

test('sample intersections preserve unsigned high bits and do not mutate inputs', () => {
  const a = new Uint32Array([0x80000000, 1, 0]), b = new Uint32Array([0x80000000, 0, 2])
  expect([...bitIntersection(a, b)]).toEqual([0x80000000, 0, 0])
  expect(bitIntersects([a, b])).toBe(true)
  expect([...a]).toEqual([0x80000000, 1, 0])
  expect([...b]).toEqual([0x80000000, 0, 2])
  expect(bitIntersects([a, b, new Uint32Array([0, 1, 2])])).toBe(false)
  expect(bitIntersects([new Uint32Array(0)])).toBe(false)
  expect(bitIntersects([])).toBe(false)
})

test('existence agrees with exhaustive sample rows, including nonminimal cubes', () => {
  let seed = 7
  const next = () => (seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0)
  for (const n of [1, 31, 32, 33, 65, 257]) {
    const sets = Array.from({length: 8}, () => {
      const bits = new Uint32Array(Math.ceil(n / 32))
      for (let i = 0; i < n; i++) if ((next() >>> 24) < 100) bits[i >> 5]! |= 1 << (i & 31)
      return bits
    })
    for (let mask = 1; mask < 256; mask++) {
      const chosen = sets.filter((_, i) => mask & (1 << i))
      const expected = Array.from({length:n}, (_, i) => chosen.every(b => !!(b[i >> 5]! & (1 << (i & 31))))).some(Boolean)
      expect(bitIntersects(chosen)).toBe(expected)
      expect(bitIntersects([chosen.slice(1).reduce(bitIntersection, chosen[0]!)])).toBe(expected)
    }
  }
})
