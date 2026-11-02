import {describe, expect, test} from 'bun:test'
import {samplePredicates} from './sample-cache.ts'

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
