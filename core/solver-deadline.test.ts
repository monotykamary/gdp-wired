import {expect, test} from 'bun:test'
import {type Constraint, costs, solve, work} from './solver.ts'
const rows: Constraint[] = [
  {lin: {a: 1, b: -1}, label: 'a <= b'},
  {lin: {b: 1, c: -1}, label: 'b <= c'},
  {lin: {c: 1, a: -1, '1': 1}, label: 'c < a'}
]
test('an expired optional stop reads and charges no input rows', () => {
  const before = work.n
  expect(solve(rows, 2000, true, () => false)).toEqual({kind: 'unknown'})
  expect(work.n).toBe(before)
})
test('an optional stop is consulted again after input admission', () => {
  let checks = 0
  expect(solve(rows, 2000, true, () => ++checks < 2)).toEqual({kind: 'unknown'})
  expect(checks).toBe(2)
})
test('an unexhausted optional stop preserves every verdict, step and work charge', () => {
  const run = (more?: () => boolean) => {
    const before = {...costs}, start = work.n, verdict = solve(rows, 2000, true, more)
    return {verdict, work: work.n - start, costs: Object.fromEntries(Object.entries(costs).map(([key, value]) => [key, value - before[key as keyof typeof costs]]))}
  }
  const original = run(), bounded = run(() => true)
  expect(original.verdict.kind).toBe('refuted')
  expect(bounded).toEqual(original)
})
