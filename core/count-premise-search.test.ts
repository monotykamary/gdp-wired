import {expect, test} from 'bun:test'
import {type Law, n, same} from './machine.ts'
import {type CountPremiseContext} from './count-premise-view.ts'
import {countPremiseSearch} from './count-premise-search.ts'
import {BudgetExpired, checkBudget, clock, counted, fullRate, withBudget} from '../kernel/prove.ts'
import {costs} from './solver.ts'

const family: Law[] = ['left', 'right', 'unrelated'].map(name => ({name, holds: same(n(0), n(0))}))
const view = (indices = [0, 1]): CountPremiseContext => ({laws: indices.map(i => family[i]!), selected: indices, omitted: [2], allowed: [], guardReads: false})
const bounded = (run: () => void) => {const before = costs.fm; try {counted(fullRate, () => withBudget(1000000, run), true)} finally {costs.fm = before}}

test('a checked local result wins; an unchecked proposal never does', () => bounded(() => {
  let full = 0
  const result = countPremiseSearch(family, clock() + 100, () => [view()], local => {if (local === family) full++; return 'proposal'}, (_c, result) => result === 'proposal' ? 'checked' : undefined)
  expect(result).toBe('checked'); expect(full).toBe(0)
  const rejected = countPremiseSearch(family, clock() + 100, () => [view()], local => local === family ? 'full' : 'fake proof', () => undefined)
  expect(rejected).toBe('full')
}))
test('a local refutation or unknown always falls back, and genuine full refutation survives', () => bounded(() => {
  for (const localResult of ['sat', 'unknown']) {
    const calls: number[] = []
    const result = countPremiseSearch(family, clock() + 100, () => [view(), view()], local => {calls.push(local.length); return local === family ? 'full refuted' : localResult}, () => undefined)
    expect(result).toBe('full refuted'); expect(calls).toEqual([2, 3])
  }
}))
test('integer-charge local expiration leaves a positive full-context reserve', () => bounded(() => {
  const end = clock() + 10, calls: number[] = []
  const result = countPremiseSearch(family, end, () => [view()], (local, stop) => {
    calls.push(local.length)
    if (local !== family) {while (clock() <= stop) costs.fm++; checkBudget('local containment'); throw new BudgetExpired('local containment')}
    expect(clock()).toBeLessThan(end); return 'full'
  }, () => undefined)
  expect(result).toBe('full'); expect(calls).toEqual([2, 3])
}))
test('selection exhaustion also returns to full context', () => bounded(() => {
  const end = clock() + 10
  expect(countPremiseSearch(family, end, stop => {while (clock() <= stop) costs.fm++; checkBudget('selection'); throw new BudgetExpired('selection')}, local => {expect(local).toBe(family); expect(clock()).toBeLessThan(end); return 'full'}, () => undefined)).toBe('full')
}))
test('an exact local endpoint cannot return an unchecked local result', () => bounded(() => {
  const end = clock() + 4, calls: number[] = []
  expect(countPremiseSearch(family, end, () => [view()], (local, stop) => {calls.push(local.length); if (local !== family) while (clock() < stop) costs.fm++; return local === family ? 'full' : 'unchecked'}, () => 'accepted')).toBe('full')
  expect(calls).toEqual([2, 3])
}))
test('an explicitly unsupported local proposal cannot suppress the full fallback', () => bounded(() => {
  const unsupported = new Error('unsupported proposal'), calls: number[] = []
  const result = countPremiseSearch(family, clock() + 100, () => [view()], local => {
    calls.push(local.length); if (local !== family) throw unsupported; return 'full'
  }, () => undefined, undefined, error => error === unsupported)
  expect(result).toBe('full'); expect(calls).toEqual([2, 3])
}))
test('outer expiration and unrelated exceptions propagate unchanged', () => bounded(() => {
  const unrelated = new Error('not a budget')
  expect(() => countPremiseSearch(family, clock() + 100, () => [view()], () => {throw unrelated}, () => undefined)).toThrow(unrelated)
  expect(() => withBudget(1, () => countPremiseSearch(family, clock() + 100, () => [view()], () => {costs.fm += 2; checkBudget('outer'); throw new BudgetExpired('outer')}, () => undefined))).toThrow(BudgetExpired)
}))
