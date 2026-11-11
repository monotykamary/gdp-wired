import {expect, test} from 'bun:test'
import {all, any, n, not, x} from './machine.ts'
import {type Goal, check} from '../kernel/kernel.ts'
import {clock, counted, fullRate, withWall} from '../kernel/prove.ts'
import {countQueryConjuncts, proveCountQuery} from './count-query.ts'
const le = {op: '<=' as const, a: x('renamed_value'), b: n(0)}, gt = {op: '<' as const, a: n(0), b: x('renamed_value')}
const run = (f: () => void) => counted(fullRate, () => withWall(performance.now() + 2000, f))
test('minimal count queries reindex ordinary trees to the complete goal', () => run(() => {
  const minimal: Goal = {name: 'small', hyps: [le, gt]}, goal: Goal = {name: 'full', hyps: [{op: '<=', a: n(0), b: x('irrelevant')}, gt, le]}, events: Record<string, unknown>[] = []
  const tree = proveCountQuery(goal, new Map(), clock() + 1000, {query: 'transport', minimal, trace: e => events.push(e)})
  expect(tree).toBeDefined(); expect(check(goal, tree!)).toBe(true)
  expect(events.map(e => e.mode)).toEqual(['minimal'])
}))
test('only a satisfiable minimal view falls back to the full query', () => run(() => {
  const goal: Goal = {name: 'full', hyps: [le, gt]}, minimal: Goal = {name: 'small', hyps: [le]}, events: Record<string, unknown>[] = []
  const tree = proveCountQuery(goal, new Map(), clock() + 1000, {query: 'fallback', minimal, trace: e => events.push(e)})
  expect(tree).toBeDefined(); expect(check(goal, tree!)).toBe(true)
  expect(events.map(e => [e.mode, e.outcome])).toEqual([['minimal', 'sat'], ['full', 'proposed']])
}))
test('a reduced proof requiring an unavailable premise is refused', () => run(() => {
  const goal: Goal = {name: 'false', hyps: [le]}, minimal: Goal = {name: 'invented', hyps: [le, gt]}, events: Record<string, unknown>[] = []
  expect(proveCountQuery(goal, new Map(), clock() + 1000, {query: 'missing premise', minimal, trace: e => events.push(e)})).toBeUndefined()
  expect(events.map(e => e.outcome)).toEqual(['transport-rejected'])
}))
test('a zero leaf allowance cannot be renewed by minimal/full fallback', () => run(() => {
  const goal: Goal = {name: 'leaf exhausted', hyps: [le, gt]}, minimal: Goal = {name: 'small', hyps: [le]}, events: Record<string, unknown>[] = []
  expect(proveCountQuery(goal, new Map(), clock() + 1000, {query: 'capped', minimal, leafUnits: 0, trace: e => events.push(e)})).toBeUndefined()
  expect(events).toMatchObject([{query: 'capped', mode: 'minimal', outcome: 'leaf-cap', hyps: 1, fullHyps: 2, units: 0}])
}))

test('a direct linear proof cannot outlive a small positive leaf allowance', () => run(() => {
  const goal: Goal = {name: 'direct cap', hyps: [
    {op: '<=', a: x('a'), b: x('b')},
    {op: '<=', a: x('b'), b: x('c')},
    {op: '<', a: x('c'), b: x('a')}
  ]}, events: Record<string, unknown>[] = []
  expect(proveCountQuery(goal, new Map(), clock() + 1000, {query: 'direct', direct: true, leafUnits: 1e-9, trace: e => events.push(e)})).toBeUndefined()
  expect(events.map(e => e.outcome)).toEqual(['leaf-cap'])
}))

test('expired count query does not search or record a fabricated result', () => run(() => {
  const goal: Goal = {name: 'expired', hyps: [le, gt]}, events: Record<string, unknown>[] = []
  expect(proveCountQuery(goal, new Map(), clock() - 1, {query: 'expired', minimal: goal, trace: e => events.push(e)})).toBeUndefined()
  expect(events).toHaveLength(0)
}))

test('minimal projections retain domain conjuncts under a negated disjunction', () => {
  const domain = {op: '<' as const, a: x('row'), b: x('size')}, guarded = any(not(domain), le)
  expect(countQueryConjuncts(not(guarded))).toEqual([domain, not(le)])
  expect(countQueryConjuncts(all(le, gt))).toEqual([le, gt])
  expect(countQueryConjuncts(any(le, gt))).toEqual([any(le, gt)])
})
