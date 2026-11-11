import {expect, test} from 'bun:test'
import {type CountCert, type Goal, type Path, canon, check, leafConstraints} from '../kernel/kernel.ts'
import {clock, counted, fullRate, withWall} from '../kernel/prove.ts'
import {n, x} from './machine.ts'
import {operationRefutation} from './count-row-reindex.ts'
import {rowSymmetryCache, rowSymmetryNames} from './count-row-symmetry.ts'
const request: Pick<CountCert, 'reads' | 'insts'> = {reads: [['ca', 'count', x('a')], ['cb', 'count', x('b')]], insts: [{wit: 'wa', unit: 1, below: n(4), terms: [[1, 'ca']]}, {wit: 'wb', unit: 1, below: n(4), terms: [[1, 'cb']]}]}
const path = (name: string): Path => {const lin = {[name]: -1, '1': 3}; return new Map([[canon(lin), {lin, holds: true}]])}
const run = (f: () => void) => counted(fullRate, () => withWall(performance.now() + 4000, f))
test('symmetry derives a bijection of variables, count reads and witnesses', () => run(() => {
  const names = rowSymmetryNames(request, 'a', 'b', clock() + 1000)!
  expect(names.get('a')).toBe('b'); expect(names.get('cb')).toBe('ca'); expect(names.get('wa')).toBe('wb')
  expect(rowSymmetryNames({...request, reads: request.reads.slice(1)}, 'a', 'b', clock() + 1000)).toBeUndefined()
  expect(rowSymmetryNames({...request, insts: [request.insts[0]!, {...request.insts[1]!, unit: 2}]}, 'a', 'b', clock() + 1000)).toBeUndefined()
  expect(rowSymmetryNames({...request, insts: [request.insts[0]!, {...request.insts[1]!, below: n(5)}]}, 'a', 'b', clock() + 1000)).toBeUndefined()
}))
test('a mirrored linear proof remaps input rows and is checked in its target path', () => run(() => {
  const goal: Goal = {name: 'symmetric', hyps: ['a', 'b'].map(name => ({op: '<=', a: x(name), b: n(2)}))}, before = path('a'), after = path('b')
  const cache = rowSymmetryCache(goal, {reads: [], insts: []}, 'a', 'b', clock() + 1000)!, tree = operationRefutation(leafConstraints(goal, before), 'a')!
  expect(check(goal, tree, before)).toBe(true)
  cache.put(before, tree)
  const mirrored = cache.get(after)
  expect(mirrored).toBeDefined(); expect(check(goal, mirrored!, after)).toBe(true)
  cache.put(before, {leaf: []}); expect(cache.get(after)).toBeUndefined()
}))
test('deferred symmetry transport returns only an unchecked candidate, not a verdict', () => run(() => {
  const goal: Goal = {name: 'symmetric', hyps: ['a', 'b'].map(name => ({op: '<=', a: x(name), b: n(2)}))}, before = path('a'), after = path('b')
  const cache = rowSymmetryCache(goal, {reads: [], insts: []}, 'a', 'b', clock() + 1000, undefined, true)!
  cache.put(before, {leaf: []})
  const candidate = cache.get(after)
  expect(candidate).toBeDefined(); expect(check(goal, candidate!, after)).toBe(false)
}))

test('an asymmetric goal or expired allowance cannot reuse a verdict', () => run(() => {
  const goal: Goal = {name: 'asymmetric', hyps: [{op: '<=', a: x('a'), b: n(2)}, {op: '<=', a: x('b'), b: n(10)}]}, before = path('a')
  const cache = rowSymmetryCache(goal, {reads: [], insts: []}, 'a', 'b', clock() + 1000)!
  cache.put(before, operationRefutation(leafConstraints(goal, before), 'a')!)
  expect(cache.get(path('b'))).toBeUndefined()
  expect(rowSymmetryCache(goal, request, 'a', 'b', clock() - 1)).toBeUndefined()
}))
