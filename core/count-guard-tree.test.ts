import {expect, test} from 'bun:test'
import {same, x, n} from './machine.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {clock} from '../kernel/prove.ts'
import {type Path, type Tree, canon} from '../kernel/kernel.ts'
const leaf = (): Tree => ({leaf: []})
test('scalar guard splits cover both equality outcomes', () => {
  const yes: Path[] = [], no: Path[] = [], tree = countGuardTree(clock() + 100).condition(same(x('position'), n(3)), new Map(), p => {yes.push(p); return leaf()}, p => {no.push(p); return leaf()})
  expect(tree && 'split' in tree).toBe(true)
  expect(yes).toHaveLength(1); expect(no).toHaveLength(2)
  expect([...yes[0]!.values()].every(a => a.holds)).toBe(true)
})
test('disjoint rows are proved once above a case split', () => {
  const split = countGuardTree(clock() + 100), row = {bound: 1, '1': -2}; let probes = 0, arms = 0
  const tree = split.hoist([{row, reject: () => {probes++; return leaf()}}], [same(x('case'), n(0))], new Map(), p => {
    expect(p.get(canon(row))?.holds).toBe(true)
    return split.condition(same(x('case'), n(0)), p, () => {arms++; return leaf()}, () => {arms++; return leaf()})
  })
  expect(tree).toBeDefined(); expect(probes).toBe(1); expect(arms).toBe(3)
})
test('two-sided aliases prevent an apparently disjoint hoist', () => {
  const a = {a: 1, b: -1}, b = {a: -1, b: 1}, path: Path = new Map([[canon(a), {lin: a, holds: true}], [canon(b), {lin: b, holds: true}]])
  let probes = 0
  const tree = countGuardTree(clock() + 100).hoist([{row: {a: 1}, reject: () => {probes++; return leaf()}}], [same(x('b'), n(0))], path, leaf)
  expect(tree).toBeDefined(); expect(probes).toBe(0)
})
test('an unproved complement never becomes a hoisted assumption', () => {
  const row = {bound: 1}; let probes = 0
  const tree = countGuardTree(clock() + 100).hoist([{row, reject: () => {probes++; return undefined}}], [same(x('case'), n(0))], new Map(), p => {expect(p.has(canon(row))).toBe(false); return leaf()})
  expect(tree).toBeDefined(); expect(probes).toBe(1)
})
test('expired and unsupported guards do not silently select an arm', () => {
  let called = false
  expect(countGuardTree(clock() - 1).condition(same(x('x'), n(0)), new Map(), () => {called = true; return leaf()}, leaf)).toBeUndefined()
  expect(called).toBe(false)
  expect(countGuardTree(clock() + 100).condition({op: 'flag', name: 'opaque'}, new Map(), leaf, leaf)).toBeUndefined()
})
