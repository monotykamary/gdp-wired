import {expect, test} from 'bun:test'
import {type Constraint} from './solver.ts'
import {type Goal, check, leafConstraints} from '../kernel/kernel.ts'
import {n, same, x} from './machine.ts'
import {countRowReindexer, operationRefutation} from './count-row-reindex.ts'
const row = (lin: Constraint['lin'], src?: Constraint['src']): Constraint => ({lin, label: '', ...(src ? {src} : {})})
test('origin hints reindex reordered hypotheses and appended product rows exactly', () => {
  const h = same(x('value'), n(1)), source: Goal = {name: 'source', hyps: [h]}, target: Goal = {name: 'target', hyps: [same(x('other'), n(0)), h]}
  const before = [row({value: 1, '1': -1}, {fact: 0})], after = [row({other: 1}, {fact: 0}), row({value: 1, '1': -1}, {fact: 1})], index = countRowReindexer(target)(source, before, after)
  expect(index(0)).toBe(1)
  expect(index(1)).toBe(2)
  expect(index(-1)).toBeUndefined()
  expect(index(0.5)).toBeUndefined()
})
test('wrong origin tags cannot substitute a different linear row', () => {
  const goal: Goal = {name: 'same', hyps: [same(x('v'), n(0))]}, reindex = countRowReindexer(goal)
  const before = [row({v: 1}, {fact: 0})], wrong = [row({v: -1}, {fact: 0})]
  expect(reindex(goal, before, wrong)(0)).toBeUndefined()
  expect(reindex(goal, before, [...wrong, row({v: 1}, {atom: 4})])(0)).toBe(1)
})
test('path, natural, term and pair rows are matched by their actual forms', () => {
  const goal: Goal = {name: 'empty', hyps: []}, before = [row({a: -1}, {nat: 'a'}), row({term: 1}, {term: 'term'}), row({a: 1, b: -1}, {pair: ['a', 'b']}), row({move: 1}, {atom: 1})], after = [...before].reverse()
  const index = countRowReindexer(goal)(goal, before, after)
  expect(before.map((_, i) => index(i))).toEqual([3, 2, 1, 0])
})
test('offset mode validates demanded rows when reusing a layout', () => {
  const goal: Goal = {name: 'same', hyps: [same(x('v'), n(0))]}, stats = {hits: 0, layouts: 0}, reindex = countRowReindexer(goal, {offsets: true, stats})
  expect(reindex(goal, [row({v: 1}, {fact: 0})], [row({v: 1}, {fact: 0})])(0)).toBe(0)
  // A matching origin-tag layout is not enough when a branch changes the row.
  expect(reindex(goal, [row({v: 1}, {fact: 0})], [row({v: -1}, {fact: 0})])(0)).toBeUndefined()
  expect(stats).toEqual({hits: 1, layouts: 1})
})
test('a reused layout refreshes the demanded index when same-origin rows swap', () => {
  const goal: Goal = {name: 'empty', hyps: []}, index = countRowReindexer(goal, {offsets: true})
  const first = [row({a: 1}, {atom: 1}), row({b: 1}, {atom: 2})]
  expect(index(goal, first, first)(0)).toBe(0)
  const swapped = [row({b: 1}, {atom: 1}), row({a: 1}, {atom: 2})]
  expect(index(goal, first, swapped)(0)).toBe(1)
  expect(index(goal, first, swapped)(1)).toBe(0)
})
test('operation interval refutations are ordinary checked linear proofs', () => {
  const goal: Goal = {name: 'impossible operation', hyps: [{op: '<=', a: n(7), b: x('move')}, {op: '<', a: x('move'), b: n(7)}]}, tree = operationRefutation(leafConstraints(goal, new Map()), 'move')
  expect(tree).toBeDefined()
  expect(check(goal, tree!)).toBe(true)
  const possible: Goal = {name: 'possible', hyps: [{op: '<=', a: n(6), b: x('move')}, {op: '<', a: x('move'), b: n(7)}]}
  expect(operationRefutation(leafConstraints(possible, new Map()), 'move')).toBeUndefined()
  expect(operationRefutation(leafConstraints(goal, new Map()), 'different')).toBeUndefined()
})
