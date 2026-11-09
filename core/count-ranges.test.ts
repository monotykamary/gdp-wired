import {expect, test} from 'bun:test'
import {get, ite, n, same, x} from './machine.ts'
import {type CountDecl, type MapRead, checkCounted, countedGoal} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'
import {modelSequence} from '../kernel/model-sequence.ts'
import {countsForReads} from './count-facts.ts'
import {rangeInstances, rangeViolations, zeroOne} from './count-ranges.ts'

const bit = (c: Parameters<typeof ite>[0]) => ite(c, n(1), n(0))
// A stored row's cardinality (0/1 body over the keys below size) and a count that sums values (not 0/1).
const ds: CountDecl[] = [
  {map: 'rowSize', j: 'a', key: 'k', below: x('size'), body: bit(same(get('Config', {op: 'add', a: {op: 'mul', k: 64, a: x('a')}, b: x('k')}), n(1)))},
  {map: 'rowSize#', j: 'a', key: 'k', below: x('size'), body: bit(same(get('Config#', {op: 'add', a: {op: 'mul', k: 64, a: x('a')}, b: x('k')}), n(1)))},
  {map: 'weight', j: 'a', key: 'k', below: x('size'), body: get('CT', x('k'))},
]
const reads: MapRead[] = [['r$0', 'rowSize', x('b')], ['r$1', 'rowSize#', x('a')], ['r$2', 'weight', x('b')]]

test('zeroOne recognizes 0/1 bodies and nothing else', () => {
  expect(zeroOne(bit(same(x('v'), n(1))))).toBe(true)
  expect(zeroOne(ite(same(x('v'), n(1)), n(1), ite(same(x('w'), n(2)), n(0), n(1))))).toBe(true)
  expect(zeroOne(n(2))).toBe(false)
  expect(zeroOne(get('CT', x('k')))).toBe(false)
  expect(zeroOne(ite(same(x('v'), n(1)), n(1), n(2)))).toBe(false)
})

test('one range instance per 0/1-bodied read, fresh witnesses, present ranges and non-0/1 bodies skipped', () => {
  const out = rangeInstances(ds, reads, ['w$range$0', 'size'])
  expect(out.map(i => [i.terms, i.unit, i.wit])).toEqual([[[[1, 'r$0']], -1, 'w$range$1'], [[[1, 'r$1']], -1, 'w$range$2']])
  expect(out.every(i => JSON.stringify(i.below) === JSON.stringify(x('size')))).toBe(true)
  const again = rangeInstances(ds, reads, [], [out[0]!])
  expect(again.map(i => i.terms[0]![1])).toEqual(['r$1'])
  expect(again[0]!.wit).not.toBe(out[0]!.wit)
  expect(rangeInstances(ds, [reads[2]!], [])).toEqual([])
})

// The 16-cell witness of T-14 (Inv2973-half, pass 1): size 1 and every row count at 2. With the range instances the goal
// has no model; without them it has.
test('a row count above its universe is refuted once its range instance is in the goal', () => {
  const counts = countsForReads(ds, reads)!
  const hyps = [same(x('size'), n(1)), {op: '<=' as const, a: n(2), b: x('r$1')}, {op: '<=' as const, a: n(2), b: x('r$0')}]
  const ranges = rangeInstances(ds, reads, ['size', 'a', 'b'])
  const g = {name: 'row count above its universe', hyps, counts}
  const withRanges = countedGoal(g, ranges)!, without = countedGoal(g, [])!
  const proof = grow(withRanges, new Map(), {nodes: 0, until: clock() + 2000})
  expect('tree' in proof).toBe(true)
  if ('tree' in proof) expect(checkCounted(g, {insts: ranges, tree: proof.tree})).toBe(true)
  const model = modelSequence(new Map())(without, clock() + 500)
  expect('tree' in model).toBe(false)
  if (!('tree' in model)) expect(model.stuck).toBe('sat')
})

test('a narrowed certificate still needs the complete read pool for replay range demand', () => {
  const selected = {reads: [reads[0]!], insts: []}
  const replay = {c: selected, all: reads}
  const witness = {size: 1, r$0: 1, r$1: 2}
  expect(rangeViolations(ds, replay.c.reads, witness)).toEqual([])
  const demanded = rangeViolations(ds, replay.all, witness)
  expect(demanded).toEqual([reads[1]!])
  expect(rangeInstances(ds, demanded, ['size']).map(i => i.terms)).toEqual([[[1, 'r$1']]])
  expect(replay.c).toBe(selected)
})

test('unsupported map and conditional bounds stay unknown even when scalar values are present', () => {
  for (const below of [get('Limits', n(0)), ite(same(x('size'), n(1)), n(1), n(2))]) {
    expect(rangeViolations([{...ds[0]!, below}], [reads[0]!], {size: 1, r$0: 3})).toEqual([])
  }
})

test('rangeViolations names the reads a model puts above their evaluated bound, nothing it leaves open', () => {
  // The T-14 witness: size 1, every row count at 2.
  expect(rangeViolations(ds, reads, {size: 1, r$0: 2, r$1: 2, r$2: 2}).map(r => r[0])).toEqual(['r$0', 'r$1'])
  expect(rangeViolations(ds, reads, {size: 3, r$0: 2, r$1: 3, r$2: 9})).toEqual([])
  expect(rangeViolations(ds, reads, {r$0: 2, r$1: 2})).toEqual([])
  expect(rangeViolations(ds, reads, {size: 1, r$1: 2}).map(r => r[0])).toEqual(['r$1'])
  const sized: CountDecl[] = [{...ds[0]!, below: {op: 'add', a: x('size'), b: n(1)}}]
  expect(rangeViolations(sized, [reads[0]!], {size: 1, r$0: 3}).map(r => r[0])).toEqual(['r$0'])
  expect(rangeViolations(sized, [reads[0]!], {size: 1, r$0: 2})).toEqual([])
})
