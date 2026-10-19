// Folds over trees as values (core/dsl.ts fold, the kernel's Fold; children, nodes with any number of children, as a
// binary fold): proven by induction over the tree, broken variants refused, run on runtime trees by the terms proven, the builders cross-checked against those terms.
import {expect, test} from 'bun:test'
import {fold, max, nat, proveFold} from './dsl.ts'
import {orgChart, orgChartLaws, rollup, rollupLaws, signoffLaws, signoffs} from '../examples/folds.ts'

test('folds proven by induction over trees; the broken variants refused; the builders cross-checked', () => {
  for (const [f, laws] of [[rollup(), rollupLaws], [signoffs(), signoffLaws]] as const) {
    const ls = laws(f as never)
    expect(proveFold(f as never, ls)).toMatchObject({proven: true, checked: true})
    expect((f as ReturnType<typeof rollup>).crossCheck(ls).failure).toBeUndefined()
  }
  expect(proveFold(rollup('caps the leaves only'), rollupLaws(rollup('caps the leaves only'))).proven).toBe(false)
  expect(proveFold(signoffs('ignores the node\'s own sign-off'), signoffLaws(signoffs('ignores the node\'s own sign-off'))).proven).toBe(false)
})

test('runtime trees: each value by the terms the kernel proved', () => {
  const chart = {node: {spend: 50}, left: {leaf: {spend: 5}}, right: {node: {spend: 70}, left: {leaf: {spend: 1}}, right: {leaf: {spend: 9}}}}
  expect(rollup().run(chart, {cap: 40})).toEqual({total: 5 + 40 + 1 + 9 + 40, teams: 5, depth: 2})
  const doc = (a: boolean, b: boolean, c: boolean) => ({node: {signed: a}, left: {leaf: {signed: b}}, right: {leaf: {signed: c}}})
  expect(signoffs().run(doc(true, true, true))).toEqual({approved: 1, sections: 3, signedCount: 3})
  expect(signoffs().run(doc(false, true, true))).toEqual({approved: 0, sections: 3, signedCount: 2})
  expect(() => rollup().run({leaf: {spend: -1}}, {cap: 1})).toThrow(RangeError)
  const capped = fold('capped').inputs({x: nat}).assume(({x}) => x.atMost(10)).leaf(({x}) => ({v: x})).node((_, l, r) => ({v: l.v.plus(r.v)}))
  expect(() => capped.run({node: {x: 1}, left: {leaf: {x: 11}}, right: {leaf: {x: 1}}})).toThrow(/assumption/)
})

test('nodes with any number of children: proven as a binary fold, run on rose trees, cross-checked', () => {
  const f = orgChart(), laws = orgChartLaws(f)
  expect(proveFold(f, laws)).toMatchObject({proven: true, checked: true})
  expect(f.crossCheck(laws).failure).toBeUndefined()
  expect(proveFold(orgChart('caps the reports only'), orgChartLaws(orgChart('caps the reports only'))).proven).toBe(false)
  // A manager with three reports, one of them managing two, and one with none.
  const chart = {node: {pay: 90}, children: [{leaf: {pay: 30}}, {node: {pay: 60}, children: [{leaf: {pay: 10}}, {leaf: {pay: 70}}]}, {node: {pay: 5}, children: []}]}
  expect(f.run(chart, {cap: 50})).toEqual({cost: 50 + 30 + 50 + 10 + 50 + 5, heads: 6, depth: 2})
  expect(f.run({node: {pay: 7}, children: []}, {cap: 50})).toEqual({cost: 7, heads: 1, depth: 0})
  // Without the lemma about the reports' depth, the chart's law about depth isn't proven: the children's values say
  // nothing about their depth.
  const bare = fold('bare chart').inputs({pay: nat}).leaf(() => ({heads: 1, depth: 0}))
    .children({heads: 0, depth: 0}, (acc, kid) => ({heads: acc.heads.plus(kid.heads), depth: max(acc.depth, kid.depth.plus(1))}))
    .node((_, kids) => ({heads: kids.heads.plus(1), depth: kids.depth}))
  expect(proveFold(bare, [bare.law('as wide as deep', ({depth, heads}) => depth.lt(heads))]).proven).toBe(false)
})
