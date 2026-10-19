// Folds over trees as values (core/dsl.ts fold, the kernel's Fold): proven by induction over the tree, broken variants
// refused, run on runtime trees by the terms proven, the builders cross-checked against those terms.
import {expect, test} from 'bun:test'
import {fold, nat, proveFold} from './dsl.ts'
import {rollup, rollupLaws, signoffLaws, signoffs} from '../examples/folds.ts'

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
