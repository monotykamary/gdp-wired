// Tables of nodes (core/dsl.ts nodes): a tree, or lists of lists, in a rule's state, each node made one a step from nodes
// already there, its folds kept with it. examples/trees.ts proven and its broken variants refused, the table's own laws
// proven beside the rule's, the builders cross-checked, the compiled rule run and its state decoded.
import {expect, test} from 'bun:test'
import {nat, proveSteps, record, rule} from './dsl.ts'
import {searchTree, searchTreeLaws, sheet, sheetLaws} from '../examples/trees.ts'

test('a search tree and a sheet of lists: proven, cross-checked, the broken variants refused', () => {
  for (const [r, laws] of [[searchTree(), searchTreeLaws], [sheet(), sheetLaws]] as const) {
    const ls = laws(r as never)
    expect(proveSteps(r, ls, [])).toMatchObject({proven: true, checked: true})
    expect((r as ReturnType<typeof sheet>).crossCheck(ls, []).failure).toBeUndefined()
  }
  expect(proveSteps(searchTree('checks the left side only'), searchTreeLaws(searchTree('checks the left side only')), []).proven).toBe(false)
  expect(proveSteps(sheet('starts a row at a cell not made yet'), sheetLaws(sheet('starts a row at a cell not made yet')), []).proven).toBe(false)
  expect(searchTree().kindLaws().map(l => l.name)).toEqual(["every Tree node's children are earlier nodes", "every Tree node's folds are its children's", 'nothing in Tree past its end'])
}, 120_000)

test('the compiled rule: nodes made from nodes already there, folds kept, the state decoded', () => {
  const t = searchTree(), g = t.compiled()
  let st = g.init({})
  // 5 and 9 alone, 7 between them; 3 above the 5 on its left is refused; 8 between 5 and 9 is made.
  for (const q of [{key: 5, l: 0, r: 0}, {key: 9, l: 0, r: 0}, {key: 7, l: 1, r: 2}, {key: 3, l: 1, r: 0}, {key: 8, l: 1, r: 2}, {key: 1, l: 9, r: 0}]) st = g.step({}, st, t.encodeInput(q))
  expect(t.decode(st)).toMatchObject({Tree_size: 4, Tree: [{value: {key: 5}, left: 0, right: 0}, {value: {key: 9}, left: 0, right: 0}, {value: {key: 7}, left: 1, right: 2}, {value: {key: 8}, left: 1, right: 2}]})
  expect([...st.maps['Tree$lo']!].filter(([, x]) => x)).toEqual([[1, 5], [2, 9], [3, 5], [4, 5]])
  const s = sheet(), gs = s.compiled(), ps = s.encodeParams({cap: 10})
  let ss = gs.init(ps)
  for (const q of [{op: 'cell', amount: 4, at: 0, next: 0}, {op: 'cell', amount: 30, at: 0, next: 1}, {op: 'row', amount: 0, at: 2, next: 0}, {op: 'cell', amount: 7, at: 0, next: 0}, {op: 'row', amount: 0, at: 3, next: 1}] as const) ss = gs.step(ps, ss, s.encodeInput(q))
  expect([...ss.maps['Row$total']!]).toEqual([[1, 14], [2, 21]]) // row 1: cells 2, 1 (10 capped, 4); row 2: cell 3 (7), then row 1
  expect(s.decode(ss)).toMatchObject({Cell_size: 3, Row_size: 2})
})

test('names are checked', () => {
  expect(() => rule('x').nodes('T', record({a: nat}), ['value'])).toThrow(/can't name a child/)
  expect(() => rule('x').nodes('T', record({a: nat}), ['l', 'l'])).toThrow(/given twice/)
})
