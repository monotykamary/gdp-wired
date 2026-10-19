// Trees and lists of lists in a rule's state, as tables of nodes that only grow (core/dsl.ts nodes): each node made one
// a step from nodes already there, its folds (values of its whole subtree) kept with it, so a law about a subtree is a
// law about one node. For the suite (`bun examples/trees.ts`), core/trees.test.ts and lean-kernel/package-check.ts.
//   - a search tree: a join makes a node from a key and two subtrees, only when every key on the left is below it and
//     every key on the right above it (each subtree's least and greatest key are its folds); then every node's left
//     subtree is below its key and its right above; the broken variant checks the left side only
//   - a sheet of rows, each a list of cells: a cell's amount capped, each list's total and largest amount its folds, a
//     row's read from the cells it starts at; every row's largest is within the cap; the broken variant lets a row start
//     at a cell not made yet, so its folds are not its cells' once that cell is made
import {type Law} from '../core/machine.ts'
import {type Term, forall, min, nat, oneOf, proveSteps, record, rule, when, yes} from '../core/dsl.ts'

export const searchTree = (bug?: 'checks the left side only') => rule('search tree').inputs({key: nat, l: nat, r: nat})
  .nodes('Tree', record({key: nat}), ['left', 'right'], {
    lo: {empty: 0, node: (x, k) => when(k.left.empty, x.key, k.left.fold.lo)},
    hi: {empty: 0, node: (x, k) => when(k.right.empty, x.key, k.right.fold.hi)},
  })
  .flags(({key, l, r, Tree}) => {
    const left = Tree.node(l), right = Tree.node(r)
    return {join: left.empty.or(left.fold.hi.lt(key)).and(bug ? yes : right.empty.or(key.lt(right.fold.lo)))}
  })
  .step(({key, l, r, join, Tree}) => Tree.make({key}, {left: l, right: r}, join))
export const searchTreeLaws = (r = searchTree()): Law[] => {
  const inside = (n: Term, size: Term) => n.atLeast(1).and(n.atMost(size))
  return [
    r.law('every node within its bounds', ({Tree, Tree_size}) => forall(n => inside(n, Tree_size).implies(Tree.node(n).fold.lo.atMost(Tree.at(n).key).and(Tree.at(n).key.atMost(Tree.node(n).fold.hi))))),
    r.law('every left subtree below its key', ({Tree, Tree_size}) => forall(n => inside(n, Tree_size).and(Tree.node(n).kids.left.atLeast(1)).implies(Tree.node(Tree.node(n).kids.left).fold.hi.lt(Tree.at(n).key)))),
    r.law('every right subtree above its key', ({Tree, Tree_size}) => forall(n => inside(n, Tree_size).and(Tree.node(n).kids.right.atLeast(1)).implies(Tree.at(n).key.lt(Tree.node(Tree.node(n).kids.right).fold.lo)))),
  ]
}

export const sheet = (bug?: 'starts a row at a cell not made yet') => rule('sheet').params({cap: nat}).inputs({op: oneOf('cell', 'row'), amount: nat, at: nat, next: nat})
  .nodes('Cell', record({amount: nat}), ['next'], {
    total: {empty: 0, node: (x, k) => x.amount.plus(k.next.fold.total)},
    most: {empty: 0, node: (x, k) => when(x.amount.atLeast(k.next.fold.most), x.amount, k.next.fold.most)},
  })
  .nodes('Row', record({first: nat}), ['next'], {
    total: {empty: 0, node: (x, k, {Cell}) => Cell.node(x.first).fold.total.plus(k.next.fold.total)},
    most: {empty: 0, node: (x, k, {Cell}) => when(Cell.node(x.first).fold.most.atLeast(k.next.fold.most), Cell.node(x.first).fold.most, k.next.fold.most)},
  })
  .step(({op, amount, at, next, cap, Cell, Row, Cell_size}) => ({
    ...Cell.make({amount: min(amount, cap)}, {next}, op.is('cell')),
    ...Row.make({first: at}, {next}, bug ? op.is('row') : op.is('row').and(at.atMost(Cell_size))),
  }))
export const sheetLaws = (r = sheet()): Law[] => [
  r.law('every row starts at a cell', ({Row, Row_size, Cell_size}) => forall(n => n.atLeast(1).and(n.atMost(Row_size)).implies(Row.at(n).first.atMost(Cell_size)))),
  r.law('every list of cells within the cap', ({Cell, Cell_size, cap}) => forall(n => n.atMost(Cell_size).implies(Cell.node(n).fold.most.atMost(cap)))),
  r.law('every row within the cap', ({Row, Row_size, cap}) => forall(n => n.atMost(Row_size).implies(Row.node(n).fold.most.atMost(cap)))),
]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'checks the left side only'] as const) {
    const r = searchTree(bug), v = proveSteps(r, searchTreeLaws(r), [])
    results.push([`search tree${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'starts a row at a cell not made yet'] as const) {
    const r = sheet(bug), v = proveSteps(r, sheetLaws(r), [])
    results.push([`sheet${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
