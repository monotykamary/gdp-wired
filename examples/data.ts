// Recursive datatypes as values (core/data.ts): lists and trees declared with their constructors, functions over them by
// structural recursion, and laws stated about them and nothing else. Each law is proven by a cyclic proof the search
// finds (which argument to induct on, where each cycle returns, the lemmas the law needs), or refuted by a value that
// breaks it. For the suite (`bun examples/data.ts`), core/data.test.ts, research/frontier/corpus.ts and
// lean-kernel/package-check.ts.
//   - lists: length, append, reverse, a map by an unknown function f, sum, sorted insertion, counting an item
//   - trees: a node's value between its subtrees; mirror, size, flatten (in order), sum, insertion into a search tree
//   - rose trees, a mutual pair (a node holds a forest, a forest trees): sum, size, flatten, mirror
//   - lists of lists (a field of a datatype declared before): concatenation, the lengths summed
//   - recursion on a natural: replicate, take, drop
//   - recursion that isn't structural, each function's termination proven before its equation is used: the merge of two
//     sorted lists (one list shorter at each call, the other the same: the measure (size xs, size ys), found), lists
//     interleaved (the two swapped at each call: size xs + size ys), a sum of three naturals with an accumulator
//     (add3acc: (x, y)), the same merge with its measure stated, and a quicksort (each call on a filter of the tail:
//     its decrease proven by induction on the filter)
//   - a user's own ≤, +, = on the naturals by recursion, a wrapper over them that isn't recursive, a count by the own =:
//     laws proven through the built-ins (core/transfer.ts), the bridges proven first
// The broken variants (an append that drops the head, a reverse that repeats it, a mirror that adds 1, an insertion that
// puts the item first, a search tree insertion that goes the wrong way or into any tree, a rose flatten that drops the
// node's value, a rose mirror that drops a tree, a concatenation that drops the first list, a replicate with one more, a
// drop of one too many, a merge that drops an item, an add3acc that forgets one) are refused with a value that breaks
// the law; the definitions that don't terminate (a merge that calls itself on the same lists, an interleave that only
// swaps them, an add3acc that doesn't lower y, a merge whose stated measure a call doesn't lower; and `adversarial`'s
// fourteen: rings that pass a value round, lower and raise it, swap two, step past a guard the runs don't reach, a call
// on a helper no longer than its argument up to 9 items only, one that halves its argument up to 8 items only, a heap
// read off through a merge that keeps both heaps where the user's ≤ fails, a nested call, an integer's) are refused, with the
// reason, before any law about them is read. `wellFounded`: a ring of two functions (a measure each) and a merge sort
// whose call's decrease needs a size law about the function of its argument.
import {type Bool, type DataLaw, type Integer, type Nat, type Val, data, define, fnParam, integer, law, mutual, natural, boolean, no, programOf, self, when, yes, proveData} from '../core/data.ts'

export const List = data('List', {nil: {}, cons: {head: natural, tail: self}})
export const Tree = data('Tree', {leaf: {}, node: {left: self, value: natural, right: self}})
const L = (v: unknown) => v as Val, N = (v: unknown) => v as Nat, B = (v: unknown) => v as Bool, I = (v: unknown) => v as Integer

export const len = define('len', {xs: List}, natural, ({xs}) => L(xs).match({nil: () => 0, cons: ({tail}) => N(len(tail)).plus(1)}))
export const sum = define('sum', {xs: List}, natural, ({xs}) => L(xs).match({nil: () => 0, cons: ({head, tail}) => N(sum(tail)).plus(head)}))
export const append = (bug?: 'drops the head') => {
  const name = bug ? 'appendDrop' : 'append'
  const f = define(name, {xs: List, ys: List}, List, ({xs, ys}) => L(xs).match({nil: () => L(ys), cons: ({head, tail}) => (bug ? L(f(tail, ys)) : List.cons(head, f(tail, ys)))}))
  return f
}
export const app = append()
export const reverse = (bug?: 'repeats the head') => {
  const name = bug ? 'reverseTwice' : 'reverse'
  const f = define(name, {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => L(app(f(tail), bug ? List.cons(head, List.cons(head, List.nil)) : List.cons(head, List.nil)))}))
  return f
}
export const rev = reverse()
// map over an unknown function f, over g, and over f after g (each its own function: the law is about every f and g).
export const f = fnParam('f'), g = fnParam('g')
export const mapF = define('mapF', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => List.cons(f(head), mapF(tail))}))
export const mapG = define('mapG', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => List.cons(g(head), mapG(tail))}))
export const mapFG = define('mapFG', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => List.cons(f(g(head)), mapFG(tail))}))
// Sorted: each item at most the next. Insertion before the first item not below it.
export const sorted = define('sorted', {xs: List}, boolean, ({xs}) => L(xs).match({nil: () => yes, cons: ({head, tail}) => L(tail).match({nil: () => yes, cons: ({head: next}) => N(head).atMost(next)}).and(B(sorted(tail)))}))
export const insert = (bug?: 'puts the item first') => {
  const name = bug ? 'insertFirst' : 'insert'
  const f = define(name, {x: natural, xs: List}, List, ({x, xs}) => L(xs).match({nil: () => List.cons(x, List.nil), cons: ({head, tail}) => (bug ? List.cons(x, xs) : when(N(x).atMost(head), List.cons(x, xs), List.cons(head, f(x, tail))))}))
  return f
}
export const ins = insert()
export const count = define('count', {y: natural, xs: List}, natural, ({y, xs}) => L(xs).match({nil: () => 0, cons: ({head, tail}) => when(N(head).eq(y), N(count(y, tail)).plus(1), N(count(y, tail)))}))

export const mirror = (bug?: 'adds one') => {
  const name = bug ? 'mirrorPlus' : 'mirror'
  const f = define(name, {t: Tree}, Tree, ({t}) => L(t).match({leaf: () => Tree.leaf, node: ({left, value, right}) => Tree.node(f(right), bug ? N(value).plus(1) : value, f(left))}))
  return f
}
export const mir = mirror()
export const size = define('size', {t: Tree}, natural, ({t}) => L(t).match({leaf: () => 0, node: ({left, right}) => N(size(left)).plus(N(size(right))).plus(1)}))
export const tsum = define('tsum', {t: Tree}, natural, ({t}) => L(t).match({leaf: () => 0, node: ({left, value, right}) => N(tsum(left)).plus(value).plus(N(tsum(right)))}))
export const flatten = define('flatten', {t: Tree}, List, ({t}) => L(t).match({leaf: () => List.nil, node: ({left, value, right}) => L(app(flatten(left), List.cons(value, flatten(right))))}))
// A search tree: every value in the left subtree below the node's, every value in the right above it.
export const allBelow = define('allBelow', {t: Tree, v: natural}, boolean, ({t, v}) => L(t).match({leaf: () => yes, node: ({left, value, right}) => N(value).lt(v).and(B(allBelow(left, v)), B(allBelow(right, v)))}))
export const allAbove = define('allAbove', {t: Tree, v: natural}, boolean, ({t, v}) => L(t).match({leaf: () => yes, node: ({left, value, right}) => N(v).lt(value).and(B(allAbove(left, v)), B(allAbove(right, v)))}))
export const bst = define('bst', {t: Tree}, boolean, ({t}) => L(t).match({leaf: () => yes, node: ({left, value, right}) => B(allBelow(left, value)).and(B(allAbove(right, value)), B(bst(left)), B(bst(right)))}))
export const bstInsert = (bug?: 'goes the wrong way') => {
  const name = bug ? 'bstInsertWrong' : 'bstInsert'
  const f = define(name, {x: natural, t: Tree}, Tree, ({x, t}) => L(t).match({leaf: () => Tree.node(Tree.leaf, x, Tree.leaf), node: ({left, value, right}) =>
    when(N(x).lt(value), bug ? Tree.node(left, value, f(x, right)) : Tree.node(f(x, left), value, right), when(N(value).lt(x), bug ? Tree.node(f(x, left), value, right) : Tree.node(left, value, f(x, right)), L(t)))}))
  return f
}
export const bins = bstInsert()

// Rose trees: a node holds a value and a forest of trees, a forest a list of them (a mutual pair, each a field of the
// other). Their functions call each other: a tree's through its forest's, a forest's through its trees'.
export const {Rose, Forest} = mutual({Rose: {node: {value: natural, kids: 'Forest'}}, Forest: {nil: {}, cons: {head: 'Rose', tail: 'Forest'}}})
export const rsum = define('rsum', {t: Rose}, natural, ({t}) => L(t).match({node: ({value, kids}) => N(value).plus(N(fsum(kids)))}))
export const fsum = define('fsum', {ts: Forest}, natural, ({ts}) => L(ts).match({nil: () => 0, cons: ({head, tail}) => N(rsum(head)).plus(N(fsum(tail)))}))
// A tree's values in order, the node's first; a forest's, each tree's in turn (`drops the value`: the node's left out).
export const roseFlatten = (bug?: 'drops the value') => {
  const [rn, fn] = bug ? ['rflatDrop', 'fflatDrop'] : ['rflat', 'fflat']
  const rf: ReturnType<typeof define> = define(rn, {t: Rose}, List, ({t}) => L(t).match({node: ({value, kids}) => (bug ? L(ff(kids)) : List.cons(value, ff(kids)))}))
  const ff: ReturnType<typeof define> = define(fn, {ts: Forest}, List, ({ts}) => L(ts).match({nil: () => List.nil, cons: ({head, tail}) => L(app(rf(head), ff(tail)))}))
  return rf
}
export const rflat = roseFlatten()
export const rsize = define('rsize', {t: Rose}, natural, ({t}) => L(t).match({node: ({kids}) => N(fsize(kids)).plus(1)}))
export const fsize = define('fsize', {ts: Forest}, natural, ({ts}) => L(ts).match({nil: () => 0, cons: ({head, tail}) => N(rsize(head)).plus(N(fsize(tail)))}))
// A tree after one more at a forest's end (`drops it`: the tree given left out).
export const snoc = (bug?: 'drops it') => {
  const name = bug ? 'snocDrop' : 'snoc'
  const f: ReturnType<typeof define> = define(name, {ts: Forest, r: Rose}, Forest, ({ts, r}) => L(ts).match({nil: () => (bug ? Forest.nil : Forest.cons(r, Forest.nil)), cons: ({head, tail}) => Forest.cons(head, f(tail, r))}))
  return f
}
// The mirror: each forest reversed, each tree in it mirrored.
export const roseMirror = (bug?: 'drops a tree') => {
  const [rn, fn] = bug ? ['rmirrorDrop', 'fmirrorDrop'] : ['rmirror', 'fmirror'], sn = snoc(bug ? 'drops it' : undefined)
  const rm: ReturnType<typeof define> = define(rn, {t: Rose}, Rose, ({t}) => L(t).match({node: ({value, kids}) => Rose.node(value, fm(kids))}))
  const fm: ReturnType<typeof define> = define(fn, {ts: Forest}, Forest, ({ts}) => L(ts).match({nil: () => Forest.nil, cons: ({head, tail}) => L(sn(fm(tail), rm(head)))}))
  return rm
}
export const rmirror = roseMirror()

// Lists of lists: a bag's lists (a field of a datatype declared before), concatenated, their lengths summed.
export const Bag = data('Bag', {none: {}, more: {items: List, rest: self}})
export const concat = (bug?: 'drops the first') => {
  const name = bug ? 'concatDrop' : 'concat'
  const f: ReturnType<typeof define> = define(name, {b: Bag}, List, ({b}) => L(b).match({none: () => List.nil, more: ({items, rest}) => (bug ? L(f(rest)) : L(app(items, f(rest))))}))
  return f
}
export const cat = concat()
export const lens = define('lens', {b: Bag}, natural, ({b}) => L(b).match({none: () => 0, more: ({items, rest}) => N(len(items)).plus(N(lens(rest)))}))

// Recursion on a natural: n copies of x (`one more`: n + 1 of them), the first n items and the rest after them (`one
// too many`: the rest after n + 1).
export const replicate = (bug?: 'one more') => {
  const name = bug ? 'replicateMore' : 'replicate'
  const f: ReturnType<typeof define> = define(name, {n: natural, x: natural}, List, ({n, x}) => N(n).match({zero: () => (bug ? List.cons(x, List.nil) : List.nil), succ: ({pred}) => List.cons(x, f(pred, x))}))
  return f
}
export const rep = replicate()
export const take = define('take', {n: natural, xs: List}, List, ({n, xs}) => N(n).match({zero: () => List.nil, succ: ({pred}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => List.cons(head, take(pred, tail))})}))
export const drop = (bug?: 'one too many') => {
  const name = bug ? 'dropMore' : 'drop'
  const f: ReturnType<typeof define> = define(name, {n: natural, xs: List}, List, ({n, xs}) => N(n).match({zero: () => (bug ? L(xs).match({nil: () => List.nil, cons: ({tail}) => L(tail)}) : L(xs)), succ: ({pred}) => L(xs).match({nil: () => List.nil, cons: ({tail}) => L(f(pred, tail))})}))
  return f
}
export const drp = drop()

// Recursion that isn't structural. The merge of two sorted lists: each call drops the head of one list and passes the
// other whole (`drops an item`: the second list's head left out; `stays`: the call on the same lists where the second
// head is smaller, which never ends; `stated`: the measure given, size xs + size ys; `stated wrong`: size xs alone, which
// the second call doesn't lower).
export const merge = (bug?: 'drops an item' | 'stays' | 'stated' | 'stated wrong') => {
  const name = !bug ? 'merge' : bug === 'drops an item' ? 'mergeDrop' : bug === 'stays' ? 'mergeStay' : bug === 'stated' ? 'mergeSum' : 'mergeWrong'
  const f: ReturnType<typeof define> = define(name, {xs: List, ys: List}, List, ({xs, ys}) => L(xs).match({nil: () => L(ys), cons: ({head: x, tail: xt}) => L(ys).match({nil: () => L(xs), cons: ({head: y, tail: yt}) =>
    when(N(x).atMost(y), List.cons(x, f(xt, ys)), bug === 'drops an item' ? L(f(xs, yt)) : bug === 'stays' ? L(f(xs, ys)) : List.cons(y, f(xs, yt)))})}), bug === 'stated' ? {measure: [['xs', 'ys']]} : bug === 'stated wrong' ? {measure: ['xs']} : {})
  return f
}
export const mrg = merge()
// Two lists interleaved: the head of the first, then the second interleaved with the first's tail (`swaps only`: the two
// swapped and nothing dropped, which never ends).
export const interleave = (bug?: 'swaps only') => {
  const name = bug ? 'interleaveSwap' : 'interleave'
  const f: ReturnType<typeof define> = define(name, {xs: List, ys: List}, List, ({xs, ys}) => L(xs).match({nil: () => L(ys), cons: ({head, tail}) => (bug ? L(f(ys, xs)) : List.cons(head, f(ys, tail)))}))
  return f
}
export const ilv = interleave()
// x + y + z with an accumulator: x moved into y, then y into z (`forgets one`: a step of y that doesn't add to z;
// `keeps y`: a step that doesn't lower y, which never ends).
export const add3acc = (bug?: 'forgets one' | 'keeps y') => {
  const name = !bug ? 'add3acc' : bug === 'forgets one' ? 'add3accForget' : 'add3accKeep'
  const f: ReturnType<typeof define> = define(name, {x: natural, y: natural, z: natural}, natural, ({x, y, z}) => N(x).match({
    zero: () => N(y).match({zero: () => z, succ: ({pred}) => (bug === 'forgets one' ? N(f(0, pred, z)) : bug === 'keeps y' ? N(f(0, y, N(z).plus(1))) : N(f(0, pred, N(z).plus(1))))}),
    succ: ({pred}) => N(f(pred, N(y).plus(1), z))}))
  return f
}
export const a3 = add3acc()
// A quicksort: the items of the tail at most the head sorted, the head, those above it sorted. Each call is on a filter
// of the tail, so its decrease (the filter no longer than the tail) is proven by induction on the filter.
export const atMost = define('atMost', {v: natural, xs: List}, List, ({v, xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => when(N(head).atMost(v), List.cons(head, atMost(v, tail)), L(atMost(v, tail)))}))
export const above = define('above', {v: natural, xs: List}, List, ({v, xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => when(N(v).lt(head), List.cons(head, above(v, tail)), L(above(v, tail)))}))
export const qsort: ReturnType<typeof define> = define('qsort', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => L(app(qsort(atMost(head, tail)), List.cons(head, qsort(above(head, tail)))))}))

// A ring of two functions that isn't structural recursion (lean-kernel/Data.lean's wf_fix_unique_ring): an expression's
// tokens, a sum's read through `paren` at the same value, each of whose operands' read at a field. Their measures, one
// a function: the size first at both, then 1 at `tokens` and 0 at `paren` (the call the size leaves equal, ranked by the
// runs).
export const Expr = data('Expr', {atom: {}, sum: {a: self, b: self}})
export const tokens: ReturnType<typeof define> = define('tokens', {e: Expr}, natural, ({e}) => L(e).match({atom: () => 1, sum: () => N(paren(e)).plus(2)}))
export const paren: ReturnType<typeof define> = define('paren', {e: Expr}, natural, ({e}) => L(e).match({atom: () => 1, sum: ({a, b}) => N(tokens(a)).plus(N(tokens(b))).plus(1)}))
// A merge sort from the bottom up: a list of sorted runs merged in pairs (`pairwise`) until one is left. Its call is on
// the runs merged in pairs, no more than the runs (a size law about `pairwise`, conjectured from its values, proven by
// induction and used in the decrease's proof).
export const Runs = data('Runs', {none: {}, run: {first: List, rest: self}})
export const pairwise: ReturnType<typeof define> = define('pairwise', {rs: Runs}, Runs, ({rs}) => L(rs).match({none: () => Runs.none, run: ({first, rest}) => L(rest).match({none: () => Runs.run(first, Runs.none), run: ({first: second, rest: more}) => Runs.run(mrg(first, second), pairwise(more))})}))
export const mergeRuns: ReturnType<typeof define> = define('mergeRuns', {rs: Runs}, List, ({rs}) => L(rs).match({none: () => List.nil, run: ({first, rest}) => L(rest).match({none: () => L(first), run: () => L(mergeRuns(pairwise(rs)))})}))
// A natural written as an integer (compare/chc-adt: CHC-COMP's ADT-LIA writes TIP's naturals as Int): counted down to 0,
// its measure the integer's value where positive (Lean's Int.toNat), the call on the path where x ≥ 1 (an if, or a
// condition's choice on Bool).
export const countDown: ReturnType<typeof define> = define('countDown', {x: integer}, integer, ({x}) => when(I(x).atLeast(1), I(countDown(I(x).minus(1))).plus(1), I(x).times(0)))
export const reachesZero: ReturnType<typeof define> = define('reachesZero', {x: integer}, boolean, ({x}) => when(I(x).atLeast(1), B(reachesZero(I(x).minus(1))), yes))
// Bitonic sort's halves (TIP's sort_BSort*): evens and odds of a list, calling each other, and a merge of two sorted lists
// by merging their evens and their odds. Its calls are on halves: each taken by the halves' size law, 2·size(evens(x))
// <= size(x) + 2 and 2·size(odds(x)) <= size(x) + 1, conjectured as one law of the two (each the other's induction step)
// and proven by induction on both at once.
export const evens: ReturnType<typeof define> = define('evens', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => List.cons(head, odds(tail))}))
export const odds: ReturnType<typeof define> = define('odds', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({tail}) => evens(tail)}))
const sort2 = define('sort2', {x: natural, y: natural}, List, ({x, y}) => when(N(x).atMost(y), List.cons(x, List.cons(y, List.nil)), List.cons(y, List.cons(x, List.nil))))
const pairs: ReturnType<typeof define> = define('pairs', {x: List, y: List}, List, ({x, y}) => L(x).match({nil: () => L(y), cons: ({head: z, tail: x2}) => L(y).match({nil: () => L(x), cons: ({head: x3, tail: x4}) => app(sort2(z, x3), pairs(x2, x4))})}))
const stitch = define('stitch', {x: List, y: List}, List, ({x, y}) => L(x).match({nil: () => L(y), cons: ({head, tail}) => List.cons(head, pairs(tail, y))}))
export const bmerge: ReturnType<typeof define> = define('bmerge', {x: List, y: List}, List, ({x, y}) => L(x).match({nil: () => List.nil, cons: ({head: z, tail: x2}) => L(y).match({nil: () => L(x), cons: ({head: x3, tail: x4}) => {
  const halves = () => stitch(bmerge(evens(x), evens(y)), bmerge(odds(x), odds(y)))
  return L(x2).match({nil: () => L(x4).match({nil: () => sort2(z, x3), cons: () => halves()}), cons: () => halves()})
}})}))
export const bsort: ReturnType<typeof define> = define('bsort', {x: List}, List, ({x}) => L(x).match({nil: () => List.nil, cons: ({head: y, tail: z}) => L(z).match({nil: () => List.cons(y, List.nil), cons: () => bmerge(bsort(evens(x)), bsort(odds(x)))})}))
// A skew heap over the user's own ≤ (TIP's sort_nat_HSort*, Peano naturals): toList's call on the merge of its subheaps,
// below the heap by the merge's size law, proven by the merge's recursion with its cases split on the user's ≤ the merge
// reads, not on the fields' tags its unfolding would.
export const Heap = data('Heap', {node: {l: self, v: natural, r: self}, nil: {}})
export const hmerge: ReturnType<typeof define> = define('hmerge', {x: Heap, y: Heap}, Heap, ({x, y}) => L(x).match({
  node: ({l: z, v: x2, r: x3}) => L(y).match({node: ({l: x4, v: x5, r: x6}) => when(B(leq(x2, x5)), Heap.node(hmerge(x3, y), x2, z), Heap.node(hmerge(x, x6), x5, x4)), nil: () => L(x)}),
  nil: () => L(y)}))
export const heapList: ReturnType<typeof define> = define('heapList', {x: Heap}, List, ({x}) => L(x).match({node: ({l, v, r}) => List.cons(v, heapList(hmerge(l, r))), nil: () => List.nil}))
export const wellFounded = {
  bsortOne: () => law('bitonic sort of one item', {x: natural}, ({x}) => L(bsort(List.cons(x, List.nil))).eq(List.cons(x, List.nil))),
  countDownNonneg: () => law('an integer counted down is never negative', {x: integer}, ({x}) => I(countDown(x)).atLeast(0)),
  reachesZero: () => law('every integer counts down to 0', {x: integer}, ({x}) => B(reachesZero(x))),
  tokensPositive: () => law('an expression has a token', {e: Expr}, ({e}) => N(tokens(e)).atLeast(1)),
  mergeRunsOne: () => law('one run merged is itself', {xs: List}, ({xs}) => L(mergeRuns(Runs.run(xs, Runs.none))).eq(L(xs))),
} satisfies Record<string, () => DataLaw>

// Nested recursion (a call of the function in another's argument): each taken with an invariant of its value, proven
// with the decrease (Data.lean's wf_fix_inv_unique; research/termination/Nested.lean defines the first two in Lean from
// the same obligations). nz 0 = 0, nz (n + 1) = nz (nz n): its value at most its argument (nz n = 0, Nested.lean's law,
// isn't found by the search: its induction's use at nz(pred)). nest keeps a list's length
// and reads itself at its own value of the tail. Ackermann's outer call lowers its first argument whatever the inner
// call's value: no invariant.
export const nz: ReturnType<typeof define> = define('nz', {n: natural}, natural, ({n}) => N(n).match({zero: () => 0, succ: ({pred}) => N(nz(nz(pred)))}))
export const nest: ReturnType<typeof define> = define('nest', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => List.cons(head, nest(nest(tail)))}))
export const ack: ReturnType<typeof define> = define('ack', {m: natural, n: natural}, natural, ({m, n}) => N(m).match({zero: () => N(n).plus(1), succ: ({pred: p}) => N(n).match({zero: () => N(ack(p, 1)), succ: ({pred: q}) => N(ack(p, ack(m, q)))})}))
// A ring: nestA reads nestB at its own value of the tail, nestB reads nestA at its argument.
export const nestA: ReturnType<typeof define> = define('nestA', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => List.cons(head, nestB(nestA(tail)))}))
export const nestB: ReturnType<typeof define> = define('nestB', {xs: List}, List, ({xs}) => L(nestA(xs)))
// A ring weighted across its functions (TIP's propositional `models`): a formula's value, `Not (And r q)` read again
// as `And r (Not q)` (no size falls: both are 1 + 1 + size r + size q), `both` reading the right operand at the left's
// value. Its measure: a fold of the formula, `Not` weighing its formula twice, the first component at both functions,
// then 1 at `both` and 0 at `ev` (`both` reads `ev` at the same formula).
export const Form = data('Form', {and: {l: self, r: self}, not: {f: self}, atom: {n: natural}})
export const ev: ReturnType<typeof define> = define('ev', {f: Form, k: natural}, natural, ({f, k}) => L(f).match({
  and: ({l, r}) => N(both(r, ev(l, k))),
  not: ({f: g}) => L(g).match({and: ({l, r}) => N(ev(Form.and(l, Form.not(r)), k)), not: ({f: h}) => N(ev(h, k)), atom: () => N(k)}),
  atom: ({n}) => N(n).plus(k),
}))
export const both: ReturnType<typeof define> = define('both', {f: Form, k: natural}, natural, ({f, k}) => N(ev(f, N(k).plus(1))))
export const nested = {
  nestSame: () => law('nest is the list', {xs: List}, ({xs}) => L(nest(xs)).eq(L(xs))),
  nestRingSame: () => law('nestA is the list', {xs: List}, ({xs}) => L(nestA(xs)).eq(L(xs))),
  ackAbove: () => law('ack is above its second argument', {m: natural, n: natural}, ({m, n}) => N(ack(m, n)).atLeast(N(n).plus(1))),
  evNotNot: () => law('an atom under two nots, read by both', {n: natural, k: natural}, ({n, k}) => N(both(Form.not(Form.not(Form.atom(n))), k)).eq(N(n).plus(k).plus(1))),
} satisfies Record<string, () => DataLaw>

// Definitions that don't terminate, made to look as if they did (core/data.test.ts): each refused with the measures
// tried, before any law about it is read. Taken as an equation, any of them would let the kernel prove anything.
const nearTail = define('nearTail', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => when(N(len(tail)).atLeast(9), List.cons(head, L(xs)), L(tail))}))
const loops = {
  // an integer counted down below 0 for ever (its size, toNat, stays 0 there): and on Bool, behind a condition's choice
  intBelow: () => { const f: ReturnType<typeof define> = define('intBelow', {x: integer}, integer, ({x}) => when(I(x).atMost(0), I(f(I(x).minus(1))), I(x).times(0))); return f },
  intBelowBool: () => { const f: ReturnType<typeof define> = define('intBelowBool', {x: integer}, boolean, ({x}) => when(I(x).atMost(5), B(f(I(x).minus(1))), yes)); return f },
  // a ring that passes its argument round
  passRound: () => { const f: ReturnType<typeof define> = define('passA', {xs: List}, natural, ({xs}) => N(g(xs))), g: ReturnType<typeof define> = define('passB', {xs: List}, natural, ({xs}) => N(f(xs))); return f },
  // one lowers its argument, the other builds it back
  lowerRaise: () => { const f: ReturnType<typeof define> = define('lowerA', {xs: List}, natural, ({xs}) => L(xs).match({nil: () => 0, cons: ({tail}) => N(g(tail))})), g: ReturnType<typeof define> = define('raiseB', {xs: List}, natural, ({xs}) => N(f(List.cons(0, xs)))); return f },
  // a ring that lowers n below 9 and passes it round from 9 up: past the runs' values
  lateRing: () => { const f: ReturnType<typeof define> = define('lateA', {n: natural}, natural, ({n}) => when(N(n).atLeast(9), N(g(n)), N(n).match({zero: () => 0, succ: ({pred}) => N(f(pred))}))), g: ReturnType<typeof define> = define('lateB', {n: natural}, natural, ({n}) => N(f(n))); return f },
  // two lists swapped at each call, through the ring
  swapRing: () => { const f: ReturnType<typeof define> = define('swapA', {xs: List, ys: List}, natural, ({xs, ys}) => L(xs).match({nil: () => 0, cons: () => N(g(ys, xs))})), g: ReturnType<typeof define> = define('swapB', {xs: List, ys: List}, natural, ({xs, ys}) => N(f(ys, xs))); return f },
  // even and odd, but odd steps up two
  stepUp: () => { const f: ReturnType<typeof define> = define('evenUp', {n: natural}, natural, ({n}) => N(n).match({zero: () => 1, succ: ({pred}) => N(g(pred))})), g: ReturnType<typeof define> = define('oddUp', {n: natural}, natural, ({n}) => N(n).match({zero: () => 0, succ: ({pred}) => N(f(N(pred).plus(3)))})); return f },
  // a call on a helper no longer than its argument up to 9 items, longer past them: the size law its values suggest is
  // false, and its induction fails
  nearTail: () => { const f: ReturnType<typeof define> = define('nearTailLoop', {xs: List}, natural, ({xs}) => L(xs).match({nil: () => 0, cons: () => N(f(nearTail(xs)))})); return f },
  // the same through a ring
  nearTailRing: () => { const f: ReturnType<typeof define> = define('nearRingA', {xs: List}, natural, ({xs}) => L(xs).match({nil: () => 0, cons: () => N(g(nearTail(xs)))})), g: ReturnType<typeof define> = define('nearRingB', {xs: List}, natural, ({xs}) => N(f(xs))); return f },
  // halves past the runs' sizes only: evens up to 8 items, the list itself from 9; a call on it is a halving's for the
  // values the size law is conjectured from, and its induction fails
  halvesTill9: () => { const h = define('halfTill9', {xs: List}, List, ({xs}) => when(N(len(xs)).atLeast(9), L(xs), L(evens(xs)))); const f: ReturnType<typeof define> = define('halvesTill9', {xs: List}, natural, ({xs}) => L(xs).match({nil: () => 0, cons: ({tail}) => L(tail).match({nil: () => 0, cons: () => N(f(h(xs)))})})); return f },
  // a merge over the user's ≤ that, where the ≤ fails, puts both heaps below a node: read off, the heap never shrinks
  guardKeeps: () => { const m: ReturnType<typeof define> = define('mergeKeeps', {x: Heap, y: Heap}, Heap, ({x, y}) => L(x).match({node: ({l, v, r}) => L(y).match({node: ({v: w}) => when(B(leq(v, w)), Heap.node(m(r, y), v, l), Heap.node(L(x), w, L(y))), nil: () => L(x)}), nil: () => L(y)})); const f: ReturnType<typeof define> = define('readKeeps', {x: Heap}, natural, ({x}) => L(x).match({node: ({l, r}) => N(f(m(l, r))), nil: () => 0})); return f },
  // 0 calls 1 and 1 calls 0
  upDown: () => { const f: ReturnType<typeof define> = define('upDown', {n: natural}, natural, ({n}) => N(n).match({zero: () => N(f(1)), succ: ({pred}) => N(f(pred))})); return f },
  // a sum of two that stays: (x + 1, y) to (x, y + 1), (0, y + 1) to (y + 1, y)
  sumStays: () => { const f: ReturnType<typeof define> = define('sumStays', {x: natural, y: natural}, natural, ({x, y}) => N(x).match({zero: () => N(y).match({zero: () => 0, succ: ({pred}) => N(f(N(pred).plus(1), pred))}), succ: ({pred}) => N(f(pred, N(y).plus(1)))})); return f },
  // nested and never ending: f(n) = f(f(n))
  nested: () => { const f: ReturnType<typeof define> = define('nestedLoop', {n: natural}, natural, ({n}) => N(f(f(n)))); return f },
  // nested, never ending at 1: f(n + 1) = f(f(n) + 1), f(1) = f(f(0) + 1) = f(1)
  nestedBump: () => { const f: ReturnType<typeof define> = define('nestedBump', {n: natural}, natural, ({n}) => N(n).match({zero: () => 0, succ: ({pred}) => N(f(N(f(pred)).plus(1)))})); return f },
  // nested, its value at most its argument up to 20 (0 there), then above it, and from 22 on it never ends: the
  // invariant its runs suggest (value ≤ argument) lowers the outer call, and is false (a body doesn't keep it)
  nestedLate: () => { const f: ReturnType<typeof define> = define('nestedLate', {n: natural}, natural, ({n}) => N(n).match({zero: () => 0, succ: ({pred}) => when(N(pred).atMost(19), N(f(f(pred))), N(f(f(pred))).plus(N(pred).times(2)))})); return f },
  // a list's length kept up to 9 items, two more from 10 on (never ending at 11): the length its runs keep lowers the
  // outer call, and the body past 9 items doesn't keep it
  nestedGrow: () => { const f: ReturnType<typeof define> = define('nestedGrow', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => when(N(len(tail)).atMost(8), List.cons(head, f(f(tail))), List.cons(head, List.cons(head, f(f(tail)))))})); return f },
  // the same through a ring: the outer call of the other
  nestedGrowRing: () => { const f: ReturnType<typeof define> = define('nestedGrowA', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => when(N(len(tail)).atMost(8), List.cons(head, g(f(tail))), List.cons(head, List.cons(head, g(f(tail)))))})), g: ReturnType<typeof define> = define('nestedGrowB', {xs: List}, List, ({xs}) => L(f(xs))); return f },
  // the weighted ring, but a Not of an And whose operands are both past 8 in size turned round (and never ending there):
  // every weighting is equal across that call
  foldSwapLate: () => {
    const sz = define('formSize', {f: Form}, natural, ({f}) => L(f).match({and: ({l, r}) => N(sz(l)).plus(N(sz(r))).plus(1), not: ({f: g}) => N(sz(g)).plus(1), atom: () => 1}))
    const f: ReturnType<typeof define> = define('evLate', {f: Form, k: natural}, natural, ({f: x, k}) => L(x).match({
      and: ({l, r}) => N(g(r, f(l, k))),
      not: ({f: y}) => L(y).match({and: ({l, r}) => when(N(sz(l)).atLeast(9).and(N(sz(r)).atLeast(9)), N(f(Form.not(Form.and(r, l)), k)), N(f(Form.and(l, Form.not(r)), k))), not: ({f: h}) => N(f(h, k)), atom: () => N(k)}),
      atom: ({n}) => N(n).plus(k),
    }))
    const g: ReturnType<typeof define> = define('bothLate', {f: Form, k: natural}, natural, ({f: x, k}) => N(f(x, N(k).plus(1))))
    return f
  },
  // on an integer (no measure reads one): below 0 it never ends
  intDown: () => { const f: ReturnType<typeof define> = define('intDown', {i: integer}, natural, ({i}) => when(I(i).eq(0), 0 as number, N(f(I(i).minus(1))) as never)); return f },
  // a ring whose measures are given and don't fall: (size xs) at both, the call passing xs round
  ringStatedWrong: () => { const f: ReturnType<typeof define> = define('statedA', {xs: List}, natural, ({xs}) => L(xs).match({nil: () => 0, cons: ({tail}) => N(g(tail))}), {measure: ['xs']}), g: ReturnType<typeof define> = define('statedB', {xs: List}, natural, ({xs}) => N(f(List.cons(1, xs))), {measure: ['xs']}); return f },
}
export const adversarial = Object.fromEntries(Object.entries(loops).map(([name, mk]) => [name, () => { const f = mk(); return law(`${name} is 0`, Object.fromEntries(f.fn.params.map(p => [p.name, p.sort])) as never, vs => { const r = f(...f.fn.params.map(p => vs[p.name])) as Nat | Bool; return 'y' in r ? r : N(r).eq(0) }) }])) as Record<keyof typeof loops, () => DataLaw>

// A user's own arithmetic on the naturals, by recursion (as a library ported from a proof assistant writes it): ≤, +,
// an equality, a count by it, and a definition that isn't recursive over them (≥ as ≤ the other way). proveData proves
// each of these agrees with the built-in (its bridge, by recursion induction), and the laws through the built-ins.
export const leq = define('leq', {x: natural, y: natural}, boolean, ({x, y}) => N(x).match({zero: () => yes, succ: ({pred: p}) => N(y).match({zero: () => no, succ: ({pred: q}) => B(leq(p, q))})}))
export const plus = define('plus', {x: natural, y: natural}, natural, ({x, y}) => N(x).match({zero: () => N(y), succ: ({pred}) => N(plus(pred, y)).plus(1)}))
export const same = define('same', {x: natural, y: natural}, boolean, ({x, y}) => N(x).match({zero: () => N(y).eq(0), succ: ({pred: p}) => N(y).match({zero: () => no, succ: ({pred: q}) => B(same(p, q))})}))
export const geq = define('geq', {x: natural, y: natural}, boolean, ({x, y}) => B(leq(y, x)))
export const occurs = define('occurs', {y: natural, xs: List}, natural, ({y, xs}) => L(xs).match({nil: () => 0, cons: ({head, tail}) => when(B(same(head, y)), N(occurs(y, tail)).plus(1), N(occurs(y, tail)))}))
export const through = {
  // n ≤ n + m, both the user's: not a shape the conjectures make; proven by plus's own recursion on n (a case's
  // classes take its condition n ≠ 0, where plus (n, m) is a successor and leq unfolds).
  leqPlus: () => law('n is at most n plus m', {n: natural, m: natural}, ({n, m}) => B(leq(n, plus(n, m)))),
  // n ≤ m + n: by no recursion of either; proven through x ≤ y and x + y.
  leqPlusLeft: () => law('n is at most m plus n', {n: natural, m: natural}, ({n, m}) => B(leq(n, plus(m, n)))),
  // geq x x: geq isn't recursive (unfolded), leq bridged.
  geqSelf: () => law('x is at least itself', {x: natural}, ({x}) => B(geq(x, x))),
  // the count of n after n: same(n, n) is n = n through its bridge, the count read through its copy.
  occursCons: () => law('one more of n after n', {n: natural, xs: List}, ({n, xs}) => N(occurs(n, List.cons(n, xs))).eq(N(occurs(n, xs)).plus(1))),
  // n ≤ 0 only when n = 0: by the cases of n, no induction.
  leqZero: () => law('at most zero is zero', {n: natural}, ({n}) => B(leq(n, 0)).implies(B(same(n, 0)))),
}
export const throughBroken = {
  leqPlus: () => law('n plus m is at most n', {n: natural, m: natural}, ({n, m}) => B(leq(plus(n, m), n))),
}

// The laws, each over the functions as declared (a broken variant's law reads the broken function).
export const laws = {
  lengthAppend: (a = app) => law('length of append', {xs: List, ys: List}, ({xs, ys}) => N(len(a(xs, ys))).eq(N(len(xs)).plus(N(len(ys))))),
  appendAssoc: (a = app) => law('append is associative', {xs: List, ys: List, zs: List}, ({xs, ys, zs}) => L(a(a(xs, ys), zs)).eq(L(a(xs, a(ys, zs))))),
  reverseReverse: (r = rev) => law('reverse of reverse', {xs: List}, ({xs}) => L(r(r(xs))).eq(L(xs))),
  mapFusion: () => law('map fusion', {xs: List}, ({xs}) => L(mapF(mapG(xs))).eq(L(mapFG(xs)))),
  lengthMap: () => law('length of map', {xs: List}, ({xs}) => N(len(mapF(xs))).eq(N(len(xs)))),
  mirrorMirror: (m = mir) => law('mirror of mirror', {t: Tree}, ({t}) => L(m(m(t))).eq(L(t))),
  sizeMirror: (m = mir) => law('size of mirror', {t: Tree}, ({t}) => N(size(m(t))).eq(N(size(t)))),
  sumFlatten: () => law('sum of flatten', {t: Tree}, ({t}) => N(sum(flatten(t))).eq(N(tsum(t)))),
  insertSorted: (i = ins) => law('insertion keeps a list sorted', {x: natural, xs: List}, ({x, xs}) => B(sorted(xs)).implies(B(sorted(i(x, xs))))),
  insertCount: (i = ins) => law('insertion adds one of the item', {x: natural, y: natural, xs: List}, ({x, y, xs}) => N(count(y, i(x, xs))).eq(when(N(x).eq(y), N(count(y, xs)).plus(1), N(count(y, xs))))),
  insertLength: (i = ins) => law('insertion adds one item', {x: natural, xs: List}, ({x, xs}) => N(len(i(x, xs))).eq(N(len(xs)).plus(1))),
  bstInsert: (i = bins) => law('search tree insertion keeps the order', {x: natural, t: Tree}, ({x, t}) => B(bst(t)).implies(B(bst(i(x, t))))),
  roseSumFlatten: (fl = rflat) => law('sum of a flattened rose tree', {t: Rose}, ({t}) => N(sum(fl(t))).eq(N(rsum(t)))),
  roseSizeMirror: (m = rmirror) => law('size of a mirrored rose tree', {t: Rose}, ({t}) => N(rsize(m(t))).eq(N(rsize(t)))),
  bagLength: (c = cat) => law('length of a concatenation', {b: Bag}, ({b}) => N(len(c(b))).eq(N(lens(b)))),
  replicateLength: (r = rep) => law('length of n copies', {n: natural, x: natural}, ({n, x}) => N(len(r(n, x))).eq(n)),
  takeDrop: (d = drp) => law('the first n and the rest', {n: natural, xs: List}, ({n, xs}) => L(app(take(n, xs), d(n, xs))).eq(L(xs))),
  dropLength: (d = drp) => law('length after dropping n', {n: natural, xs: List}, ({n, xs}) => N(len(d(n, xs))).eq(N(len(xs)).minus(n))),
  mergeLength: (m = mrg) => law('length of a merge', {xs: List, ys: List}, ({xs, ys}) => N(len(m(xs, ys))).eq(N(len(xs)).plus(N(len(ys))))),
  interleaveLength: (i = ilv) => law('length of an interleaving', {xs: List, ys: List}, ({xs, ys}) => N(len(i(xs, ys))).eq(N(len(xs)).plus(N(len(ys))))),
  add3acc: (f = a3) => law('add3acc adds its three', {x: natural, y: natural, z: natural}, ({x, y, z}) => N(f(x, y, z)).eq(N(x).plus(y).plus(z))),
  mergeStated: () => law('length of a merge, its measure stated', {xs: List, ys: List}, ({xs, ys}) => N(len(merge('stated')(xs, ys))).eq(N(len(xs)).plus(N(len(ys))))),
  qsortSingle: () => law('quicksort of one item', {x: natural}, ({x}) => L(qsort(List.cons(x, List.nil))).eq(List.cons(x, List.nil))),
} satisfies Record<string, (...a: never[]) => DataLaw>

export const broken = {
  lengthAppend: () => laws.lengthAppend(append('drops the head')),
  reverseReverse: () => laws.reverseReverse(reverse('repeats the head')),
  mirrorMirror: () => laws.mirrorMirror(mirror('adds one')),
  insertSorted: () => laws.insertSorted(insert('puts the item first')),
  bstInsert: () => laws.bstInsert(bstInsert('goes the wrong way')),
  // The hypothesis dropped: an insertion into any tree.
  bstInsertAny: () => law('search tree insertion keeps the order', {x: natural, t: Tree}, ({x, t}) => B(bst(bins(x, t)))),
  roseSumFlatten: () => laws.roseSumFlatten(roseFlatten('drops the value')),
  roseSizeMirror: () => laws.roseSizeMirror(roseMirror('drops a tree')),
  bagLength: () => laws.bagLength(concat('drops the first')),
  replicateLength: () => laws.replicateLength(replicate('one more')),
  takeDrop: () => laws.takeDrop(drop('one too many')),
  dropLength: () => laws.dropLength(drop('one too many')),
  mergeLength: () => laws.mergeLength(merge('drops an item')),
  add3acc: () => laws.add3acc(add3acc('forgets one')),
}

// Definitions that don't terminate, or whose measure isn't the one given: each refused (the law about it never read),
// its reason the measures tried.
export const nonterminating = {
  mergeStays: () => laws.mergeLength(merge('stays')),
  interleaveSwaps: () => laws.interleaveLength(interleave('swaps only')),
  add3accKeeps: () => laws.add3acc(add3acc('keeps y')),
  mergeStatedWrong: () => laws.mergeLength(merge('stated wrong')),
}
// Its refusal (the reason), or undefined when the definitions it reads are taken.
export const refusal = (mk: () => DataLaw): string | undefined => { try { programOf([mk()]); return undefined } catch (e) { return (e as Error).message } }

// Laws the search doesn't prove within its time (research/frontier/README.md): none.
export const open = new Set<string>([])

if (import.meta.main) {
  // (`bun examples/data.ts <law>`: that law and its broken variant alone; `-<law>`: all but those)
  const arg = process.argv[2], skip = (name: string) => (arg?.startsWith('-') ? name === arg.slice(1) : !!arg && name !== arg)
  let failed = false
  for (const [name, mk] of Object.entries(laws)) {
    if (skip(name)) continue
    const v = proveData((mk as () => DataLaw)()), ok = v.proven && v.checked
    console.log(`${ok ? 'ok  ' : open.has(name) ? 'open' : 'FAIL'} ${v.law}: ${v.proven ? `proven, ${v.ms} ms (${v.scheme}${v.lemmas.length ? `; lemmas: ${v.lemmas.join('; ')}` : ''})` : `not proven (${v.goal}: ${v.stuck})`}`)
    failed ||= !ok && !open.has(name)
  }
  for (const [name, mk] of Object.entries(through)) {
    if (skip(name)) continue
    const v = proveData(mk()), ok = v.proven && v.checked
    console.log(`${ok ? 'ok  ' : 'FAIL'} ${v.law}: ${v.proven ? `proven, ${v.ms} ms (${v.scheme}${v.lemmas.length ? `; lemmas: ${v.lemmas.join('; ')}` : ''})` : `not proven (${v.goal}: ${v.stuck})`}`)
    failed ||= !ok
  }
  for (const [name, mk] of [...Object.entries(broken), ...Object.entries(throughBroken).map(([n, f]) => [`${n} (through)`, f] as const)]) {
    if (skip(name)) continue
    const v = proveData(mk())
    console.log(`${!v.proven ? 'ok  ' : 'FAIL'} ${v.law} (broken): ${v.proven ? 'proven' : `refused${v.counterexample ? `, broken at ${JSON.stringify(v.counterexample)}` : ''}`}`)
    failed ||= v.proven
  }
  for (const [name, mk] of Object.entries(wellFounded)) {
    if (skip(name)) continue
    const v = proveData(mk()), ok = v.proven && v.checked
    console.log(`${ok ? 'ok  ' : 'FAIL'} ${v.law}: ${v.proven ? `proven, ${v.ms} ms (${v.scheme})` : `not proven (${v.goal}: ${v.stuck})`}`)
    failed ||= !ok
  }
  for (const [name, mk] of [...Object.entries(nonterminating), ...Object.entries(adversarial)]) {
    if (skip(name)) continue
    const why = refusal(mk)
    console.log(`${why ? 'ok  ' : 'FAIL'} ${name} (doesn't terminate): ${why ? `refused: ${why}` : 'taken'}`)
    failed ||= !why
  }
  if (failed) process.exit(1)
}
