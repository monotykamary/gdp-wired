// Recursive datatypes as values (core/data.ts): lists and trees declared with their constructors, functions over them by
// structural recursion, and laws stated about them and nothing else. Each law is proven by a cyclic proof the search
// finds (which argument to induct on, where each cycle returns, the lemmas the law needs), or refuted by a value that
// breaks it. For the suite (`bun examples/data.ts`), core/data.test.ts, research/frontier/corpus.ts and
// lean-kernel/package-check.ts.
//   - lists: length, append, reverse, a map by an unknown function f, sum, sorted insertion, counting an item
//   - trees: a node's value between its subtrees; mirror, size, flatten (in order), sum, insertion into a search tree
// The broken variants (an append that drops the head, a reverse that repeats it, a mirror that adds 1, an insertion that
// puts the item first, a search tree insertion that goes the wrong way) are refused with a value that breaks the law.
// The search tree's insertion law is the one the search doesn't prove (`open`).
import {type Bool, type DataLaw, type Nat, type Val, data, define, fnParam, law, natural, boolean, self, when, yes, proveData} from '../core/data.ts'

export const List = data('List', {nil: {}, cons: {head: natural, tail: self}})
export const Tree = data('Tree', {leaf: {}, node: {left: self, value: natural, right: self}})
const L = (v: unknown) => v as Val, N = (v: unknown) => v as Nat, B = (v: unknown) => v as Bool

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
} satisfies Record<string, (...a: never[]) => DataLaw>

export const broken = {
  lengthAppend: () => laws.lengthAppend(append('drops the head')),
  reverseReverse: () => laws.reverseReverse(reverse('repeats the head')),
  mirrorMirror: () => laws.mirrorMirror(mirror('adds one')),
  insertSorted: () => laws.insertSorted(insert('puts the item first')),
  bstInsert: () => laws.bstInsert(bstInsert('goes the wrong way')),
}

// Not proven by the search within its time: the two lemmas it needs (allBelow and allAbove kept by an insertion under
// a comparison) are found and proven, the law with them is not (research/frontier/README.md).
export const open = new Set(['bstInsert'])

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
  for (const [name, mk] of Object.entries(broken)) {
    if (skip(name)) continue
    const v = proveData(mk())
    console.log(`${!v.proven ? 'ok  ' : 'FAIL'} ${v.law} (broken): ${v.proven ? 'proven' : `refused${v.counterexample ? `, broken at ${JSON.stringify(v.counterexample)}` : ''}`}`)
    failed ||= v.proven
  }
  if (failed) process.exit(1)
}
