// Abstract sorts, unknown functions and closures (core/data.ts, examples/abstract.ts): laws proven at every element
// sort, function and closure; and false laws that a wrong encoding would prove, each refused (the sort read beyond
// equality) or refuted (a value that breaks it).
import {expect, test} from 'bun:test'
import {type Bool, type DataLaw, type Nat, type Val, type Value, data, define, evalX, law, natural, boolean, proveData, self, unknownFn} from './data.ts'
import {Elem, Elems, broken, cat, f, first, h, laws, len, none} from '../examples/abstract.ts'

const L = (v: unknown) => v as Val, N = (v: unknown) => v as Nat
const refuted = (l: DataLaw) => { const v = proveData(l, {ms: 4000}); expect(v.proven).toBe(false); expect(v.counterexample).toBeDefined() }
const refused = (mk: () => DataLaw, why: RegExp) => expect(mk).toThrow(why)

test('laws at every element sort, function and closure are proven', () => {
  for (const mk of [laws.memCons, laws.memCat, laws.catAssoc, laws.firstCons, laws.mapLength, laws.runJoin, laws.incIsAdd]) expect(proveData(mk())).toMatchObject({proven: true, checked: true})
}, 120_000)

test('an abstract sort read beyond equality is refused', () => {
  const beyond = /an abstract sort, beyond equality/
  // an order, a constant, a size, a function the law reaches that reads the code
  refused(broken.ordered, beyond)
  refused(broken.named, beyond)
  refused(() => law('size x = 1', {x: Elem}, ({x}) => L(x).size().eq(1)), beyond)
  const code = define('codeOfElem', {x: Elem}, natural, ({x}) => L(x).match({el: ({code: c}) => c as Nat}))
  refused(() => law('code x ≤ code x + 1', {x: Elem}, ({x}) => N(code(x)).atMost(N(code(x)).plus(1))), beyond)
  refused(() => law('first [] is el', {x: Elem}, () => L(first(Elems.nil)).is('el')), beyond)
})

test('false laws a wrong abstract sort, unknown or closure would prove are refuted', () => {
  // true where the sort has two elements, false at three
  refuted(law('at most two elements', {x: Elem, y: Elem, z: Elem}, ({x, y, z}) => L(x).eq(L(y)).or(L(y).eq(L(z)), L(x).eq(L(z)))))
  // the default is an element like any other
  refuted(law('every element is the default', {x: Elem}, ({x}) => L(x).eq(L(none()))))
  const other = unknownFn('otherDefault', [], Elem)
  refuted(law('two defaults are one', {x: Elem}, () => L(none()).eq(L(other()))))
  // an unknown function is any function: not injective, not an involution, not constant, its lists of any length
  refuted(broken.injective())
  refuted(law('h (h x) = x', {x: Elem}, ({x}) => L(h(h(x))).eq(L(x))))
  refuted(law('f x = f y', {x: Elem, y: Elem}, ({x, y}) => L(f(x)).eq(L(f(y)))))
  refuted(broken.shortLists())
  refuted(law('f x ++ f x = f x', {x: Elem}, ({x}) => L(cat(f(x), f(x))).eq(L(f(x)))))
  const p = unknownFn('somewhere', [Elem], boolean)
  refuted(law('p x or p y', {x: Elem, y: Elem}, ({x, y}) => (p(x) as Bool).or(p(y) as Bool)))
  // two closures told apart; every closure includes every function (other), so none of them need grow
  refuted(broken.mixedUp())
  refuted(broken.grows())
  refuted(law('len (f x) = len (f y) ⇒ f x = f y', {x: Elem, y: Elem}, ({x, y}) => N(len(f(x))).eq(N(len(f(y)))).implies(L(f(x)).eq(L(f(y))))))
}, 60_000)

test('an unknown function into a datatype takes every value (the decoding is onto)', () => {
  // A list [3, 1, 4] at key 7: the table that makes it (depth, then each node's constructor and natural, by place),
  // read back through the decoder as the search and refute read it.
  const List = data('NatsForOnto', {nil: {}, cons: {head: natural, tail: self}})
  const u = unknownFn('onto', [natural], List)
  const pair = (a: number, b: number) => (a + b) * (a + b) + b, B = 2, table = new Map<number, number>()
  const want = [3, 1, 4], a = 7
  table.set(pair(a, 0), want.length + 1)
  let place = 0
  for (const x of want) { table.set(pair(a, 3 * place + 1), 1); table.set(pair(a, 3 * (B * place + 1) + 2), x); place = B * place + 2 }
  table.set(pair(a, 3 * place + 1), 0)
  const x = L(u(a)).x
  const v = evalX(x, new Map(), {onto: (n: number) => table.get(n) ?? 0}) as Value
  const back = (w: Value): number[] => (typeof w === 'object' && w.c === 1 ? [w.f[0] as number, ...back(w.f[1]!)] : [])
  expect(List.ctors.map(c => c.name)).toEqual(['nil', 'cons'])
  expect(back(v)).toEqual(want)
})
