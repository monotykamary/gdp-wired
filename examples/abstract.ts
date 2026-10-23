// Abstract sorts, unknown functions and closures in the datatype language (core/data.ts): what an automatic prover can
// still say about values it may not look into, and about functions it is not given. For the suite (`bun
// examples/abstract.ts`), core/abstract.test.ts and research/edges/lean-edges.ts (each proof checked again in Lean).
//   - an abstract sort (`opaque`): lists of elements compared by equality alone, so each law holds for every element
//     sort, not only for the naturals the kernel encodes them as (core/data.ts says why); reading an element any other
//     way (its order, a constant of it) is refused
//   - an unknown constant of the sort (a default a lookup returns), an unknown function into a list (the list monad's
//     return), an unknown function between elements: each law is about every one of them
//   - closures (defunctionalisation): a pipeline whose stages are functions, held in a field of a datatype, each stage a
//     closure value and its application one function; with an unknown closure besides the named ones, a law about every
//     stage is about every function of a natural
// The broken variants (an order of elements, a constant element, an unknown function taken to be injective, a list
// function taken to return at most two items, two closures mixed up, every stage taken to grow) are refused, by the
// check or by a value that breaks them.
import {type Bool, type DataLaw, type Nat, type Val, closures, data, define, law, natural, boolean, opaque, proveData, self, unknownFn, when} from '../core/data.ts'

const L = (v: unknown) => v as Val, N = (v: unknown) => v as Nat, B = (v: unknown) => v as Bool

// Elements of an abstract sort, and lists of them.
export const Elem = opaque('Elem')
export const Elems = data('Elems', {nil: {}, cons: {head: Elem, tail: self}})
export const mem: ReturnType<typeof define> = define('mem', {x: Elem, xs: Elems}, boolean, ({x, xs}) => L(xs).match({nil: () => L(x).ne(L(x)), cons: ({head, tail}) => L(head).eq(L(x)).or(B(mem(x, tail)))}))
export const cat: ReturnType<typeof define> = define('cat', {xs: Elems, ys: Elems}, Elems, ({xs, ys}) => L(xs).match({nil: () => L(ys), cons: ({head, tail}) => Elems.cons(head, cat(tail, ys))}))
export const count: ReturnType<typeof define> = define('count', {x: Elem, xs: Elems}, natural, ({x, xs}) => L(xs).match({nil: () => 0, cons: ({head, tail}) => when(L(head).eq(L(x)), N(count(x, tail)).plus(1), N(count(x, tail)))}))
// The first element, or an unknown default (a constant of the sort: the law is about every default).
export const none = unknownFn('none', [], Elem)
export const first = define('first', {xs: Elems}, Elem, ({xs}) => L(xs).match({nil: () => L(none()), cons: ({head}) => L(head)}))
// The list monad's bind at an unknown function of an element into a list, and return.
export const f = unknownFn('f', [Elem], Elems)
export const bindF: ReturnType<typeof define> = define('bindF', {xs: Elems}, Elems, ({xs}) => L(xs).match({nil: () => Elems.nil, cons: ({head, tail}) => L(cat(f(head), bindF(tail)))}))
// An unknown function between elements, mapped over a list.
export const h = unknownFn('h', [Elem], Elem)
export const mapH: ReturnType<typeof define> = define('mapH', {xs: Elems}, Elems, ({xs}) => L(xs).match({nil: () => Elems.nil, cons: ({head, tail}) => Elems.cons(L(h(head)), mapH(tail))}))
export const len: ReturnType<typeof define> = define('len', {xs: Elems}, natural, ({xs}) => L(xs).match({nil: () => 0, cons: ({tail}) => N(len(tail)).plus(1)}))

// A pipeline of stages, each a function of a natural held in a field: the closures `inc`, `add k`, and any other.
export const {data: Op, apply} = closures('Op', {x: natural}, natural, {
  inc: {apply: (_, {x}) => N(x).plus(1)},
  add: {fields: {k: natural}, apply: ({k}, {x}) => N(x).plus(N(k))},
}, {unknown: 'other'})
export const Stages = data('Stages', {done: {}, then: {op: Op, rest: self}})
export const run: ReturnType<typeof define> = define('run', {s: Stages, x: natural}, natural, ({s, x}) => L(s).match({done: () => N(x), then: ({op, rest}) => N(run(rest, apply(op, x)))}))
export const join: ReturnType<typeof define> = define('join', {s: Stages, t: Stages}, Stages, ({s, t}) => L(s).match({done: () => L(t), then: ({op, rest}) => Stages.then(op, join(rest, t))}))

export const laws = {
  // x is a member of a list that starts with it; a member of xs is one of xs ++ ys; ++ is associative
  memCons: () => law('mem x (x :: xs)', {x: Elem, xs: Elems}, ({x, xs}) => B(mem(x, Elems.cons(x, xs)))),
  memCat: () => law('mem x xs ⇒ mem x (xs ++ ys)', {x: Elem, xs: Elems, ys: Elems}, ({x, xs, ys}) => B(mem(x, xs)).implies(B(mem(x, cat(xs, ys))))),
  catAssoc: () => law('(xs ++ ys) ++ zs = xs ++ (ys ++ zs)', {xs: Elems, ys: Elems, zs: Elems}, ({xs, ys, zs}) => L(cat(cat(xs, ys), zs)).eq(L(cat(xs, cat(ys, zs))))),
  countCat: () => law('count x (xs ++ ys) = count x xs + count x ys', {x: Elem, xs: Elems, ys: Elems}, ({x, xs, ys}) => N(count(x, cat(xs, ys))).eq(N(count(x, xs)).plus(N(count(x, ys))))),
  // the first of x :: xs is x, whatever the default
  firstCons: () => law('first (x :: xs) = x', {x: Elem, xs: Elems}, ({x, xs}) => L(first(Elems.cons(x, xs))).eq(L(x))),
  // return: [x] >>= f = f x, for every f
  bindReturn: () => law('[x] >>= f = f x', {x: Elem}, ({x}) => L(bindF(Elems.cons(x, Elems.nil))).eq(L(f(x)))),
  // a map keeps the length, for every h
  mapLength: () => law('len (map h xs) = len xs', {xs: Elems}, ({xs}) => N(len(mapH(xs))).eq(N(len(xs)))),
  // two pipelines joined run one after the other, whatever their stages; inc is add 1
  runJoin: () => law('run (s ++ t) x = run t (run s x)', {s: Stages, t: Stages, x: natural}, ({s, t, x}) => N(run(join(s, t), x)).eq(N(run(t, run(s, x))))),
  incIsAdd: () => law('apply inc x = apply (add 1) x', {x: natural}, ({x}) => N(apply(Op.inc, x)).eq(N(apply(Op.add(1), x)))),
}
export const broken = {
  // a law about every element sort can't say two distinct ones are ordered, nor name one (refused: no proof is tried)
  ordered: () => law('x ≠ y ⇒ x < y or y < x', {x: Elem, y: Elem}, ({x, y}) => L(x).ne(L(y)).implies(N(L(x).match({el: ({code}) => code as Nat})).lt(N(L(y).match({el: ({code}) => code as Nat}))))),
  named: () => law('first [] = el 0', {x: Elem}, () => L(first(Elems.nil)).eq(Elem.make('el', 0))),
  // false for some f, h, default or closure: refuted
  injective: () => law('h x = h y ⇒ x = y', {x: Elem, y: Elem}, ({x, y}) => L(h(x)).eq(L(h(y))).implies(L(x).eq(L(y)))),
  shortLists: () => law('len (f x) ≤ 2', {x: Elem}, ({x}) => N(len(f(x))).atMost(2)),
  mixedUp: () => law('apply inc x = apply (add 2) x', {x: natural}, ({x}) => N(apply(Op.inc, x)).eq(N(apply(Op.add(2), x)))),
  grows: () => law('x ≤ apply op x', {op: Op, x: natural}, ({op, x}) => N(x).atMost(N(apply(op, x)))),
}

if (import.meta.main) {
  let failed = false
  for (const mk of Object.values(laws)) {
    const v = proveData((mk as () => DataLaw)()), ok = v.proven && v.checked
    console.log(`${ok ? 'ok  ' : 'FAIL'} ${v.law}: ${v.proven ? `proven, ${v.ms} ms (${v.scheme}${v.lemmas.length ? `; lemmas: ${v.lemmas.join('; ')}` : ''})` : `not proven (${v.goal}: ${v.stuck})`}`)
    failed ||= !ok
  }
  for (const [name, mk] of Object.entries(broken)) {
    let why: string
    try { const v = proveData(mk()); why = v.proven ? '' : v.counterexample ? `refuted at ${JSON.stringify(v.counterexample)}` : '' } catch (e) { why = `refused: ${(e as Error).message}` }
    console.log(`${why ? 'ok  ' : 'FAIL'} ${name} (broken): ${why || 'not refused'}`)
    failed ||= !why
  }
  if (failed) process.exit(1)
}
