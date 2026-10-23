// The lemma use a case node loses (compare/tip/README.md, lang/edges: why tip2015/list_assoc isn't proven): bind over an
// append, (a ++ b) >>= g = (a >>= g) ++ (b >>= g), with ++ associative given as a lemma. With g's values a recursive
// function of the element (`W=x`: rep x) it is proven; with an unknown's (`W=g`: rep (g x)) it isn't: in the case
// a = x :: t, b = [] the use of associativity it needs holds in 15 of the node's 24 models and is ranked under uses
// that hold in 19, and the case keeps four (lemmaCaps.perCase). `DATA_TRACE=1` shows the attempts.
//   W=x bun research/edges/lemma-case.ts; W=g bun research/edges/lemma-case.ts
import {type Nat, type Val, data, define, fnParam, law, natural, self, proveData} from '../../core/data.ts'
const L = (v: unknown) => v as Val, N = (v: unknown) => v as Nat
const List = data('List', {nil: {}, cons: {head: natural, tail: self}})
const g = fnParam('g')
const rep: ReturnType<typeof define> = define('rep', {n: natural}, List, ({n}) => N(n).match({zero: () => List.nil, succ: ({pred}) => List.cons(pred, rep(pred))}))
const app: ReturnType<typeof define> = define('app', {xs: List, ys: List}, List, ({xs, ys}) => L(xs).match({nil: () => L(ys), cons: ({head, tail}) => List.cons(head, app(tail, ys))}))
const G = (x: unknown) => (process.env.W === 'x' ? rep(x as Nat) : rep(g(x as Nat)))
const bindG: ReturnType<typeof define> = define('bindG', {xs: List}, List, ({xs}) => L(xs).match({nil: () => List.nil, cons: ({head, tail}) => L(app(G(head), bindG(tail)))}))
const assoc = law('assoc', {a: List, b: List, c: List}, ({a, b, c}) => L(app(app(a, b), c)).eq(L(app(a, app(b, c)))))
const v = proveData(law('dist', {a: List, b: List}, ({a, b}) => L(bindG(app(a, b))).eq(L(app(bindG(a), bindG(b))))), {ms: 20000, lemmas: [assoc], transfer: false})
console.log(process.env.W ?? 'g', v.proven && v.checked ? `proven (${v.scheme})` : `not proven (${v.goal}: ${v.stuck})`)
