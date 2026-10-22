// The lemmas research/data/withlemma.ts and prof.ts give a law (debugging only: the corpus never gives a lemma).
import {List, Tree, app, sum, rev, allBelow, allAbove, bins} from '../../examples/data.ts'
import {law, natural, type Bool, type DataLaw, type Nat, type Val} from '../../core/data.ts'
const B = (v: unknown) => v as Bool, N = (v: unknown) => v as Nat, L = (v: unknown) => v as Val
export const given: Record<string, DataLaw[]> = {
  sumFlatten: [law('sum after one 0', {a: List}, ({a}) => N(sum(app(a, List.cons(0, List.nil)))).eq(N(sum(a)))), law('sum of append', {a: List, b: List}, ({a, b}) => N(sum(app(a, b))).eq(N(sum(a)).plus(N(sum(b)))))],
  bstInsert: [law('below kept', {t: Tree, v: natural, x: natural}, ({t, v, x}) => B(allBelow(t, v)).and(N(x).lt(v)).implies(B(allBelow(bins(x, t), v)))), law('above kept', {t: Tree, v: natural, x: natural}, ({t, v, x}) => B(allAbove(t, v)).and(N(v).lt(x)).implies(B(allAbove(bins(x, t), v))))],
  reverseReverse: [law('reverse of append one', {a: List, n: natural}, ({a, n}) => L(rev(app(a, List.cons(n, List.nil)))).eq(List.cons(n, rev(a))))],
}
