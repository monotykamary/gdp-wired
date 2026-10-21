// Debugging: one lemma of the search proven as a law of its own: bun research/data/lemma.ts <name>
import {List, app, rev, sum} from '../../examples/data.ts'
import {law, natural, proveData, type DataLaw, type Nat, type Val} from '../../core/data.ts'
const N = (v: unknown) => v as Nat, L = (v: unknown) => v as Val
const lemmas: Record<string, () => DataLaw> = {
  revSnoc: () => law('reverse of append one', {a: List, n: natural}, ({a, n}) => L(rev(app(a, List.cons(n, List.nil)))).eq(List.cons(n, rev(a)))),
  sumApp: () => law('sum of append', {a: List, b: List}, ({a, b}) => N(sum(app(a, b))).eq(N(sum(a)).plus(N(sum(b))))),
}
const v = proveData(lemmas[process.argv[2]!]!(), {lemmas: false, ms: 60000})
console.log(JSON.stringify({proven: v.proven, ms: v.ms, scheme: v.scheme, goal: v.goal, stuck: v.stuck}))
