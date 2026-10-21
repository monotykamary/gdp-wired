// Debugging: a law of examples/data.ts with lemmas given (never what the corpus does): bun research/data/withlemma.ts <law>
import {laws, List, Tree, app, sum, rev} from '../../examples/data.ts'
import {law, proveData, natural, type DataLaw, type Nat, type Val} from '../../core/data.ts'
const N = (v: unknown) => v as Nat, L = (v: unknown) => v as Val
const given: Record<string, DataLaw[]> = {
  sumFlatten: [law('sum of append', {a: List, b: List}, ({a, b}) => N(sum(app(a, b))).eq(N(sum(a)).plus(N(sum(b)))))],
  reverseReverse: [law('reverse of append one', {a: List, n: natural}, ({a, n}) => L(rev(app(a, List.cons(n, List.nil)))).eq(List.cons(n, rev(a))))],
}
void Tree
const name = process.argv[2]!
const v = proveData((laws as Record<string, () => DataLaw>)[name]!(), {lemmas: given[name], ms: 60000})
console.log(JSON.stringify({proven: v.proven, ms: v.ms, scheme: v.scheme, lemmas: v.lemmas, goal: v.goal, stuck: v.stuck}))
