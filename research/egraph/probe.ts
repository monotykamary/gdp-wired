import {data, define, law, natural, self, proveData, type Val} from '../../core/data.ts'
import {withWall} from '../../kernel/prove.ts'
const List = data('AstraList', {nil: {}, cons: {head: natural, tail: self}})
const app = define('astraAppend', {xs: List, ys: List}, List, ({xs, ys}) => (xs as Val).match({nil: () => ys as Val, cons: ({head, tail}) => List.cons(head, app(tail, ys))}))
const rev = define('astraReverse', {xs: List}, List, ({xs}) => (xs as Val).match({nil: () => List.nil, cons: ({head, tail}) => app(rev(tail), List.cons(head, List.nil)) as Val}))
const lemma = law('astra reverse append one', {a: List, n: natural}, ({a, n}) => (rev(app(a, List.cons(n, List.nil))) as Val).eq(List.cons(n, rev(a))))
const v = withWall(performance.now() + 20000, () => proveData(lemma, {lemmas: false, ms: 10000}))
console.log(JSON.stringify(v))
