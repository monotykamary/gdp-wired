import {forall, proveRule} from '../../../core/dsl.ts'
import {withWall} from '../../../kernel/prove.ts'
import {protocols, tabR} from '../../../research/protocols/ic3syn/models.ts'
import {below} from '../../../research/protocols/ic3syn/common.ts'
const wall = Number(process.argv[2] ?? 60000), id = process.argv[3] ?? 'learning_switch'
const p = protocols.find(q => q.id === id)!
const r: any = p.make()
const hand = id === 'learning_switch' ? [
  r.law('pending: the source routes back', ({size, T, P}: any) => forall((ps, pd, s, d) => below(size, ps, pd, s, d).and(P.has(ps, pd, s, d), ps.eq(s).not()).implies(tabR(T, ps, s, ps)))),
  r.law('a route leads back to the root', ({size, T}: any) => forall((t, x, y) => below(size, t, x, y).and(tabR(T, t, x, y), t.eq(y).not(), x.eq(y).not()).implies(tabR(T, t, y, t)))),
] : [
  r.law('the root has no successor', ({size, T, started}: any) => forall((a, b) => started.eq(1).and(below(size, a, b), tabR(T, b, b, a)).implies(a.eq(b)))),
  r.law('no route without a domain', ({size, T, Dom, started}: any) => forall((c, a, b) => started.eq(1).and(below(size, a, b, c), tabR(T, c, a, b), Dom.has(c, a).not()).implies(a.eq(b)))),
  r.law('a pending packet routes back to its source or is in its domain', ({size, packets, T, Dom, Src, Pend, started}: any) => forall((q, c, a) => started.eq(1).and(q.lt(packets), below(size, c, a), Pend.has(q, c, a))
    .implies(tabR(T, Src.at(q).minus(1), c, Src.at(q).minus(1)).or(Dom.has(Src.at(q).minus(1), c))))),
  r.law('nothing before the start', ({size, packets, T, Dom, Pend, started}: any) => forall((q, a, b) => started.eq(0).implies(T.has(q, a, b).not().and(Dom.has(a, b).not(), Pend.has(q, a, b).not())))),
  r.law('a domain routes to its root', ({size, T, Dom, started}: any) => forall((b, c) => started.eq(1).and(below(size, b, c), Dom.has(b, c)).implies(tabR(T, b, c, b)))),
]
const laws = [...p.laws(r), ...hand]
const t0 = performance.now()
const v: any = withWall(performance.now() + wall, () => proveRule(r, laws, {search: false}))
console.log(JSON.stringify({id, proven: v.proven, goal: v.goal, why: String(v.why ?? '').slice(0, 200), ms: Math.round(performance.now() - t0)}))
if (process.env.FAIL) {
  const {proveLaws} = await import('../../../kernel/prove.ts')
  const o: any = proveLaws(r.machine, laws.map((l: any) => l.law ?? l))
  console.log(o.proven, JSON.stringify(o.failed).slice(0, 4000))
}
