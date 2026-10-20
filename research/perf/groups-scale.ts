// Two groups of effects decided at every pair (examples/groups.ts), at the sizes a supervisor sends: the compiled group
// rule (its names compared through a join on equal names), the same rule with the names compared as two orders (every
// pair of rows read, as before the join), and the loop over every pair of the pair rule. Disjoint ordered effects, so
// nothing stops early. Each answer is checked against the others.
//   bun research/perf/groups-scale.ts
import {all, everyKey, rule, when} from '../../core/dsl.ts'
import {Effect, Row, groups, pair, type Held} from '../../examples/groups.ts'

// The group rule with x = y written as neither x < y nor y < x: the compiler sees no equality, so it reads every pair.
const nested = rule('resource groups, names compared by order')
  .carriesList('L', Effect).carriesList('R', Effect).carriesList('LN', Row).carriesList('RN', Row)
  .state({conflict: 0})
  .flags(({L, R, LN, RN}) => {
    const c = (l: ReturnType<typeof L.at>, r: ReturnType<typeof L.at>) => all(l.effect, r.effect, l.ordered.or(r.ordered))
    return {
      rows: everyKey(p => p.lt(LN.len).implies(LN.at(p).item.lt(L.len))).and(everyKey(q => q.lt(RN.len).implies(RN.at(q).item.lt(R.len)))),
      known: everyKey((i, j) => all(i.lt(L.len), j.lt(R.len)).implies(all(c(L.at(i), R.at(j)), L.at(i).exact.and(R.at(j).exact).not()).not())),
      unshared: everyKey((p, q) => all(p.lt(LN.len), q.lt(RN.len), LN.at(p).name.lt(RN.at(q).name).not(), RN.at(q).name.lt(LN.at(p).name).not())
        .implies(c(L.at(LN.at(p).item), R.at(RN.at(q).item)).not())),
    }
  })
  .assume(({rows}) => rows)
  .step(({known, unshared}) => ({conflict: when(known.and(unshared), 0, 1)}))

const g = groups(), gc = g.compiled(), nc = nested.compiled(), pc = pair.compiled()
const rowsOf = (side: Held[]) => side.flatMap((e, item) => (e.scope.exact ? e.scope.names : []).map(name => ({item, name})))
const effectsOf = (side: Held[]) => side.map(e => ({effect: e.effect, ordered: e.ordered, exact: e.scope.exact}))
const viaRule = (r: typeof g | typeof nested, c: typeof gc, left: Held[], right: Held[]) =>
  r.decode(c.step({}, c.init({}), r.encodeInput({L: effectsOf(left), R: effectsOf(right), LN: rowsOf(left), RN: rowsOf(right)} as never))).conflict === 1
const viaLoop = (left: Held[], right: Held[]) => left.some(l => right.some(r => pair.decode(pc.step({}, pc.init({}), pair.encodeInput({
  leftEffect: l.effect, rightEffect: r.effect, leftExact: l.scope.exact, rightExact: r.scope.exact, leftOrdered: l.ordered, rightOrdered: r.ordered,
  Left: new Set(l.scope.names), Right: new Set(r.scope.names),
} as never))).conflict === 1))

const side = (from: number, n: number, k: number): Held[] => Array.from({length: n}, (_, i) => ({effect: true, ordered: true, scope: {exact: true, names: Array.from({length: k}, (_, j) => from + i * k + j)}}))
const time = (f: () => boolean): [number, boolean] => { const t = performance.now(), out = f(); return [performance.now() - t, out] }
console.log('| Effects per side × names | Loop over pairs | Rule, every pair of rows | Rule, joined on names |')
console.log('|---|---|---|---|')
for (const [n, k] of [[32, 4], [256, 4], [256, 16], [256, 32], [256, 64]] as const) {
  const left = side(2, n, k), right = side(2 + n * k, n, k)
  viaRule(g, gc, left, right); viaLoop(left.slice(0, 2), right.slice(0, 2)) // warm up
  const [loop, a] = time(() => viaLoop(left, right)), [joined, b] = time(() => viaRule(g, gc, left, right))
  const [pairs, c] = time(() => viaRule(nested, nc, left, right))
  if (a !== b || b !== c) throw new Error(`n=${n} k=${k}: the loop says ${a}, the joined rule ${b}, the rule over every pair ${c}`)
  // and one shared name: every way says conflict
  const shared = side(2, n, k); shared[n - 1] = {...shared[n - 1]!, scope: {exact: true, names: [...right[n - 1]!.scope.names.slice(0, 1)]}}
  if (!viaRule(g, gc, shared, right) || !viaLoop(shared, right)) throw new Error(`n=${n} k=${k}: a shared name isn't a conflict`)
  const ms = (x: number) => (Number.isNaN(x) ? '—' : x < 10 ? `${x.toFixed(1)} ms` : x < 1000 ? `${Math.round(x)} ms` : `${(x / 1000).toFixed(2)} s`)
  console.log(`| ${n} × ${k} | ${ms(loop)} | ${ms(pairs)} | ${ms(joined)} |`)
}
