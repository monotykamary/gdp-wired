import {checkRefutation} from '../../core/check.ts'
import {type Law, type Machine, all, any, atMost, bit, get, ite, less, min, minus, n, not, plus, prove, same, search, x} from '../../core/machine.ts'
import {admit, admitFlagged, boundedLoss, loss} from '../../core/models.ts'
import {agree, product} from './relational.ts'

function verdict(m: Machine, goals: Law[], invariants: Law[], depth = 3, bound = 2) {
  // Every invariant a proof assumes is proven too: the set is inductive together, or nothing is claimed.
  const proofs = [...new Set([...goals, ...invariants])].map(g => prove(m, g, invariants))
  if (proofs.every(p => p.proven)) {
    const checked = proofs.every(p => p.obligations.every(o => o.verdict.kind === 'refuted' && checkRefutation(o.constraints, o.verdict.steps)))
    const cases = proofs.reduce((s, p) => s + p.obligations.length, 0)
    return `PROVEN  (${cases} cases, ${checked ? 'all certificates checked' : 'NOT CHECKED'})`
  }
  for (const g of goals) {
    const found = search(m, g, depth, bound)
    if (found) return `REFUTED ${g.name}: params ${JSON.stringify(found.params)}, requests ${JSON.stringify(found.trace)}`
  }
  return 'NOT PROVEN (no counterexample found in the search bounds)'
}

console.log('Migration safety: the refactored machine agrees with the budget rule on every history')
const v1 = loss()
const refactors: [string, Machine][] = [
  ['min as an if, branches swapped', {...v1, name: 'v2', step: {state: {s: ite(atMost(x('b'), x('s')), x('s'), plus(x('s'), ite(less(x('m'), x('c')), x('m'), x('c'))))}}}],
  ['s <= b - 1 instead of s < b', {...v1, name: 'v3', step: {state: {s: ite(atMost(x('s'), minus(x('b'), n(1))), plus(x('s'), min(x('c'), x('m'))), x('s'))}}}],
  ['the derived guard s <= b', {...v1, name: 'v4', step: {state: {s: ite(atMost(x('s'), x('b')), plus(x('s'), min(x('c'), x('m'))), x('s'))}}}],
]
for (const [what, v] of refactors) {
  const p = product(v1, v)
  console.log(`  ${what.padEnd(34)} ${verdict(p, agree(v1), agree(v1))}`)
  if (what.includes('derived')) console.log(`  ${''.padEnd(34)} and on its own, bounded_loss: ${verdict(v, [boundedLoss], [boundedLoss])}`)
}
const a1 = admit()
const a2: Machine = (() => {
  // A refactor: count + 1 <= cap instead of count < cap, the checks in another order.
  const caps = [['Dom', 'dom', x('dm')], ['Hour', 'hour', x('hr')], ['Day', 'day', x('d')], ['Acct', 'acct', n(1)]] as const
  const granted = all(...caps.map(([k, f, cap]) => atMost(plus(get(k, x(f)), n(1)), cap)), same(x('ok'), n(1)))
  return {...a1, name: 'admit v2', step: {maps: Object.fromEntries(caps.map(([k, f]) => [k, {key: x(f), value: ite(granted, plus(get(k, x(f)), n(1)), get(k, x(f)))}]))}}
})()
console.log(`  ${'caps rule, checks reordered, +1 <='.padEnd(34)} ${verdict(product(admitFlagged(), {...a2, step: {flags: {granted: (a2.step.maps!.Acct!.value as any).c}, maps: Object.fromEntries(Object.entries(a2.step.maps!).map(([k, w]) => [k, {...w, value: {...(w.value as any), c: {op: 'flag', name: 'granted'}}}]))}}), agree(a1), agree(a1))}`)

console.log('\nTenant isolation: what account B gets is the same whether or not anyone else signs up')
// Copy a sees every request; copy b sees only B's (others' requests can't be granted there). who = 0 is B's request.
const isolation = (sameProvider: boolean, perAccountOnly: boolean): Machine => {
  const base = perAccountOnly ? {...admit(), step: {maps: {Acct: {key: x('acct'), value: ite(all(same(x('ok'), n(1)), less(get('Acct', x('acct')), n(1))), plus(get('Acct', x('acct')), n(1)), get('Acct', x('acct')))}}}} : admitFlagged()
  const mine = all(same(x('who'), n(0)), same(x('acct'), x('Bacct')), same(x('day'), x('Bday')), same(x('hour'), x('Bhour')), same(x('dom'), x('Bdom')))
  const others = all(same(x('who'), n(1)), not(same(x('acct'), x('Bacct'))),
    ...(sameProvider ? [] : [not(same(x('day'), x('Bday'))), not(same(x('hour'), x('Bhour'))), not(same(x('dom'), x('Bdom')))]))
  return product(base, base, {
    name: 'isolation', params: ['Bacct', 'Bday', 'Bhour', 'Bdom'], inputs: ['who'],
    bInputs: {ok: ite(same(x('who'), n(1)), n(0), x('ok'))}, assume: all(bit('who'), any(mine, others)),
  })
}
const sees: Law = {name: "B's grant: a.Acct[B] = b.Acct[B]", holds: same(get('a_Acct', x('Bacct')), get('b_Acct', x('Bacct')))}
const atB = (k: string, key: string): Law => ({name: `a.${k}[B] = b.${k}[B]`, holds: same(get(`a_${k}`, x(key)), get(`b_${k}`, x(key)))})
const bKeys: Law[] = [sees, atB('Day', 'Bday'), atB('Hour', 'Bhour'), atB('Dom', 'Bdom')]
console.log(`  caps rule, others anywhere           ${verdict(isolation(true, false), bKeys, bKeys, 2, 1)}`)
console.log(`  caps rule, others at other providers ${verdict(isolation(false, false), bKeys, bKeys, 2, 1)}`)
console.log(`  per-account cap only, others anywhere ${verdict(isolation(true, true), [sees], [sees], 2, 1)}`)
