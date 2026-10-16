import {checkRefutation} from '../core/check.ts'
import {type Law, type Machine, all, any, bit, get, ite, less, n, not, plus, prove, same, search, x} from '../core/machine.ts'
import {admit, admitFlagged} from '../core/models.ts'
import {product} from './relational.ts'

function verdict(m: Machine, goals: Law[], invariants: Law[], depth = 3, bound = 2) {
  const proofs = goals.map(g => prove(m, g, invariants))
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

const t0 = performance.now()
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
console.log(`  caps rule, others anywhere           ${verdict(isolation(true, false), [sees], bKeys, 2, 1)}`)
console.log(`  caps rule, others at other providers ${verdict(isolation(false, false), [sees], bKeys, 2, 1)}`)
console.log(`  per-account cap only, others anywhere ${verdict(isolation(true, true), [sees], [sees], 2, 1)}`)
console.log(`(${Math.round(performance.now() - t0)} ms)`)
