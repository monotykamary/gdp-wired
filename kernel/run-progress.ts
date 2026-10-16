// "There is a request that…": no lockout and progress, proven by naming the request. The laws each proof assumes are
// proven inductive first, by the same kernel.
import {type C, type E, type Law, type Machine, all, atMost, get, less, n, plus, same, times, x} from '../core/machine.ts'
import {admit, capLaws, inflight, inflightLoss} from '../core/models.ts'
import {check, progressObligations} from './kernel.ts'
import {countLeaves, grow, proveLaws} from './prove.ts'

function progress(what: string, m: Machine, laws: Law[], instances: Record<string, E[]>, p: {when: C, then: C, request: Record<string, E>}) {
  const base = proveLaws(m, laws)
  if (!base.proven || !base.checked) return console.log(`  ${what.padEnd(52)} the assumed laws aren't inductive`)
  let leaves = 0
  for (const g of progressObligations(m, laws, instances, {name: what, ...p})) {
    const out = grow(g)
    if (!('tree' in out)) return console.log(`  ${what.padEnd(52)} STUCK    ${g.name.slice(what.length + 2)}: ${out.stuck} ${JSON.stringify(Object.fromEntries(Object.entries(out.witness ?? {}).filter(([, v]) => v !== 0)))}`)
    if (!check(g, out.tree)) return console.log(`  ${what.padEnd(52)} kernel REJECTS`)
    leaves += countLeaves(out.tree)
  }
  console.log(`  ${what.padEnd(52)} PROVEN   ${leaves} leaves (+ ${base.leaves} for the laws), kernel accepts`)
}

console.log('Progress and no lockout')
const strong: Law = {name: 's + 50p <= b + 150', holds: atMost(plus(x('s'), times(50, x('p'))), plus(x('b'), n(150)))}
const flight = [inflightLoss, strong]
progress('in-flight: a request in flight can always complete', inflight, flight, {}, {when: atMost(n(1), x('p')), then: less(x("p'"), x('p')), request: {t: n(0), done: n(1)}})
progress('in-flight: under budget with room, one is admitted', inflight, flight, {}, {when: all(less(x('s'), x('b')), less(x('p'), n(3))), then: same(x("p'"), plus(x('p'), n(1))), request: {t: n(0), done: n(0)}})
progress('in-flight: with none in flight, one completes (false)', inflight, flight, {}, {when: same(x('p'), n(0)), then: less(x("p'"), x('p')), request: {t: n(0), done: n(1)}})
const keys = {A: x('A'), D: x('D'), H: x('H'), M: x('M')}
const under = all(less(get('Acct', keys.A), n(1)), less(get('Day', keys.D), x('d')), less(get('Hour', keys.H), x('hr')), less(get('Dom', keys.M), x('dm')))
const inst = Object.fromEntries(capLaws.map(l => [l.name, [keys.A, keys.D, keys.H, keys.M]]))
progress('admit: an account under every cap gets its grant', admit(), capLaws, inst, {when: under, then: same(get("Acct'", keys.A), n(1)), request: {acct: keys.A, day: keys.D, hour: keys.H, dom: keys.M, ok: n(1)}})
progress('admit: ... even with the day full (false)', admit(), capLaws, inst, {when: all(less(get('Acct', keys.A), n(1)), less(get('Hour', keys.H), x('hr')), less(get('Dom', keys.M), x('dm'))), then: same(get("Acct'", keys.A), n(1)), request: {acct: keys.A, day: keys.D, hour: keys.H, dom: keys.M, ok: n(1)}})
