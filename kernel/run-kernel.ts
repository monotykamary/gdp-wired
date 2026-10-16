// Every earlier machine proof again, now as kernel-checked trees: the prover is untrusted, kernel.ts + check.ts decide.
import {type Law, type Machine, all, any, atMost, bit, get, ite, less, min, minus, n, not, plus, same, search, times, x} from '../core/machine.ts'
import {admit, admitFlagged, boundedLoss, capLaws, inflight, inflightLoss, loss} from '../core/models.ts'
import {agree, product} from '../next/relational.ts'
import {check, obligations} from './kernel.ts'
import {proveLaws} from './prove.ts'

function run(what: string, m: Machine, laws: Law[]) {
  const t0 = performance.now()
  const r = proveLaws(m, laws)
  const ms = Math.round(performance.now() - t0)
  const verdict = r.proven ? `PROVEN   ${r.leaves} leaves, kernel ${r.checked ? 'accepts' : 'REJECTS'}` : `STUCK    ${r.failed!.goal}: ${r.failed!.stuck} ${r.failed!.witness ? JSON.stringify(Object.fromEntries(Object.entries(r.failed!.witness).filter(([, v]) => v !== 0))) : ''}`
  console.log(`  ${what.padEnd(44)} ${verdict}  (${ms} ms)`)
  return r
}

console.log('Single machines')
const lossProof = run('budget rule: bounded_loss', loss(), [boundedLoss])
run('caps rule: the 4 caps', admit(), capLaws)
run('caps rule, grant as a flag: the 4 caps', admitFlagged(), capLaws)
run('budget rule, max_tokens cap forgotten', loss(false), [boundedLoss])
run('caps rule, Day unguarded', admit(['Acct', 'Hour', 'Dom']), capLaws)
run('in-flight: the loss law alone', inflight, [inflightLoss])
const strong: Law = {name: 's + 50p <= b + 150', holds: atMost(plus(x('s'), times(50, x('p'))), plus(x('b'), n(150)))}
run('in-flight: with s + 50p <= b + 150', inflight, [inflightLoss, strong])

console.log('Migration safety')
const v1 = loss()
run('min as an if, branches swapped', product(v1, {...v1, step: {state: {s: ite(atMost(x('b'), x('s')), x('s'), plus(x('s'), ite(less(x('m'), x('c')), x('m'), x('c'))))}}}), agree(v1))
run('s <= b - 1 instead of s < b', product(v1, {...v1, step: {state: {s: ite(atMost(x('s'), minus(x('b'), n(1))), plus(x('s'), min(x('c'), x('m'))), x('s'))}}}), agree(v1))
run('the derived guard s <= b', product(v1, {...v1, step: {state: {s: ite(atMost(x('s'), x('b')), plus(x('s'), min(x('c'), x('m'))), x('s'))}}}), agree(v1))
const a1 = admit()
const caps = [['Dom', 'dom', x('dm')], ['Hour', 'hour', x('hr')], ['Day', 'day', x('d')], ['Acct', 'acct', n(1)]] as const
const granted2 = all(...caps.map(([kk, f, cap]) => atMost(plus(get(kk, x(f)), n(1)), cap)), same(x('ok'), n(1)))
const a2: Machine = {...a1, step: {maps: Object.fromEntries(caps.map(([kk, f]) => [kk, {key: x(f), value: ite(granted2, plus(get(kk, x(f)), n(1)), get(kk, x(f)))}]))}}
run('caps rule, checks reordered, +1 <=', product(admitFlagged(), a2), agree(a1))

console.log('Tenant isolation')
const isolation = (sameProvider: boolean, perAccountOnly: boolean): Machine => {
  const base = perAccountOnly ? {...admit(), step: {maps: {Acct: {key: x('acct'), value: ite(all(same(x('ok'), n(1)), less(get('Acct', x('acct')), n(1))), plus(get('Acct', x('acct')), n(1)), get('Acct', x('acct')))}}}} : admitFlagged()
  const mine = all(same(x('who'), n(0)), same(x('acct'), x('Bacct')), same(x('day'), x('Bday')), same(x('hour'), x('Bhour')), same(x('dom'), x('Bdom')))
  const others = all(same(x('who'), n(1)), not(same(x('acct'), x('Bacct'))),
    ...(sameProvider ? [] : [not(same(x('day'), x('Bday'))), not(same(x('hour'), x('Bhour'))), not(same(x('dom'), x('Bdom')))]))
  return product(base, base, {name: 'isolation', params: ['Bacct', 'Bday', 'Bhour', 'Bdom'], inputs: ['who'], bInputs: {ok: ite(same(x('who'), n(1)), n(0), x('ok'))}, assume: all(bit('who'), any(mine, others))})
}
const atB = (kk: string, key: string): Law => ({name: `a.${kk}[B] = b.${kk}[B]`, holds: same(get(`a_${kk}`, x(key)), get(`b_${kk}`, x(key)))})
const bKeys: Law[] = [atB('Acct', 'Bacct'), atB('Day', 'Bday'), atB('Hour', 'Bhour'), atB('Dom', 'Bdom')]
run('caps rule, others anywhere', isolation(true, false), bKeys)
run('caps rule, others at other providers', isolation(false, false), bKeys)
run('per-account cap only, others anywhere', isolation(true, true), [bKeys[0]!])

// A precondition is about params and holds from the start; a request's assumption holds only at a step. The search
// replays from the start before any request, so a law that needs the assumption at the start is false there.
console.log('Preconditions')
const credit = (how: 'pre' | 'assume'): Machine => ({name: 'credit', params: ['A'], inputs: ['c'], state: {s: x('A')}, step: {state: {s: plus(x('s'), x('c'))}}, [how]: atMost(n(1), x('A'))})
const positiveS: Law = {name: 's >= 1', holds: atMost(n(1), x('s'))}
run('credit, A >= 1 as a precondition', credit('pre'), [positiveS])
const asAssume = run('credit, A >= 1 as a request\'s assumption', credit('assume'), [positiveS])
console.log(`  the search agrees: ${JSON.stringify(search(credit('assume'), positiveS))} breaks it, and with the precondition ${JSON.stringify(search(credit('pre'), positiveS) ?? 'nothing')} does`)
void asAssume

// The kernel rejects what isn't a proof.
console.log('Tampering (each must be rejected)')
const goal = obligations(loss(), [boundedLoss])[1]!
const tree = lossProof.proof!.trees[goal.name]!
const leaves: any[] = []
const walk = (t: any): unknown => ('leaf' in t ? leaves.push(t) : (walk(t.yes), walk(t.no)))
walk(tree)
const mutate = (f: (t: any) => void) => { const copy = structuredClone(tree); f(copy); return check(goal, copy) }
console.log(`  untouched                                    ${check(goal, tree) ? 'accepted' : 'rejected'}`)
console.log(`  a leaf's derivation emptied                  ${mutate(t => { let n0: any = t; while (!('leaf' in n0)) n0 = n0.yes; n0.leaf = [] }) ? 'ACCEPTED' : 'rejected'}`)
console.log(`  a split's atom changed                       ${mutate(t => { if ('split' in t) t.split = {...t.split, 1: (t.split['1'] ?? 0) + 7} }) ? 'ACCEPTED' : 'rejected'}`)
console.log(`  a branch replaced by its sibling              ${mutate(t => { if ('split' in t) t.no = t.yes }) ? 'ACCEPTED' : 'rejected'}`)
const wrongLaw: Law = {name: boundedLoss.name, holds: atMost(x('s'), x('b'))}
console.log(`  the proof of s <= b + m offered for s <= b   ${check(obligations(loss(), [wrongLaw])[1]!, tree) ? 'ACCEPTED' : 'rejected'}`)
