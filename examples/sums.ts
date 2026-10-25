// Sums over a map's keys, and liveness under strong fairness (kernel.ts's sumMachine and livenessParts, Sums.lean and
// Live.lean's sleads_sf_soundA).
//   - A token: `Bal.sum()` is the sum of every balance, exact; the balances sum to the supply, so no balance exceeds it.
//     The kernel knows a sum by its facts: a step moves it by what the step writes, and the term at any key, with the
//     keys a step writes, is at most it. A mint that forgets the supply is refused with a run.
//   - Seats: `Taken.sum()` counts the seats taken (cells 0 or 1); it never passes the capacity. A booking that skips the
//     check is refused.
//   - A flaky job: a worker takes it (fetch), loses it (stall), takes it again, and so on; it fails for good only when
//     failed while active. Under weak fairness nothing proves it ends (the regions don't stay: no rank holds); under
//     strong fairness (`fairness: 'strong'`), where an event that keeps coming back is taken, it ends: fetch hands over to
//     the active region, fail ends it. A variant where a stall may lose the job for good is refused.
// With --lean, each law as a Lean theorem (Sums.lean's sum_holds, Live.lean's sleads_sf_soundA):
//   bun examples/sums.ts
//   bun examples/sums.ts --lean > lean-kernel/SumsExamples.lean
import {forall, nat, oneOf, proveLeadsTo, proveRule, rule, when, yes} from '../core/dsl.ts'
import {type LeanItem, toLean} from '../lean-kernel/emit.ts'

const token = (bug?: 'free mint') => rule('token')
  .params({cap: nat})
  .inputs({op: oneOf('mint', 'transfer', 'burn'), from: nat, to: nat, value: nat})
  .assume(({value, cap}) => value.atMost(cap))
  .state({supply: 0})
  .maps({Bal: 0})
  .flags(({op, from, value, Bal}) => ({
    mints: op.is('mint'),
    transfers: op.is('transfer').and(Bal.at(from).atLeast(value)),
    burns: op.is('burn').and(Bal.at(from).atLeast(value)),
  }))
  .step(({from, to, value, supply, Bal, mints, transfers, burns}) => ({
    // One write at every key: the payer's balance less the value, the payee's plus it (the same account: unchanged).
    Bal: Bal.each(k => Bal.at(k).minus(when(transfers.or(burns).and(k.eq(from)), value, 0)).plus(when(mints.or(transfers).and(k.eq(to)), value, 0))),
    supply: when(mints, bug ? supply : supply.plus(value), when(burns, supply.minus(value), supply)),
  }))
const seats = (bug?: 'no check') => rule('seats')
  .params({capacity: nat})
  .inputs({op: oneOf('book', 'cancel'), seat: nat})
  .maps({Taken: 0})
  .flags(({op, seat, capacity, Taken}) => ({
    books: op.is('book').and(Taken.at(seat).eq(0), bug ? yes : Taken.sum().lt(capacity)),
    cancels: op.is('cancel'),
  }))
  .step(({seat, Taken, books, cancels}) => ({Taken: Taken.set(seat, when(books, 1, when(cancels, 0, Taken.at(seat))))}))
const job = (bug?: 'lost') => rule('flaky job')
  .inputs({op: oneOf('fetch', 'stall', 'fail', 'lose')})
  .state({st: (bug ? oneOf('wait', 'active', 'failed', 'lost') : oneOf('wait', 'active', 'failed')).from('wait')})
  .flags(({op, st}) => ({fetches: op.is('fetch').and(st.is('wait')), stalls: op.is('stall').and(st.is('active')), fails: op.is('fail').and(st.is('active')),
    loses: bug ? op.is('lose').and(st.is('active')) : op.is('lose').and(st.is('active'), st.is('wait'))}))
  .step(({st, fetches, stalls, fails, loses}) => ({st: when(fetches, 'active', when(stalls, 'wait', when(fails, 'failed', bug ? when(loses, 'lost', st) : st)))}))
const ends = (r: ReturnType<typeof job>, fairness?: 'strong') => r.leadsTo('the job fails for good', {
  from: ({st}) => st.is('failed').not(), to: ({st}) => st.is('failed'), rank: () => 0,
  helpful: [{when: ({st}) => st.is('wait'), request: () => ({op: 0})}, {when: ({st}) => st.is('active'), request: () => ({op: 2})}],
  ...(fairness ? {fairness} : {}),
})

const t = token(), s = seats(), j = job()
const supplyLaw = t.law('the balances sum to the supply', ({Bal, supply}) => Bal.sum().eq(supply))
const cellLaw = t.law('no balance exceeds the supply', ({Bal, supply}) => forall(k => Bal.at(k).atMost(supply)))
const seatLaw = s.law('no more seats taken than the capacity', ({Taken, capacity}) => Taken.sum().atMost(capacity))
const seatBit = s.law('a seat is taken or free', ({Taken}) => forall(k => Taken.at(k).atMost(1)))

if (process.argv.includes('--lean')) {
  const items: LeanItem[] = [
    // (the machine with the sums the laws read: a law leaves its rule as it was)
    {id: 'token', machine: t.withSumsOf(supplyLaw, cellLaw).machine, laws: [...t.kindLaws(), supplyLaw, cellLaw]},
    {id: 'seats', machine: s.machine, laws: [...s.kindLaws(), seatBit, seatLaw]},
    {id: 'job', machine: j.machine, laws: j.kindLaws(), liveness: [ends(j, 'strong')]},
  ]
  console.log(toLean(items, {title: 'Sums over a map\'s keys and strong fairness (examples/sums.ts)'}))
  process.exit(0)
}
let failed = false
const report = (ok: boolean, what: string) => { failed ||= !ok; console.log(`${ok ? 'ok  ' : 'FAIL'} ${what}`) }
const shown = (v: ReturnType<typeof proveRule>) => (v.proven ? (v.checked ? 'proven' : 'KERNEL REJECTS') : v.run ? `refused, a run of ${v.run.trace.length} requests` : `not proven (${v.why ?? v.stuck})`)
for (const [r, laws] of [[t, [supplyLaw]], [t, [supplyLaw, cellLaw]], [s, [seatBit, seatLaw]]] as const) {
  const v = proveRule(r as never, laws as never, {search: false})
  report(v.proven && v.checked, `${r.machine.name}: ${laws.map(l => l.name).join('; ')}: ${shown(v)}`)
}
// The law about cells alone: the search finds the sum's law itself.
const alone = proveRule(t, [cellLaw])
report(alone.proven && alone.checked, `token: ${cellLaw.name}, alone: ${shown(alone)}${alone.found?.laws?.length ? ` with ${alone.found.laws.map(f => f.text).join('; ')}` : ''}`)
const tb = token('free mint'), tv = proveRule(tb, [tb.law('the balances sum to the supply', ({Bal, supply}) => Bal.sum().eq(supply))])
report(!tv.proven && !!tv.run, `a mint that forgets the supply: ${shown(tv)}`)
const sb = seats('no check'), sv = proveRule(sb, [sb.law('no more seats taken than the capacity', ({Taken, capacity}) => Taken.sum().atMost(capacity))])
report(!sv.proven && !!sv.run, `a booking that skips the check: ${shown(sv)}`)
const weak = proveLeadsTo(j, j.kindLaws(), ends(j)), strong = proveLeadsTo(j, j.kindLaws(), ends(j, 'strong'))
report(!weak.proven, `flaky job, weak fairness: ${weak.proven ? 'PROVEN' : 'not proven (no rank: the regions do not stay)'}`)
report(strong.proven && strong.checked, `flaky job, strong fairness: ${strong.proven ? 'proven' : `NOT PROVEN (${strong.goal})`}`)
const jb = job('lost'), lost = proveLeadsTo(jb, jb.kindLaws(), ends(jb, 'strong'))
report(!lost.proven, `a stall that may lose the job, strong fairness: ${lost.proven ? 'PROVEN' : 'refused'}`)
if (failed) process.exit(1)
