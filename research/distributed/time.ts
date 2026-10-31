// Clocks, leases and liveness over keys on core/system.ts (research/distributed/DESIGN.md, section 6):
//   a lease in a store (SET NX PX): "a process uses the lease only while the store holds it for that process, unexpired",
//     under clock skew ≤ E and a margin M ≥ 2E: proven, its invariants found (nothing written; the search's budget 40 s,
//     --lease-ms); with the skew bound dropped, or a margin of E: refuted, the run replayed;
//   a transactional outbox: "every outbox row is eventually published", "... eventually handled by the consumer" (at
//     least once, under weak fairness of each row's relay and delivery), and "... eventually marked published", refuted
//     under weak fairness by a fair run that never gets there, found (the relay crashing between publish and mark: a
//     cycle of two steps), proven under strong fairness.
//   bun research/distributed/time.ts [--ms 20000] [--lease-ms 40000] [--only lease|outbox]
import {type KeyedLiveness, forall, nat, proveLeadsTo, proveSteps, refuteLeadsTo, rule, when} from '../../core/dsl.ts'
import {type Model, assuming, client, clocked, delivery, expires, modelsOf, system, time} from '../../core/system.ts'

const arg = (n: string) => { const i = process.argv.indexOf(`--${n}`); return i < 0 ? undefined : process.argv[i + 1] }
const ms = Number(arg('ms') ?? 20_000), leaseMs = Number(arg('lease-ms') ?? 40_000), only = arg('only')
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Env = any
const show = (v: {proven: boolean, checked: boolean, run?: unknown}) => (v.proven && v.checked ? 'proven' : v.run ? 'refuted' : 'unknown')
const timed = <T>(f: () => T): [T, number] => { const t0 = performance.now(), out = f(); return [out, Math.round(performance.now() - t0)] }

// --- a lease -------------------------------------------------------------------------------------------------------
// A process p acquires the lease as Redis's SET key p NX PX L does: where the key is absent, it holds p until the store's
// time plus L (`at`, the store's clock the time reference); p reads its own clock (t) when it asks and counts the lease
// valid until t + L − M, its margin M. It uses the lease (a write the lease protects, at the instant it checks) only
// while its clock reads before that. The key expires at its time (expires: never before it, no eviction).
export const lease = (skew: 'bounded' | 'unbounded', margin: 'twice the skew' | 'the skew') => {
  const acquire = rule('acquire').params({L: nat, M: nat, E: nat}).inputs({t: nat, p: nat}).state({taken: 0, owner: 0, at: 0, now: 0, until: 0})
    .pre(({L, M, E}) => (margin === 'twice the skew' ? M.atLeast(E.times(2)) : M.atLeast(E)).and(L.atLeast(M)))
    .step(({L, M, t, p, taken, owner, at, now, until}) => {
      const ok = taken.eq(0)
      return {taken: when(ok, 1, taken), owner: when(ok, p, owner), at: when(ok, now.plus(L), at), until: when(ok, t.plus(L).minus(M), until)}
    })
  const use = rule('use').inputs({t: nat, p: nat}).state({until: 0}).assume(({t, until}) => t.lt(until)).step(() => ({}))
  const c = (m: typeof acquire.machine) => clocked(m, 't', skew === 'bounded' ? 'E' : Infinity), shared = ['taken', 'owner', 'at']
  return system(`lease (skew ${skew}, margin ${margin})`, {
    time: time(), expire: expires({taken: 0, owner: 0}, 'at'),
    acquire: {rule: c(acquire.machine), id: 'p', shared}, use: {rule: c(use.machine), id: 'p', shared},
  })
}
// An invariant the proof needs, written (the search finds another, as three laws at every key: a lease written and not
// the owner's is past by any reading of its clock, until + E <= now; so is every lease written while the key is free;
// while it is taken, every lease written ends by its expiry, until + E <= at): every process holds no lease (until 0),
// or its lease is past by any reading its clock may give (its until + E is not after the time), or it is the store's
// owner and its until + E not after the expiry.
export const leaseInvariant = (r: ReturnType<typeof lease>) => r.law('a lease a process may still count valid is the store\'s, for that process',
  ({until, now, E, taken, owner, at}: Env) => forall(q => until.at(q).eq(0).or(until.at(q).plus(E).atMost(now)).or(taken.eq(1).and(owner.eq(q)).and(until.at(q).plus(E).atMost(at)))))
export const leaseLaw = (r: ReturnType<typeof lease>) => r.stepLaw('a process uses the lease only while the store holds it for that process, unexpired',
  (b: Env) => b.taken.eq(1).and(b.owner.eq(b.p)).and(b.now.lt(b.at)), (b: Env) => b.act.is('use'))

// --- an outbox -----------------------------------------------------------------------------------------------------
// The app's transaction inserts an outbox row (client: a row at a fresh id); a relay polls pending rows at least once and
// publishes each to the broker's queue Q, then marks it published; it may crash between the two (its in-flight mark
// lost), and polls the row again; the consumer takes each message of Q at least once.
export const CRASH: Model = {name: 'the relay crashes', assumes: 'the relay may stop between publishing a row and marking it published, and then polls the row again (its publish repeated)',
  checked: 'the outbox pattern\'s own failure: the publish and the mark are two transactions (a broker and a database)'}
export const outbox = () => {
  const publish = rule('publish').inputs({row: nat}).maps({Q: 0, InFlight: 0}).step(({row, Q, InFlight}) => ({Q: Q.set(row, 1), InFlight: InFlight.set(row, 1)}))
  const mark = rule('mark').inputs({msg: nat}).maps({Outbox: 0, InFlight: 0}).assume(({msg, InFlight}) => InFlight.at(msg).eq(1)).step(({msg, Outbox}) => ({Outbox: Outbox.set(msg, 2)}))
  const crash = rule('crash').inputs({msg: nat}).maps({InFlight: 0}).step(({msg, InFlight}) => ({InFlight: InFlight.set(msg, 0)}))
  const handle = rule('handle').inputs({id: nat}).maps({Done: 0}).step(({id, Done}) => ({Done: Done.set(id, 1)}))
  return system('outbox', {
    app: client('Outbox', []), relay: delivery(publish.machine, 'Outbox', [], 'at-least-once', {id: 'row'}), mark: mark.machine,
    crash: assuming(crash.machine, CRASH), consume: delivery(handle.machine, 'Q', [], 'at-least-once', {id: 'id'}),
  })
}
const ACT = {app: 0, relay: 1, mark: 2, crash: 3, consume: 4}
export const published = (r: ReturnType<typeof outbox>): KeyedLiveness => r.leadsTo('every outbox row is eventually published', {
  from: ({Outbox}: Env, k) => Outbox.at(k).eq(1), to: ({Q}: Env, k) => Q.at(k).eq(1), helpful: (_: Env, k) => ({act: ACT.relay, msg: k})})
export const handled = (r: ReturnType<typeof outbox>): KeyedLiveness => r.leadsTo('every outbox row is eventually handled by the consumer', {
  from: ({Outbox}: Env, k) => Outbox.at(k).atLeast(1), to: ({Done}: Env, k) => Done.at(k).eq(1),
  helpful: [{when: ({Outbox, Q}: Env, k) => Outbox.at(k).eq(1).and(Q.at(k).eq(0)), request: (_: Env, k) => ({act: ACT.relay, msg: k})}, {when: ({Q}: Env, k) => Q.at(k).eq(1), request: (_: Env, k) => ({act: ACT.consume, msg: k})}]})
export const marked = (r: ReturnType<typeof outbox>, fairness: 'weak' | 'strong'): KeyedLiveness => r.leadsTo('every outbox row is eventually marked published', {
  from: ({Outbox}: Env, k) => Outbox.at(k).eq(1), to: ({Outbox}: Env, k) => Outbox.at(k).eq(2), fairness,
  helpful: [{when: ({InFlight}: Env, k) => InFlight.at(k).eq(0), request: (_: Env, k) => ({act: ACT.relay, msg: k})}, {when: ({InFlight}: Env, k) => InFlight.at(k).eq(1), request: (_: Env, k) => ({act: ACT.mark, msg: k})}]})

if (import.meta.main) {
  if (only !== 'outbox') for (const [skew, margin] of [['bounded', 'twice the skew'], ['unbounded', 'twice the skew'], ['bounded', 'the skew']] as const) {
    const r = lease(skew, margin), law = leaseLaw(r)
    const [v, t] = timed(() => proveSteps(r, [], [law], {search: {ms: leaseMs}}))
    console.log(`lease | skew ${skew}, margin ${margin} | assumes ${modelsOf(r).map(m => m.name).join(', ')} | ${show(v)} | ${t} ms${v.found?.laws?.length ? ` | found: ${v.found.laws.map(f => f.text).join('; ')}` : ''}`)
    if (v.run) for (const s of v.run.trace) console.log(`    ${JSON.stringify(s)}`)
    if (!(v.proven && v.checked) && !v.run) {
      console.log(`    ${v.goal ?? ''} ${v.stuck ?? ''} ${v.why ?? ''}`)
      const [w, tw] = timed(() => proveSteps(r, [leaseInvariant(r)], [law], {search: false}))
      console.log(`    with the invariant written ("${leaseInvariant(r).name}"): ${show(w)} | ${tw} ms`)
    }
  }
  if (only !== 'lease') {
    const r = outbox()
    for (const l of [published(r), handled(r), marked(r, 'weak'), marked(r, 'strong')]) {
      const [v, t] = timed(() => proveLeadsTo(r, [], l, {ms}))
      console.log(`outbox | ${l.name} (${l.fairness ?? 'weak'} fairness) | assumes ${modelsOf(r).map(m => m.name).join(', ')} | ${show(v)} | ${t} ms${v.found?.rank ? ` | rank ${v.found.rank}` : ''}${v.found?.laws?.length ? ` | laws: ${v.found.laws.map(f => f.text).join('; ')}` : ''}`)
      if (!(v.proven && v.checked)) {
        console.log(`    ${v.goal ?? ''} ${v.stuck ?? ''} ${v.why ?? ''}`)
        const [f, ft] = timed(() => refuteLeadsTo(r, [], l, {ms}))
        console.log(`    a fair run that never gets there, found: ${f ? (f.verdict.refuted ? `refuted, the run fair: ${f.verdict.fair!.join(', ')}` : `not shown (${f.verdict.why})`) : 'none found'} | ${ft} ms`)
        if (f) console.log(`      stem ${JSON.stringify(f.ring.stem)} at ${JSON.stringify(f.ring.params)}; ring: ${f.ring.sets.map(x => `${JSON.stringify(x.request)} from ${JSON.stringify(x.holds)}`).join(' ; ')}`)
      }
    }
  }
}
