// Liveness under fairness (kernel.ts livenessParts, dsl.ts leadsTo): the ticket queue of examples/liveness.ts proven and
// its broken variant refused; on random runs that send `work` at least every third request, each ticket issued is
// served within a bound; and the broken variant has a run that sends only `work` and never serves the first ticket.
// Batches (two helpful requests, a rank of two in order), a history with a query, and a machine with sets too. A
// liveness about every key (a fresh param), its rank found, and its stalling variant refuted by a fair ring.
import {expect, test} from 'bun:test'
import {evalC, evalE, interpret} from './machine.ts'
import {proveLiveness} from '../kernel/prove.ts'
import {allDone, batchLaws, batches, everyLoggedTicket, everyRecountedTicket, everyReview, everyTicket, loggedLaws, loggedTickets, recounted, recountedLaws, reviewLaws, reviews, ticketLaws, tickets} from '../examples/liveness.ts'
import {count, keyed, nat, oneOf, proveLeadsTo, refuteLeadsTo, rule, when} from './dsl.ts'
import {allowed} from './watch.ts'

test('every ticket is served: proven; the stalling variant refused', () => {
  const v = proveLiveness(tickets().machine, ticketLaws(), everyTicket())
  expect(v).toMatchObject({proven: true, checked: true})
  // (by default its certificate is its parts' cyclic proofs, none on the usual rule; with GDP_CERT=usual, none is made)
  expect(v.uncovered ?? []).toEqual([])
  const bad = tickets('stalls with two waiting')
  expect(proveLiveness(bad.machine, ticketLaws(bad), everyTicket(bad)).proven).toBe(false)
})

test('fair runs serve every ticket; the stalling variant has a fair run that never does', () => {
  let seed = 21
  const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
  const r = tickets(), m = r.machine, run = interpret(m), l = everyTicket(r)
  let checked = 0
  for (let trial = 0; trial < 300; trial++) {
    const params = {cap: 1 + rand(4), t: rand(5)}
    let st = run.init(params), since: number | undefined
    for (let i = 0; i < 60; i++) {
      const env = {...params}
      if (since === undefined && evalC(l.from, env, st, m)) since = i
      if (since !== undefined && evalC(l.to, env, st, m)) { checked++; since = undefined; break }
      // `work` at least every third request; the bound: the rank (at most cap + 1) times three steps.
      if (since !== undefined) expect(i - since).toBeLessThanOrEqual(3 * (params.cap + 2))
      const input = r.encodeInput({op: i % 3 === 2 || rand(2) ? 'work' : 'take'})
      if (allowed(m, run, params, st, input)) st = run.step(params, st, input)
    }
  }
  expect(checked).toBeGreaterThan(100)
  const bad = tickets('stalls with two waiting'), bm = bad.machine, brun = interpret(bm), params = {cap: 5, t: 0}
  let st = brun.init(params)
  for (const op of ['take', 'take'] as const) st = brun.step(params, st, bad.encodeInput({op}))
  for (let i = 0; i < 50; i++) st = brun.step(params, st, bad.encodeInput({op: 'work'}))
  expect(evalC(everyTicket(bad).from, params, st, bm) && !evalC(everyTicket(bad).to, params, st, bm)).toBe(true)
})

test('a history: liveness through its plain machine (sums as state, queries free); a request naming a query refused', () => {
  expect(proveLiveness(loggedTickets().machine, loggedLaws(), everyLoggedTicket())).toMatchObject({proven: true, checked: true})
  const bad = loggedTickets('stalls with two waiting')
  expect(proveLiveness(bad.machine, loggedLaws(bad), everyLoggedTicket(bad)).proven).toBe(false)
  expect(proveLiveness(recounted().machine, recountedLaws(), everyRecountedTicket())).toMatchObject({proven: true, checked: true})
  const backwards = recounted('reads the recount backwards')
  expect(proveLiveness(backwards.machine, recountedLaws(backwards), everyRecountedTicket(backwards)).proven).toBe(false)
  const q = rule('queried').inputs({t: nat}).state({n: 0}).log('t').queries({seen: r => count(r.t.atLeast(0))}).step(({n}) => ({n}))
  const live = q.leadsTo('never', {from: ({n}) => n.eq(0), to: ({n}) => n.eq(0), rank: () => 0, helpful: ({n}) => ({seen: n})})
  expect(() => proveLiveness(q.machine, [], live)).toThrow(/query/)
})

test('batches: two helpful requests, each in its region, a rank of two in order; one request alone, or one natural, refused', () => {
  expect(proveLiveness(batches().machine, batchLaws(), allDone())).toMatchObject({proven: true, checked: true})
  const bad = batches('stalls on the last item')
  expect(proveLiveness(bad.machine, batchLaws(bad), allDone(bad)).proven).toBe(false)
  const r = batches(), l = allDone(r)
  // `work` alone helps nowhere once the items run out; the items alone can rise on a load.
  expect(proveLiveness(r.machine, batchLaws(r), {...l, helpful: [l.helpful![0]!]}).proven).toBe(false)
  expect(proveLiveness(r.machine, batchLaws(r), {...l, rank: (l.rank as unknown[])[1] as never}).proven).toBe(false)
  // Runs that send both, each at least every third request, get everything done.
  let seed = 5
  const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
  const m = r.machine, run = interpret(m)
  for (let trial = 0; trial < 50; trial++) {
    const params = {size: rand(4)}
    let st = run.init(params), done = false
    for (let i = 0; i < 200 && !done; i++) {
      const op = i % 3 === 0 ? 'load' : i % 3 === 1 ? 'work' : rand(2) ? 'load' : 'work'
      st = run.step(params, st, r.encodeInput({op}))
      done = evalC(l.to, params, st, m)
    }
    expect(done).toBe(true)
  }
})

test('a machine with sets: the helpful request leaves the set it carries free', () => {
  expect(proveLiveness(reviews().machine, reviewLaws(), everyReview())).toMatchObject({proven: true, checked: true})
  const bad = reviews('approves only what the set names')
  expect(proveLiveness(bad.machine, reviewLaws(bad), everyReview(bad)).proven).toBe(false)
})

test('a request that moves the region without lowering the rank: refused (each helpful request can always arrive in the wrong region)', () => {
  // toggle flips the phase; act0 works only in phase 0, act1 only in phase 1. The run toggle, act0, toggle, act1, ...
  // sends both infinitely often and never works, so "the work gets done" is false.
  const r = rule('two phases').inputs({op: nat}).state({phase: 0, work: 3})
    .assume(({op}) => op.atMost(2))
    .step(({op, phase, work}) => ({phase: when(op.eq(0), when(phase.eq(0), 1, 0), phase),
      work: when(op.eq(1).and(phase.eq(0)).or(op.eq(2).and(phase.eq(1))), work.minus(1), work)}))
  const live = r.leadsTo('the work gets done', {from: ({work}) => work.atLeast(0), to: ({work}) => work.eq(0), rank: ({work}) => work,
    helpful: [{when: ({phase}) => phase.eq(0), request: () => ({op: 1})}, {when: ({phase}) => phase.eq(1), request: () => ({op: 2})}]})
  // The phase is 0 or 1, so some region always holds: only the toggle keeping the rank while it moves the region fails.
  const laws = [r.law('the phase is 0 or 1', ({phase}) => phase.atMost(1))]
  const v = proveLiveness(r.machine, laws, live)
  expect(v.proven).toBe(false)
  expect(v.failed?.goal).toContain('the rank kept only with its region')
  const m = r.machine, run = interpret(m)
  let st = run.init({})
  for (let i = 0; i < 40; i++) st = run.step({}, st, {op: [0, 1, 0, 2][i % 4]!})
  expect(st.scalars.work).toBe(3)
})

test('weak fairness: each example\'s helpful requests proven allowed in their region (free inputs, a query by witness, empty sets)', async () => {
  const {toLean} = await import('../lean-kernel/emit.ts')
  const ex = await import('../examples/liveness.ts')
  const items = [
    {id: 'tickets', machine: tickets().machine, laws: ticketLaws(), liveness: [everyTicket()]},
    {id: 'tagged', machine: ex.taggedTickets().machine, laws: ex.taggedLaws, liveness: [ex.everyTaggedTicket]},
    {id: 'batches', machine: batches().machine, laws: batchLaws(), liveness: [allDone()]},
    {id: 'recounted', machine: recounted().machine, laws: recountedLaws(), liveness: [everyRecountedTicket()]},
    {id: 'reviews', machine: reviews().machine, laws: reviewLaws(), liveness: [everyReview()]},
  ]
  for (const item of items) expect(toLean([item])).toMatch(/_live0_holds_wf \(run/)
  // A helpful request the machine never allows: the claim under weak fairness isn't made.
  const never = rule('never served').params({t: nat}).inputs({op: nat}).state({next: 1, served: 0})
    .assume(({op}) => op.eq(0))
    .step(({op, next, served}) => ({next, served: when(op.eq(1), served.plus(1), served)}))
  const live = never.leadsTo('served', {from: ({served}) => served.eq(0), to: ({served}) => served.gt(0), rank: ({served}) => served.plus(1).minus(served), helpful: () => ({op: 1})})
  const out = toLean([{id: 'never', machine: never.machine, laws: [never.law('served at most 1', ({served}) => served.atMost(1))], liveness: [live]}])
  expect(out).toMatch(/never_live0_holds \(run/)
  expect(out).not.toMatch(/holds_wf/)
})

// Orders by id: placing one sets it to 1, settling a placed one to 2 (the stalling variant leaves it at 1).
const orders = (stalls = false) => rule('orders').inputs({op: oneOf('place', 'settle'), id: nat}).maps({S: 0})
  .assume(({op, id, S}) => op.is('place').implies(S.at(id).eq(0)))
  .step(({op, id, S}) => ({S: S.set(id, when(op.is('place'), 1, when(S.at(id).eq(1), stalls ? 1 : 2, S.at(id))))}))
const settled = (r: ReturnType<typeof orders>) => r.leadsTo('every order placed is settled', {from: ({S}, k) => S.at(k).eq(1), to: ({S}, k) => S.at(k).eq(2), helpful: (_, k) => ({op: 1, id: k})})

test('a liveness about every key: its key a fresh param no step reads, refused without it; the stalling variant refuted by a fair ring', () => {
  const r = orders(), l = settled(r)
  expect(l.forall).toMatch(/^key\$/)
  expect(keyed(r, l).machine.params).toEqual([l.forall!])
  expect(() => proveLiveness(r.machine, [], l)).toThrow()
  expect(proveLeadsTo(r, [], l, {ms: 10_000})).toMatchObject({proven: true, checked: true})
  // not refuted where it holds: no ring
  expect(refuteLeadsTo(r, [], l, {ms: 3000})?.verdict.refuted ?? false).toBe(false)
  const bad = orders(true), lb = settled(bad)
  expect(proveLeadsTo(bad, [], lb, {ms: 5000}).proven).toBe(false)
  const f = refuteLeadsTo(bad, [], lb, {ms: 10_000})
  expect(f?.verdict).toEqual({refuted: true, fair: ['taken', 'weak', 'strong']})
  // the stem and one lap on the interpreter: the order stays placed
  const m = keyed(bad, lb).machine, run = interpret(m), ps = f!.ring.params
  let st = run.init(ps)
  for (const q of f!.ring.stem) st = run.step(ps, st, q)
  for (let lap = 0; lap < 5; lap++) for (const set of f!.ring.sets) {
    const q = Object.fromEntries(m.inputs.map(i => [i, set.request[i] ? evalE(set.request[i]!, {...ps, ...st.scalars}, st, m) : 0]))
    expect(allowed(m, run, ps, st, q)).toBe(true)
    st = run.step(ps, st, q)
    expect([evalC(lb.from, ps, st, m), evalC(lb.to, ps, st, m)]).toEqual([true, false])
  }
})
