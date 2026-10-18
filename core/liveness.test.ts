// Liveness under fairness (kernel.ts livenessParts, dsl.ts leadsTo): the ticket queue of examples/liveness.ts proven and
// its broken variant refused; on random runs that send `work` at least every third request, each ticket issued is
// served within a bound; and the broken variant has a run that sends only `work` and never serves the first ticket.
// Batches (two helpful requests, a rank of two in order), a history with a query, and a machine with sets too.
import {expect, test} from 'bun:test'
import {evalC, interpret} from './machine.ts'
import {proveLiveness} from '../kernel/prove.ts'
import {allDone, batchLaws, batches, everyLoggedTicket, everyRecountedTicket, everyReview, everyTicket, loggedLaws, loggedTickets, recounted, recountedLaws, reviewLaws, reviews, ticketLaws, tickets} from '../examples/liveness.ts'
import {count, nat, rule} from './dsl.ts'
import {allowed} from './watch.ts'

test('every ticket is served: proven; the stalling variant refused', () => {
  expect(proveLiveness(tickets().machine, ticketLaws(), everyTicket())).toMatchObject({proven: true, checked: true})
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
