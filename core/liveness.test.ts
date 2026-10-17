// Liveness under fairness (kernel.ts livenessParts, dsl.ts leadsTo): the ticket queue of examples/liveness.ts proven and
// its broken variant refused; on random runs that send `work` at least every third request, each ticket issued is
// served within a bound; and the broken variant has a run that sends only `work` and never serves the first ticket.
import {expect, test} from 'bun:test'
import {evalC, interpret} from './machine.ts'
import {proveLiveness} from '../kernel/prove.ts'
import {everyTicket, ticketLaws, tickets} from '../examples/liveness.ts'
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
