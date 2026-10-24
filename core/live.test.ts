// The searches past the kernel's goals, on small rules: a liveness whose rank is made of the rule's own terms
// (core/live.ts: a control variable's levels, a distance to a deadline), laws about ids a counter hands out
// (core/fresh.ts), and a one-step law broken only by a run past the random ones (dsl.ts's step-law ghosts for the
// bounded runs). Each proven, and its broken variant refused.
import {expect, test} from 'bun:test'
import {bool, nat, no, oneOf, proveLeadsTo, proveSteps, rule, when, yes} from './dsl.ts'

// A runner: running cycles between connecting, streaming and reconnecting (each a level), STOP drains it to stopped.
const runner = (broken = false) => rule('runner')
  .inputs({ev: oneOf('start', 'ok', 'drop', 'retry', 'stop', 'done')})
  .state({st: oneOf('stopped', 'connecting', 'streaming', 'reconnecting', 'stopping').from('stopped'), tries: 0})
  .step(({ev, st, tries}) => {
    const running = st.is('connecting').or(st.is('streaming'), st.is('reconnecting'))
    return {
      st: when(ev.is('start').and(st.is('stopped')), 'connecting', when(ev.is('ok').and(st.is('connecting')), 'streaming',
        when(ev.is('drop').and(st.is('streaming')), 'reconnecting', when(ev.is('retry').and(st.is('reconnecting')), 'connecting',
          when(ev.is('stop').and(running), 'stopping', when(ev.is('done').and(st.is('stopping')), broken ? 'connecting' : 'stopped', st)))))),
      // (a counter the runs raise, which no rank should read)
      tries: when(ev.is('retry'), tries.plus(1), tries),
    }
  })
const stops = (r: ReturnType<typeof runner>) => r.leadsTo('a started runner comes back to stopped', {
  from: ({st}) => st.is('stopped').not(),
  to: ({st}) => st.is('stopped'),
  helpful: [{when: ({st}) => st.is('stopping').not(), request: () => ({ev: 4})}, {when: ({st}) => st.is('stopping'), request: () => ({ev: 5})}],
})

test('a rank of a control variable\'s levels: proven, and the variant that restarts refused', () => {
  const r = runner(), v = proveLeadsTo(r, [], stops(r), {ms: 20_000})
  expect(v).toMatchObject({proven: true, checked: true})
  expect(v.found?.rank).toMatch(/if st = /)
  const bad = runner(true)
  expect(proveLeadsTo(bad, [], stops(bad), {ms: 5_000}).proven).toBe(false)
}, 60_000)

// A timelock: an operation is ready once the time reaches its timestamp; time goes on by a tick.
const timelock = (broken = false) => rule('timelock')
  .params({d: nat})
  .inputs({op: oneOf('schedule', 'tick'), id: nat, delay: nat})
  .state({now: 0})
  .maps({Ts: 0})
  .step(({op, id, delay, now, Ts}) => ({
    now: when(op.is('tick'), broken ? now : now.plus(1), now),
    Ts: Ts.set(id, when(op.is('schedule').and(Ts.at(id).eq(0)), now.plus(delay).plus(1), Ts.at(id))),
  }))
const ready = (r: ReturnType<typeof timelock>) => r.leadsTo('every scheduled operation becomes ready', {
  from: ({now, Ts, d}) => now.lt(Ts.at(d)),
  to: ({now, Ts, d}) => Ts.at(d).atMost(now),
  helpful: () => ({op: 1}),
})

test('a rank of a distance the rule compares (a deadline read from a map): proven, and the clock that stops refused', () => {
  const r = timelock(), v = proveLeadsTo(r, [], ready(r), {ms: 20_000})
  expect(v).toMatchObject({proven: true, checked: true})
  expect(v.found?.rank).toMatch(/Ts\(d\)/)
  const bad = timelock(true)
  expect(proveLeadsTo(bad, [], ready(bad), {ms: 5_000}).proven).toBe(false)
}, 60_000)

// Sessions numbered by a counter: deleting a live session marks it ended, and it is never live again.
const sessions = (broken = false) => rule('sessions')
  .inputs({op: oneOf('create', 'delete', 'touch'), sid: nat})
  .state({next: 0})
  .maps({Live: bool.from(false), Ended: bool.from(false)})
  .step(({op, sid, next, Live, Ended}) => {
    // (the broken variant hands out a fresh id below the counter: an old one)
    const id = broken ? next.minus(1) : next
    return {
      next: when(op.is('create'), next.plus(1), next),
      Live: Live.each(k => when(op.is('create').and(k.eq(id)), yes, when(op.is('delete').and(k.eq(sid)), no, Live.at(k)))),
      Ended: Ended.each(k => when(op.is('delete').and(k.eq(sid), Live.at(sid)), yes, Ended.at(k))),
    }
  })
const neverBack = (r: ReturnType<typeof sessions>) => r.stepLaw('a deleted session never comes back', ({sid}, after) => after.Live.at(sid).not(), ({Ended, sid}) => Ended.at(sid))

test('laws about the ids a counter hands out: proven with them, and the variant that reuses an id refused', () => {
  const r = sessions(), v = proveSteps(r, [], [neverBack(r)], {search: {ms: 10_000}})
  expect(v).toMatchObject({proven: true, checked: true})
  expect(v.found?.laws?.map(f => f.text).join('; ')).toMatch(/next <= k → Live\[k\] = 0/)
  const bad = sessions(true)
  expect(proveSteps(bad, [], [neverBack(bad)], {search: {ms: 5_000}}).proven).toBe(false)
}, 60_000)

// A lock that opens only after `code` turns in a row of exactly the right digit (the random runs' draws of 0..8 hit it
// at 1 in 9 a turn): a step law broken at the end, found by the bounded runs over the step law's ghost.
const lock = (code: number) => rule('lock')
  .inputs({digit: nat})
  .state({right: 0, open: bool.from(false)})
  .step(({digit, right, open}) => ({right: when(digit.eq(7), right.plus(1), 0), open: open.or(right.atLeast(code))}))
const staysShut = (r: ReturnType<typeof lock>) => r.stepLaw('the lock never opens', (_, after) => after.open.not())

test('a one-step law broken only far from the start: refused by a bounded run, with the run', () => {
  const r = lock(5), v = proveSteps(r, [], [staysShut(r)], {search: {ms: 10_000}})
  expect(v.proven).toBe(false)
  expect(v.run?.trace.length).toBeGreaterThanOrEqual(6)
}, 60_000)
