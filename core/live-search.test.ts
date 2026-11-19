import {expect, test} from 'bun:test'
import {bool, count, max, nat, oneOf, proveLeadsTo, refuteLeadsTo, rule, when} from './dsl.ts'
import {helpfulWriteSupports, leadsByWriteSupports} from './live-support.ts'
import {refutedBy} from './live.ts'
import {livenessHelpful} from '../kernel/kernel.ts'

const historyValve = (closes: boolean) => rule('history valve').inputs({action: oneOf('sample', 'noop')})
  .state({open: bool.from(true)}).log('action')
  .queries({seen: r => count(r.action.is('sample'))})
  .flags(({action, seen}) => ({close: action.is('sample').and(seen.gt(0))}))
  .step(({open, close}) => ({open: closes ? open.and(close.not()) : open}))
const valveEventuallyCloses = (r: ReturnType<typeof historyValve>) => r.leadsTo('a sampled valve closes', {
  from: ({open}) => open, to: ({open}) => open.not(), helpful: () => ({action: 0}),
})

test('a growing history is not a lasso merely because its query can be pinned to zero', () => {
  for (const closes of [true, false]) {
    const r = historyValve(closes), l = valveEventuallyCloses(r)
    const request = livenessHelpful(l)[0]!.request
    const ring = {params: {}, stem: [], sets: [{holds: l.from, request}]}
    const result = refutedBy(r.machine, r.kindLaws(), l, ring)
    expect(result.refuted).toBe(!closes)
    if (closes) expect(result.why).toContain('without pinning history queries')
    else expect(refuteLeadsTo(r, [], l, {ms: 5000})?.verdict.refuted).toBe(true)
  }
}, 20_000)

test('the recurrence checks the new log sum, and a query is never a helpful client field', () => {
  const r = rule('event log').inputs({op: nat}).state({stamp: 0}).log('op')
    .sums({size: () => 1}).queries({readSize: () => 1}).step(({stamp}) => ({stamp}))
  const live = r.leadsTo('the first recorded event is eventually seen', {
    from: ({size}) => size.eq(0), to: ({size}) => size.gt(0), helpful: () => ({op: 0}),
  })
  const request = livenessHelpful(live)[0]!.request
  const ring = {params: {}, stem: [], sets: [{holds: live.from, request}]}
  expect(refutedBy(r.machine, r.kindLaws(), live, ring)).toMatchObject({refuted: false, why: expect.stringContaining('into the next set')})
  const invalid = {...live, request: {readSize: {op: 'const' as const, value: 0}}}
  expect(refutedBy(r.machine, r.kindLaws(), invalid, ring)).toMatchObject({refuted: false, why: expect.stringContaining('names inputs a client sends')})
})

test('a frontier-derived clock bound is checked, not assumed', () => {
  const gate = (broken: boolean, disabled = false) => rule('numbered permits').inputs({at: nat, n: nat, spare: bool}).params({width: nat})
    .pre(({width}) => width.gt(0)).state({frontier: 0, closedUntil: 0, open: bool.from(false)}).maps({Allocated: 0})
    .assume(({at}) => disabled ? at.eq(0) : at.atLeast(0))
    .step(({at, n, width, frontier, closedUntil, Allocated}) => ({
      frontier: max(frontier, n),
      closedUntil: when(at.atMost(closedUntil), n.plus(broken ? 3 : 1).mul(width), closedUntil),
      open: at.gt(closedUntil).and(Allocated.at(n).eq(0)),
      Allocated: Allocated.set(n, when(at.eq(0), 1, Allocated.at(n))),
    }))
  const live = (r: ReturnType<typeof gate>) => r.leadsTo('eventually gets a permit', {from: ({open}) => open.not(), to: ({open}) => open,
    helpful: ({frontier, width}) => ({at: frontier.plus(2).mul(width), n: frontier.plus(2)})})
  for (const broken of [false, true]) {
    const r = gate(broken), l = live(r)
    expect(helpfulWriteSupports(r.machine, l).length).toBe(1)
    const out = proveLeadsTo(r, [], l, {ms: 10_000})
    expect(out.proven && out.checked).toBe(!broken)
  }
  const disabled = gate(false, true)
  expect(leadsByWriteSupports(disabled.machine, disabled.kindLaws(), live(disabled), 5000)).toBeUndefined()
}, 30_000)

test('a guarded natural distance and helpful handoffs terminate under strong, not weak, fairness', () => {
  const r = rule('batch drain')
    .params({limit: nat}).inputs({op: oneOf('offer', 'process', 'interrupt')})
    .state({phase: oneOf('idle', 'busy', 'done').from('idle'), used: 0})
    .flags(({op,phase}) => ({offers: op.is('offer').and(phase.is('idle')), processes: op.is('process').and(phase.is('busy')),
      interrupts: op.is('interrupt').and(phase.is('busy'))}))
    .step(({phase, used, limit, offers, processes, interrupts}) => ({
      phase: when(offers, phase.of('busy'), when(processes, when(used.lt(limit), phase.of('idle'), phase.of('done')), when(interrupts, phase.of('idle'), phase))),
      used: when(processes, used.plus(1), used),
    }))
  const live = (fairness: 'strong' | 'weak') => r.leadsTo('draining stops', {from: ({phase}) => phase.is('done').not(), to: ({phase}) => phase.is('done'),
    helpful: [{when: ({phase}) => phase.is('idle'), request: () => ({op: 0})},
      {when: ({phase}) => phase.is('busy'), request: () => ({op: 1})}], fairness})
  expect(proveLeadsTo(r, [], live('strong'), {ms: 20_000})).toMatchObject({proven: true, checked: true})
  expect(proveLeadsTo(r, [], live('weak'), {ms: 3000}).proven).toBe(false)
}, 30_000)
