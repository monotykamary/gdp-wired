// Functions defined by a recurrence, with lemmas proven by induction: for the suite (`bun examples/lemmas.ts`),
// core/lemmas.test.ts and lean-kernel/package-check.ts.
//   - delay: exponential backoff, 1, 2, 4, ... up to 64; its lemmas say it is at least 1 and at most 64, which a retry
//     schedule needs (the next try is at most 64 after the last request; a failure waits at least a tick) and which its
//     two equations alone don't give: the broken variant states no lemma and is refused
//   - twos: two by two for five steps; "at most 10" is proven only beside "at most 2x", as a law leans on another
//   - filled: a bucket filled one a step up to its capacity, a function of two arguments (the steps, the capacity);
//     a meter that reads it at its own capacity stays within it
//   - leftovers: what is left over each day, the day's remainder mod 7 added up: a recurrence that reads another
//     function (modBy), its lemma leaning on that function's fact
//   - delay, again: it never shrinks, a law between two attempts (for every x <= y), proven with its lemmas; an
//     escalation that only moves up keeps its delay at least where it started, and a ladder's delay at its last rung
//     is at most the delay at its current one (the law between read at two values of the state at once)
//   - a tank filled at a capacity the request may raise: the level stays within the capacity (a function of two
//     arguments read at keys over the state and the request)
//   - a pump allowed to pump only while the bucket is within its capacity reaches its goal, under weak fairness too: its
//     helpful request is allowed by the bucket's lemma, a fact about two keys
import {type Law} from '../core/machine.ts'
import {type Liveness, type StepLaw, min, modBy, nat, oneOf, proveLeadsTo, proveSteps, recur, rule, when} from '../core/dsl.ts'

export const backoff = (bug?: 'states no lemma') => recur('delay', {zero: 1, next: (_, d) => min(d.times(2), 64)}, bug ? {} : {
  'at least 1': (_, d) => d.atLeast(1),
  'at most 64': (_, d) => d.atMost(64),
})
export const retries = (bug?: 'states no lemma') => rule('retry with backoff')
  .inputs({op: oneOf('fail', 'ok'), now: nat})
  .state({tries: 0, next: 0, last: 0})
  .fns({delay: backoff(bug)})
  .assume(({now, last}) => now.atLeast(last))
  .flags(({op, now, next}) => ({retry: op.is('fail').and(now.atLeast(next)), done: op.is('ok').and(now.atLeast(next))}))
  .step(({now, tries, next, retry, done, delay}) => ({
    tries: when(retry, tries.plus(1), when(done, 0, tries)),
    next: when(retry, now.plus(delay(tries)), next),
    last: now,
  }))
export const retryLaws = (r = retries()): Law[] => [r.law('the next try is at most 64 after the last request', ({next, last}) => next.atMost(last.plus(64)))]
export const retrySteps = (r = retries()): StepLaw[] => [r.stepLaw('a failure waits at least a tick', ({now, retry}, after) => retry.implies(after.next.gt(now)))]

export const twos = () => recur('twos', {zero: 0, next: (x, y) => when(x.lt(5), y.plus(2), y)}, {
  'at most 10': (_, y) => y.atMost(10),
  'at most 2x': (x, y) => y.atMost(x.times(2)),
})
// A counter that reads twos at the next count: what it holds stays at most 10, by the lemma.
export const counter = () => rule('two by two').inputs({}).state({n: 0, v: 0}).fns({twos: twos()}).step(({n, twos}) => ({n: n.plus(1), v: twos(n.plus(1))}))
export const counterLaws = (r = counter()): Law[] => [r.law('the value is at most 10', ({v}) => v.atMost(10))]

export const filled = () => recur('filled', {args: ['cap'], zero: 0, next: (_, f, {cap}) => min(f.plus(1), cap)}, {
  'within the capacity': (_, f, {cap}) => f.atMost(cap),
  'at most the steps': (x, f) => f.atMost(x),
}, {
  'never drains': (_, f, __, g) => f.atMost(g),
})
export const fillMeter = () => rule('fill meter').params({cap: nat}).inputs({}).state({n: 0, level: 0}).fns({filled: filled()})
  .step(({n, cap, filled}) => ({n: n.plus(1), level: filled(n.plus(1), cap)}))
export const fillMeterLaws = (r = fillMeter()): Law[] => [r.law('the level is within the capacity', ({level, cap}) => level.atMost(cap))]

export const leftovers = () => recur('leftovers', {fns: {rem: modBy(7)}, zero: 0, next: (x, l, {rem}) => l.plus(rem(x))}, {
  'at most 6 a day': (x, l) => l.atMost(x.times(6)),
})
export const ledger = () => rule('leftover ledger').inputs({}).state({day: 0, total: 0}).fns({left: leftovers()})
  .step(({day, left}) => ({day: day.plus(1), total: left(day.plus(1))}))
export const ledgerLaws = (r = ledger()): Law[] => [r.law('at most 6 a day so far', ({total, day}) => total.atMost(day.times(6)))]

export const growing = () => recur('growing', {zero: 1, next: (_, d) => min(d.times(2), 64)}, {
  'at least 1': (_, d) => d.atLeast(1),
  'at most 64': (_, d) => d.atMost(64),
}, {
  'never shrinks': (_, d, __, e) => d.atMost(e),
})
export const escalation = () => rule('escalation').params({start: nat}).inputs({up: oneOf('stay', 'up')}).state({level: ({start}) => start}).fns({delay: growing()})
  .step(({up, level}) => ({level: when(up.is('up'), level.plus(1), level)}))
export const escalationLaws = (r = escalation()): Law[] => [
  r.law('never below the start', ({level, start}) => start.atMost(level)),
  r.law('the delay is at least where it started', ({level, start, delay}) => delay(start).atMost(delay(level))),
]

export const ladder = () => rule('ladder').inputs({up: oneOf('stay', 'up')}).state({prev: 0, level: 0}).fns({delay: growing()})
  .step(({up, level}) => ({prev: level, level: when(up.is('up'), level.plus(1), level)}))
export const ladderLaws = (r = ladder()): Law[] => [
  r.law('the last rung is at most the current one', ({prev, level}) => prev.atMost(level)),
  r.law('the delay at the last rung is at most the delay now', ({prev, level, delay}) => delay(prev).atMost(delay(level))),
]
export const tank = () => rule('tank').inputs({op: oneOf('fill', 'raise'), to: nat}).state({n: 0, room: 0, level: 0}).fns({filled: filled()})
  .step(({op, to, n, room, filled}) => {
    const room2 = when(op.is('raise').and(to.gt(room)), to, room)
    return {n: n.plus(1), room: room2, level: filled(n.plus(1), room2)}
  })
export const tankLaws = (r = tank()): Law[] => [r.law('the level is within the room', ({level, room}) => level.atMost(room))]

export const pump = () => rule('pump').params({cap: nat, goal: nat}).inputs({op: oneOf('wait', 'pump')}).state({n: 0}).fns({filled: filled()})
  .assume(({op, n, cap, filled}) => op.is('pump').implies(filled(n, cap).atMost(cap)))
  .step(({op, n}) => ({n: when(op.is('pump'), n.plus(1), n)}))
export const pumpLive = (r = pump()): Liveness => r.leadsTo('the pump reaches its goal', {
  from: ({n, goal}) => n.lt(goal), to: ({n, goal}) => n.atLeast(goal), rank: ({n, goal}) => goal.minus(n), helpful: () => ({op: 1}),
})

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'states no lemma'] as const) {
    const r = retries(bug), v = proveSteps(r, retryLaws(r), retrySteps(r))
    results.push([`retry with backoff${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  const c = counter(), v = proveSteps(c, counterLaws(c), [])
  results.push(['two by two', v.proven && v.checked, true])
  for (const [what, r, laws] of [['fill meter', fillMeter(), fillMeterLaws], ['leftover ledger', ledger(), ledgerLaws], ['escalation', escalation(), escalationLaws], ['ladder', ladder(), ladderLaws], ['tank', tank(), tankLaws]] as const) {
    const w = proveSteps(r as never, laws(r as never), [])
    results.push([what, w.proven && w.checked, true])
  }
  const p = pump(), lv = proveLeadsTo(p, [], pumpLive(p))
  results.push(['pump', lv.proven && lv.checked, true])
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
