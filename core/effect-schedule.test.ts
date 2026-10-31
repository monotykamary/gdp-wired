// Effect's Schedule as a rule (core/effect-schedule.ts through core/effect.ts), on Effect 4.x and 3.x: every combinator
// read and stepped beside Effect's own schedule (random attempt times, inputs and jitters, the decisions and delays
// compared); the laws a reviewer states proven, the broken policies refuted by runs Effect's schedule takes; retry and
// repeat inside a method read as part of its step, checked on the runtime; and what isn't read refused with why.
import {expect, test} from 'bun:test'
import * as effect from 'effect'
import {proveRule, proveSteps} from './dsl.ts'
import {extractEffect, fromSchedule, jitterRun, scheduleConforms} from './effect.ts'
import type {ScheduleRule} from './effect-schedule.ts'
import {inProject, policyLaws, readLease, readPolicy} from '../examples/effect-retry.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Any = any
// A schedule written for Effect 3, in a project whose effect is 3.x (its parameters the rule's params).
const sched3 = (src: string, params: string[] = [], runs = 100) => extractEffect(inProject(3, 's.ts', `import {Duration, Effect, Schedule} from 'effect'\nexport const s = (${params.map(p => `${p}: number`).join(', ')}) => ${src}\n`), {entry: 's', check: {runs}} as never)
const sched4 = (src: string, params: string[] = [], runs = 100) => fromSchedule(src, {effect, params, runs})

const TAGGED = '{_tag: "Timeout"} | {_tag: "Refused", code: number}'
export const V4 = [
  'Schedule.spaced("100 millis")', 'Schedule.recurs(3)', 'Schedule.forever', 'Schedule.once', 'Schedule.exponential("10 millis")',
  'Schedule.exponential("10 millis", 3)', 'Schedule.fibonacci("10 millis")', 'Schedule.during("1 second")', 'Schedule.duration("50 millis")',
  'Schedule.spaced("100 millis").pipe(Schedule.upTo({times: 3}))', 'Schedule.fibonacci("10 millis").pipe(Schedule.upTo({duration: "2 seconds"}))',
  'Schedule.exponential("10 millis").pipe(Schedule.upTo({times: 5, duration: "1 second"}))',
  'Schedule.min([Schedule.exponential("100 millis"), Schedule.spaced("2 seconds")])', 'Schedule.max([Schedule.recurs(4), Schedule.spaced("50 millis")])',
  'Schedule.min([Schedule.recurs(2), Schedule.spaced("50 millis").pipe(Schedule.upTo({times: 4}))])',
  'Schedule.concat(Schedule.recurs(2), Schedule.spaced("1 second").pipe(Schedule.upTo({times: 3})))',
  'Schedule.concat(Schedule.recurs(1), Schedule.during("300 millis"))',
  'Schedule.spaced("10 millis").pipe(Schedule.while(({attempt, elapsed}) => attempt < 4 && elapsed <= 500))',
  'Schedule.exponential("10 millis").pipe(Schedule.while(({output}) => Duration.isLessThan(output, Duration.millis(100))))',
  `Schedule.spaced("10 millis").pipe(Schedule.while(({input}: {input: ${TAGGED}}) => input._tag === "Timeout"))`,
  'Schedule.spaced("10 millis").pipe(Schedule.while(({input}: {input: number}) => input < 2))',
  'Schedule.spaced("10 millis").pipe(Schedule.addDelay(({attempt}) => Effect.succeed(Duration.millis(attempt * 5))))',
  'Schedule.exponential("10 millis").pipe(Schedule.modifyDelay(({duration}) => Effect.succeed(Duration.min(duration, Duration.seconds(1)))))',
  'Schedule.exponential("10 millis", 3).pipe(Schedule.jittered)', 'Schedule.exponential("100 millis").pipe(Schedule.jittered, (s) => Schedule.min([s, Schedule.spaced("2 seconds")]))',
  'Schedule.concat(Schedule.recurs(2), Schedule.exponential("10 millis").pipe(Schedule.jittered, Schedule.upTo({duration: "1 second"})))',
  'Schedule.recurs(3).pipe(Schedule.passthrough)', 'Schedule.recurs(n)', 'Schedule.spaced(Duration.millis(n)).pipe(Schedule.upTo({times: 4}))',
  // (inside min, which steps a schedule again after it stopped: each combinator counts its own metadata)
  'Schedule.min([Schedule.spaced(10), Schedule.spaced(1).pipe(Schedule.while(({input}: {input: boolean}) => input), Schedule.upTo({times: 1}))])',
  'Schedule.min([Schedule.spaced(50), Schedule.spaced(5).pipe(Schedule.while(({input}: {input: boolean}) => input), Schedule.while(({attempt, elapsed}) => attempt <= 2 && elapsed <= 30), Schedule.addDelay(({attempt}) => Effect.succeed(Duration.millis(attempt))))])',
]
export const V3 = [
  'Schedule.spaced("100 millis")', 'Schedule.recurs(3)', 'Schedule.forever', 'Schedule.once', 'Schedule.stop', 'Schedule.exponential("10 millis")',
  'Schedule.exponential("10 millis", 3)', 'Schedule.fibonacci("10 millis")', 'Schedule.linear("10 millis")', 'Schedule.fromDelay("50 millis")',
  'Schedule.recurUpTo("300 millis")', 'Schedule.fibonacci("10 millis").pipe(Schedule.upTo("2 seconds"))',
  'Schedule.exponential("10 millis").pipe(Schedule.union(Schedule.spaced("1 second")))', 'Schedule.either(Schedule.recurs(2), Schedule.spaced("50 millis"))',
  'Schedule.intersect(Schedule.recurs(4), Schedule.spaced("50 millis"))', 'Schedule.recurs(4).pipe(Schedule.zipLeft(Schedule.spaced("20 millis")))',
  'Schedule.recurs(4).pipe(Schedule.zipRight(Schedule.exponential("20 millis")))',
  'Schedule.recurs(2).pipe(Schedule.andThen(Schedule.spaced("1 second").pipe(Schedule.upTo("3 seconds"))))',
  'Schedule.linear("10 millis").pipe(Schedule.whileOutput((d) => Duration.lessThan(d, Duration.millis(60))))',
  'Schedule.recurs(9).pipe(Schedule.untilOutput((n) => n >= 3))',
  `Schedule.spaced("10 millis").pipe(Schedule.whileInput((e: ${TAGGED}) => e._tag === "Timeout"))`,
  'Schedule.spaced("10 millis").pipe(Schedule.untilInput((n: number) => n > 3))',
  'Schedule.recurs(9).pipe(Schedule.check((n: number, out) => n < 2 || out < 3))',
  'Schedule.exponential("10 millis").pipe(Schedule.modifyDelay((_, d) => Duration.min(d, Duration.millis(200))))',
  'Schedule.spaced("10 millis").pipe(Schedule.addDelay((n) => Duration.millis(n * 5)))',
  'Schedule.exponential("10 millis").pipe(Schedule.jittered)', 'Schedule.exponential("10 millis").pipe(Schedule.jitteredWith({min: 0.5, max: 1.5}), Schedule.union(Schedule.spaced("1 second")))',
  'Schedule.recurs(3).pipe(Schedule.andThen(Schedule.exponential("10 millis").pipe(Schedule.jittered, Schedule.upTo("1 second"))))',
  'Schedule.recurs(n).pipe(Schedule.either(Schedule.spaced(Duration.seconds(m))))',
]
// (the params a source reads: n where it recurs(n) or waits millis(n), m where it waits seconds(m))
const params = (src: string) => [...(/recurs\(n\)|millis\(n\)/.test(src) ? ['n'] : []), ...(/seconds\(m\)/.test(src) ? ['m'] : [])]

test('every combinator (4.x) decides as Effect\'s own schedule does: random attempt times, inputs, jitters and params', () => {
  for (const src of V4) {
    const x = sched4(src, params(src))
    expect([src, x.ok, x.refusals]).toEqual([src, true, []])
    expect(x.evidence!.requests).toBeGreaterThanOrEqual(100)
  }
}, 600_000)

test('every combinator (3.x) decides as Effect\'s own schedule does: random attempt times, inputs, jitters and params', () => {
  for (const src of V3) {
    const x = sched3(src, params(src))
    expect([src, x.ok, x.refusals]).toEqual([src, true, []])
    expect(x.evidence!.requests).toBeGreaterThanOrEqual(100)
  }
}, 600_000)

test('a rule given wrongly is caught: the rule of one schedule beside Effect running another parts at the first decision they differ', () => {
  const x = sched4('Schedule.spaced("100 millis").pipe(Schedule.upTo({duration: "300 millis"}))') as Any
  expect(scheduleConforms(x.schedule, () => effect.Schedule.spaced('101 millis').pipe(effect.Schedule.upTo({duration: '300 millis'})), effect).failure).toMatch(/Effect's schedule waits 101 ms, the rule 100 ms/)
  // (a deadline 50 ms early: a decision between the two deadlines parts)
  expect(scheduleConforms(x.schedule, () => effect.Schedule.spaced('100 millis').pipe(effect.Schedule.upTo({duration: '250 millis'})), effect, {runs: 300}).failure).toMatch(/Effect's schedule stops, the rule goes on/)
}, 120_000)

test('the backoff\'s laws, both lines: within the cap, at most 6 retries, stops after the deadline, never decreasing (beside its lemma)', () => {
  for (const v of [4, 3] as const) {
    const x = readPolicy(v), r = x.rule as Any, {laws, stepLaws} = policyLaws(r)
    expect(x.ok).toBe(true)
    for (const l of laws.slice(0, 3)) expect([v, l.name, proveRule(r, [l])]).toMatchObject([v, l.name, {proven: true, checked: true}])
    expect(proveSteps(r, [laws[0]!, laws[3]!], stepLaws)).toMatchObject({proven: true, checked: true})
    // (the exponential a recur function: its lemmas proven by induction when it is made, its facts the rule's)
    expect(Object.keys(r.machine.fns)).toEqual(['exponential_x2_b100'])
    expect(x.notes.join('\n')).toMatch(/defined by its recurrence .* proven by induction/)
  }
}, 300_000)

test('broken: the backoff without its cap is refuted by a run, and Effect\'s own schedule takes it past the cap', () => {
  for (const v of [4, 3] as const) {
    const x = readPolicy(v, 'no cap'), r = x.rule as Any, verdict = proveRule(r, [policyLaws(r).laws[0]!])
    expect(verdict.proven).toBe(false)
    expect(verdict.run!.trace.length).toBeGreaterThanOrEqual(6)
    expect(x.replay!(verdict.run!)).toEqual({ok: true, what: 'Effect\'s schedule, decision by decision: goes on after 100 ms, goes on after 200 ms, goes on after 400 ms, goes on after 800 ms, goes on after 1600 ms, goes on after 3200 ms'})
  }
}, 300_000)

test('broken: a jitter after the cap waits past it, a run Effect\'s schedule takes with its Random answered', () => {
  const x = readPolicy(3, 'jitter after the cap'), r = x.rule as Any, cap = policyLaws(r).laws[0]!
  expect(proveRule(r, [cap]).proven).toBe(false)
  const run = jitterRun((x as {schedule?: ScheduleRule}).schedule!, cap)!
  expect(run.trace.length).toBe(6)
  expect(x.replay!(run).what).toMatch(/goes on after 2399 ms$/)
  // (and before the cap, within it: a jitter of the delay before the cap is capped)
  const fine = extractEffect(inProject(3, 'p.ts', 'import {Schedule} from \'effect\'\nexport const p = Schedule.exponential(\'100 millis\').pipe(Schedule.jittered, Schedule.union(Schedule.spaced(\'2 seconds\')), Schedule.intersect(Schedule.recurs(6)))\n'), {entry: 'p'}), fr = fine.rule as Any
  expect(proveRule(fr, [fr.law('the delay never exceeds the cap', ({delay}: Any) => delay.atMost(2000))])).toMatchObject({proven: true, checked: true})
}, 300_000)

test('retry and repeat inside a method (4.x and 3.x): read as part of its step, checked on the runtime', () => {
  const svc = (body: string) => `import {Data, Effect, Ref, Schedule} from 'effect'
export class Busy extends Data.TaggedError('Busy')<{}> {}
export const make = Effect.gen(function* () {
  const n = yield* Ref.make(0)
${body}
})`
  const take = (retry: string) => `  const take = Effect.fn('take')(function* (k: number) {
    yield* Effect.gen(function* () { const x = yield* Ref.get(n); if (x + k > 10) return yield* new Busy(); yield* Ref.set(n, x + k) }).pipe(${retry})
  })
  return {take}`
  const cases: [3 | 4, string][] = [
    [4, take('Effect.retry(Schedule.exponential(\'10 millis\').pipe(Schedule.upTo({times: 3})))')], [4, take('Effect.retry({times: 2})')],
    [4, take('Effect.retry({schedule: Schedule.spaced(\'5 millis\'), times: 3, while: (e) => e._tag === \'Busy\'})')],
    [3, take('Effect.retry(Schedule.recurs(2).pipe(Schedule.addDelay(() => \'5 millis\')))')], [3, take('Effect.retry({times: 3})')],
    [4, '  const bump = Effect.fn(\'bump\')(function* () { yield* Ref.update(n, x => x + 1).pipe(Effect.repeat(Schedule.recurs(2))) })\n  return {bump}'],
    [3, '  const bump = Effect.fn(\'bump\')(function* () { yield* Ref.update(n, x => x + 2).pipe(Effect.repeat({times: 3})) })\n  return {bump}'],
    [4, '  const bump = Effect.fn(\'bump\')(function* () { yield* Effect.repeat(Ref.update(n, x => x + 1), Schedule.spaced(\'1 second\').pipe(Schedule.upTo({times: 2}))) })\n  return {bump}'],
  ]
  for (const [v, body] of cases) {
    const x = extractEffect(inProject(v, 'svc.ts', svc(body)), {entry: 'make'}) as Any
    expect([v, body, x.ok, x.refusals]).toEqual([v, body, true, []])
    expect(x.evidence.requests).toBeGreaterThan(1000)
    expect(x.schedules.length).toBe(1)
  }
}, 300_000)

test('what the schedule reader doesn\'t take is refused where it is, with the reason and what reads instead', () => {
  const refused: [3 | 4, string, RegExp][] = [
    [4, 'Schedule.exponential("10 millis", 1.5)', /a whole number at least 1/],
    [4, 'Schedule.spaced("1.5 millis")', /a whole number of milliseconds/],
    [4, 'Schedule.cron("* * * * *")', /Schedule.cron in Effect 4/],
    [4, 'Schedule.fixed("1 second")', /Schedule.fixed in Effect 4/],
    [4, 'Schedule.union(Schedule.recurs(1), Schedule.spaced("1 second"))', /Schedule.union in Effect 4/],
    [3, 'Schedule.during("1 second")', /Schedule.during in Effect 3/],
    [4, 'Schedule.min([Schedule.recurs(2), Schedule.spaced("1 second")]).pipe(Schedule.while(({output}) => output < 3))', /the output of this schedule/],
    [4, 'Schedule.spaced("10 millis").pipe(Schedule.map(({output}) => output))', /Schedule.map/],
    [4, 'Schedule.spaced("10 millis").pipe(Schedule.while(({now}) => now < 3))', /the metadata's now/],
    [3, 'Schedule.spaced("10 millis").pipe(Schedule.whileInput((e: {at: Date}) => e.at === e.at))', /the input's Date/],
    [3, 'Schedule.spaced("10 millis").pipe(Schedule.addDelay((n) => Duration.millis(n - 1)))', /a subtraction/],
    [4, 'Schedule.spaced(Duration.millis(Math.random()))', /Math.random\(\): a number other than/],
  ]
  for (const [v, src, why] of refused) {
    const x = v === 4 ? sched4(src) : sched3(src)
    expect([src, x.ok]).toEqual([src, false])
    expect(x.refusals[0]!.what).toMatch(why)
  }
  // Inside a method: a retry that never ends, the clock read in what is retried, a repeat's value, a repeat reading the
  // effect's result, a policy reading the service's params.
  const svc = (body: string, ps = '') => `import {Clock, Data, Effect, Ref, Schedule} from 'effect'
export class Busy extends Data.TaggedError('Busy')<{}> {}
export const make = (${ps}) => Effect.gen(function* () {
  const n = yield* Ref.make(0)
  const go = Effect.fn('go')(function* (k: number) {
${body}
  })
  return {go}
})`
  const inner = 'Effect.gen(function* () { const x = yield* Ref.get(n); if (x + k > 10) return yield* new Busy(); yield* Ref.set(n, x + k) })'
  const methods: [string, RegExp, string?][] = [
    [`yield* ${inner}.pipe(Effect.retry(Schedule.spaced('1 second')))`, /goes on past 1000 attempts .* the call would never return/],
    [`yield* Effect.gen(function* () { const t = yield* Clock.currentTimeMillis; if (t < 10) return yield* new Busy(); yield* Ref.set(n, k) }).pipe(Effect.retry(Schedule.recurs(3)))`, /the clock read in an effect that is retried/],
    ['const c = yield* Ref.update(n, x => x + 1).pipe(Effect.repeat(Schedule.recurs(2)))\n    return c', /the value of a repeat/],
    ['yield* Ref.updateAndGet(n, x => x + 1).pipe(Effect.repeat(Schedule.recurs(5).pipe(Schedule.while(({input}: {input: number}) => input < 3))))', /reads the effect's result/],
    [`yield* ${inner}.pipe(Effect.retry(Schedule.recurs(max)))`, /max: a retry policy reading the service's params/, 'max: number'],
    ['yield* Ref.update(n, x => x + 1).pipe(Effect.repeat(Schedule.recurs(40)))', /runs the effect 41 times \(up to 17 are unrolled\)/],
    ['yield* Ref.update(n, x => x + 1).pipe(Effect.repeat(Schedule.spaced("1 second").pipe(Schedule.upTo({times: 1}))))\n    const t = yield* Clock.currentTimeMillis\n    yield* Ref.set(n, t)', /the clock read after a repeat that waits/],
  ]
  for (const [body, why, ps] of methods) {
    const x = extractEffect(svc(body, ps), {file: 'svc.ts', entry: 'make', effect})
    expect([body, x.ok]).toEqual([body, false])
    expect(x.refusals[0]!.what).toMatch(why)
  }
}, 300_000)

test('the lease (examples/effect-retry-policy.ts): acquire retried with the backoff, read with it, its law proven', () => {
  const x = readLease() as Any, r = x.rule
  expect([x.ok, x.refusals]).toEqual([true, []])
  expect(x.schedules.map((s: Any) => s.use)).toEqual(['retry'])
  expect(proveSteps(r, x.invariants ?? [], [r.stepLaw('an acquire never takes the lease from its holder', (b: Any, a: Any) => b.holder.eq(0).or(a.holder.eq(b.holder)), (b: Any) => b.method.is('acquire'))])).toMatchObject({proven: true, checked: true})
}, 120_000)
