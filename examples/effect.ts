// Effect services (core/effect.ts): for the suite (`bun examples/effect.ts`) and core/effect.test.ts.
//   - the daily quota of examples/effect-quota.ts, read from its source with extractEffect (checked by running it on
//     Effect's runtime beside the rule), its laws proven: a user's use stays within the limit, spend reports what is
//     left, a refund never raises the use;
//   - the same quota for one user written by hand, run beside the service with conforms; the broken variant's window
//     lasts a millisecond too long, and a run shows where the two part;
//   - a Schema's kind (fromSchema): commands as a tagged union, the rule over them proven.
import {fileURLToPath} from 'node:url'
import {readFileSync} from 'node:fs'
import * as effect from 'effect'
import {Effect, Schema} from 'effect'
import {type Term, all, bool, forall, int, Int, min, nat, rule, when, yes} from '../core/dsl.ts'
import {conforms, extractEffect, fromSchema} from '../core/effect.ts'
import {proveRule, proveSteps} from '../core/dsl.ts'
import {DAY, make} from './effect-quota.ts'

export const quotaFile = fileURLToPath(new URL('./effect-quota.ts', import.meta.url))
export const readQuota = () => extractEffect(readFileSync(quotaFile, 'utf8'), {file: quotaFile, entry: 'make', effect})
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export const quotaLaws = (r: any) => ({
  laws: [r.law('a user\'s use stays within the limit', ({usage, limit}: any) => forall(k => usage.at(k).used.atMost(limit))),
    r.law('spend reports what is left, never less than nothing', ({spend_result}: any) => spend_result.atLeast(0))],
  stepLaws: [r.stepLaw('a refund never raises the use', ({usage}: any, after: any) => forall(k => after.usage.at(k).used.atMost(usage.at(k).used)), (b: any) => b.method.is('refund'))],
})

// One user's quota by hand: the window open for a day from its start; a spend of units > 0 within the limit.
export const quotaRule = (bug?: 'a window a millisecond too long') => rule('quota').params({limit: nat}).inputs({units: int, now: nat})
  .state({used: int.from(0), windowStart: 0, started: bool.from(false), remaining: int.from(0)})
  .assume(({units, now, used, windowStart, started, limit}) => {
    const open = all(started, windowStart.atMost(now), bug ? Int.of(now).minus(windowStart).atMost(DAY) : Int.of(now).minus(windowStart).lt(DAY))
    return all(units.gt(0), Int.of(limit).atLeast(when(open, used, 0).plus(units)))
  })
  .step(({units, now, used, windowStart, started, limit}) => {
    const open = all(started, windowStart.atMost(now), bug ? Int.of(now).minus(windowStart).atMost(DAY) : Int.of(now).minus(windowStart).lt(DAY))
    const u = when(open, used, 0)
    return {used: u.plus(units), windowStart: when(open, windowStart, now), started: yes, remaining: Int.of(limit).minus(u).minus(units)}
  })
const TIMES = [0, 1, DAY - 1, DAY, DAY + 1, 2 * DAY]
export const quotaConforms = (bug?: 'a window a millisecond too long') => conforms(quotaRule(bug), {
  effect, now: 'now',
  make: ({limit}) => make(limit as number),
  request: (q: Effect.Success<ReturnType<typeof make>>, {units}) => q.spend('ada', units as number),
  observe: (_, remaining) => ({remaining}),
}, {params: rand => ({limit: rand(6)}), draw: rand => ({units: rand(4) - 1, now: TIMES[rand(TIMES.length)]!}), runs: 200, depth: 10})

// Commands as a Schema's tagged union: a spend of some units (capped at 100 in all), or a reset.
export const Command = Schema.Union([Schema.TaggedStruct('Spend', {units: Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))}), Schema.TaggedStruct('Reset', {})])
export const capped = () => rule('capped').inputs({cmd: fromSchema(Command)}).state({total: 0})
  .step(({cmd, total}) => ({total: cmd.match({Spend: (c: {units: Term}) => min(total.plus(c.units), 100), Reset: () => 0})}))

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  const x = readQuota(), r = x.rule!, {laws, stepLaws} = quotaLaws(r)
  results.push(['quota (Effect): read and checked on the runtime', x.ok, true])
  const v = proveRule(r, [...x.invariants!, ...laws]), s = proveSteps(r, x.invariants!, stepLaws)
  results.push(['quota (Effect): its laws', v.proven && v.checked && s.proven && s.checked, true])
  results.push(['quota by hand: runs as the service does', !quotaConforms().failure, true])
  const broken = quotaConforms('a window a millisecond too long')
  results.push(['quota by hand, a window a millisecond too long: runs as the service does', !broken.failure, false])
  const c = capped(), cv = proveRule(c, [c.law('the total stays within 100', ({total}) => total.atMost(100))])
  results.push(['commands from a Schema: the total stays within 100', cv.proven && cv.checked, true])
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got}`)
  if (broken.failure) console.log(`     ${broken.failure}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
