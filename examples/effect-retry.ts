// Retry policies (Effect's Schedule, read by gdp-wired/effect): for the suite (`bun examples/effect-retry.ts`) and
// core/effect-schedule.test.ts. On Effect 4 (examples/effect-retry-policy.ts) and Effect 3 (the same policy in 3.x's
// combinators), each policy read from its source into its rule and checked by stepping Effect's own schedule beside it:
//   - the backoff's laws, proven: the delay never exceeds the cap; never more than 6 retries; it stops after the
//     deadline; the delays never decrease (beside its lemma: the last delay is at most the next backoff, the
//     exponential a `recur` function whose lemmas are proven by induction);
//   - the lease whose acquire is retried with it: read with the retry as part of its step, the policy beside it;
//   - broken: the backoff without its cap. "the delay never exceeds the cap" is refuted by a run of the rule, replayed
//     on Effect's schedule, which waits 3,200 ms at its sixth decision;
//   - broken: a jitter after the cap (Effect 3: jittered after the union) waits past it.
import {mkdirSync, mkdtempSync, readFileSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {fileURLToPath} from 'node:url'
import * as effect from 'effect'
import * as effect3 from 'effect3'
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Any = any
import {type Law} from '../core/machine.ts'
import {type StepLaw, proveRule, proveSteps} from '../core/dsl.ts'
import {type Extraction} from '../core/extract.ts'
import {extractEffect, jitterRun} from '../core/effect.ts'
import type {ScheduleRule} from '../core/effect-schedule.ts'

export const policyFile = fileURLToPath(new URL('./effect-retry-policy.ts', import.meta.url))
// Code in a project of its own whose `effect` is 3.x or 4.x (the check runs it there, and so may the code that imports it).
export function inProject(v: 3 | 4, name: string, code: string): string {
  const dir = mkdtempSync(join(tmpdir(), `gdp-effect${v}-`))
  mkdirSync(join(dir, 'node_modules'))
  symlinkSync(fileURLToPath(new URL(`../node_modules/${v === 3 ? 'effect3' : 'effect'}`, import.meta.url)), join(dir, 'node_modules/effect'))
  writeFileSync(join(dir, name), code)
  return join(dir, name)
}
export const inEffect3 = (name: string, code: string) => inProject(3, name, code)
// The same backoff in Effect 3's combinators: union for 4.x's min, intersect with recurs for upTo's times, upTo of a
// duration (below it, where 4.x's is at most it).
export const policy3 = (bug?: 'no cap' | 'jitter after the cap') => `import {Schedule} from 'effect'
export const backoff = Schedule.exponential('100 millis').pipe(${bug === 'no cap' ? '' : "Schedule.union(Schedule.spaced('2 seconds')), "}${bug === 'jitter after the cap' ? 'Schedule.jittered, ' : ''}Schedule.intersect(Schedule.recurs(6)), Schedule.upTo('10 seconds'))
`
export const policy4 = (bug?: 'no cap') => readFileSync(policyFile, 'utf8').replace(
  "Schedule.min([Schedule.exponential('100 millis'), Schedule.spaced('2 seconds')])", bug ? "Schedule.exponential('100 millis')" : '$&')

export const readPolicy = (v: 3 | 4, bug?: 'no cap' | 'jitter after the cap'): Extraction => v === 4
  ? extractEffect({code: policy4(bug as 'no cap'), file: policyFile}, {entry: 'backoff', effect})
  : extractEffect(inEffect3('policy.ts', policy3(bug)), {entry: 'backoff'})
export const policyLaws = (r: Any): {laws: Law[], stepLaws: StepLaw[]} => {
  const next = Object.keys(r.machine.fns ?? {}).find(f => f.startsWith('exponential'))!
  return {
    laws: [
      r.law('the delay never exceeds the cap', ({delay}: Any) => delay.atMost(2000)),
      r.law('never more than 6 retries', ({retries}: Any) => retries.atMost(6)),
      r.law('it stops after the deadline', ({elapsed, done}: Any) => elapsed.gt(10_000).implies(done)),
      r.law('the last delay is at most the next backoff', (env: Any) => env.delay.atMost(env[next](env.attempt))),
    ],
    stepLaws: [r.stepLaw('the delays never decrease', (b: Any, a: Any) => a.delay.atLeast(b.delay))],
  }
}
export const readLease = (): Extraction => extractEffect(policyFile, {entry: 'make', effect})

if (import.meta.main) {
  const results: [string, boolean, boolean][] = [], runs: string[] = []
  for (const v of [4, 3] as const) {
    const x = readPolicy(v), r = x.rule as Any
    results.push([`backoff (Effect ${v}): read and checked against Effect's schedule (${x.evidence?.requests} decisions)`, x.ok, true])
    const {laws, stepLaws} = policyLaws(r)
    for (const l of laws.slice(0, 3)) { const p = proveRule(r, [l]); results.push([`backoff (Effect ${v}): ${l.name}`, p.proven && p.checked, true]) }
    const s = proveSteps(r, [laws[0]!, laws[3]!], stepLaws)
    results.push([`backoff (Effect ${v}): the delays never decrease`, s.proven && s.checked, true])
    // Broken: no cap. The run that breaks it, and Effect's own schedule taking it.
    const b = readPolicy(v, 'no cap'), br = b.rule as Any, bv = proveRule(br, [policyLaws(br).laws[0]!])
    results.push([`backoff without its cap (Effect ${v}): the delay never exceeds the cap`, bv.proven, false])
    if (bv.run) runs.push(`no cap (Effect ${v}): ${b.replay!(bv.run).what}`)
  }
  {
    // (not proven; the run that breaks it takes each jitter at the top of its range, where a random draw rarely lands)
    const j = readPolicy(3, 'jitter after the cap'), jr = j.rule as Any, cap = policyLaws(jr).laws[0]!, jv = proveRule(jr, [cap])
    const jrun = jv.run ?? jitterRun((j as {schedule?: ScheduleRule}).schedule!, cap)
    results.push([`backoff jittered after its cap (Effect 3): the delay never exceeds the cap`, jv.proven || !jrun, false])
    if (jrun) runs.push(`jitter after the cap (Effect 3): ${j.replay!(jrun).what}`)
  }
  const lease = readLease(), lr = lease.rule as Any, ls = (lease as {schedules?: {use: string, source: string}[]}).schedules ?? []
  results.push([`lease (Effect 4): read with acquire's retry in its step (${ls.map(q => `${q.use} ${q.source.replace(/\s+/g, ' ')}`).join('; ')})`, lease.ok && ls.length > 0, true])
  const lv = proveSteps(lr, lease.invariants ?? [], [lr.stepLaw('an acquire never takes the lease from its holder', (b: Any, a: Any) => b.holder.eq(0).or(a.holder.eq(b.holder)), (b: Any) => b.method.is('acquire'))])
  results.push(['lease (Effect 4): an acquire never takes the lease from its holder', lv.proven && lv.checked, true])
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  for (const r of runs) console.log(`     ${r}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
