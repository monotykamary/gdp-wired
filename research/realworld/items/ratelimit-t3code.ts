// T3 Code (pingdotgg/t3code), the source-control rate-limit pause, an Effect 4 service (Context.Service, a Ref of a
// ReadonlyMap copied and set in Ref.update, Effect.fn methods, a Schema.TaggedError, Clock). MIT, (c) T3 Tools Inc.
// https://github.com/pingdotgg/t3code/blob/9826dbb9904b2591bfbf60d1317486b59132f56b/packages/source-control-core/src/server/SourceControlRateLimit.ts
//
// A provider host (GitHub, GitLab) that answers 429 is paused: recordRateLimit counts the attempt, bumps the key's
// generation (a lease) and sets retryAt from the Retry-After header or a doubling fallback (30 s to 15 min); check fails
// with SourceControlRateLimitPausedError while it is paused (unless allowPaused) and hands out the generation as the
// lease; recordSuccess with the current lease, once the pause is over, resets the attempts. A rate limit reported under
// an older lease only extends the pause.
// - One key: each method reads and writes the entry of normalizedKey(input, CredentialScope) only (:75-77), a string
//   built from the provider, the host and the scope (a template string, and a service read: the 'scope' gap); keys are
//   independent.
// - `now: nat` is Clock.currentTimeMillis, read once a call. input.retryAt (optional) is `hinted` and `hint`;
//   options?.allowPaused === true is `allowPaused`; the lease a natural (a generation check returned).
// - fallbackCooldownMs (:79-84): Math.min(30_000 * 2 ** Math.max(0, attempt - 1), 900_000), by cases of the attempt.
// research/realworld/repro/conform-effect.ts runs this rule beside the original service (fetched at the pin, run on
// Effect 4.0.7), and reads the original with gdp-wired/effect's extractEffect, which refuses it where it first leaves the
// subset: check's optional argument (`options?: {allowPaused}`, a value that may be missing, at :104); past it, the key's
// template string and the context reference it reads.
import {Int, bool, int, max, nat, oneOf, rule, when, yes} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'pingdotgg/t3code', commit: '9826dbb9904b2591bfbf60d1317486b59132f56b', licence: 'MIT', author: 'T3 Tools Inc.', language: 'TypeScript', path: 'packages/source-control-core/src/server/SourceControlRateLimit.ts'}
export const MAX = 900_000

export const pause = () => rule('t3codeRateLimit')
  .inputs({op: oneOf('check', 'recordRateLimit', 'recordSuccess'), allowPaused: bool, lease: nat, hinted: bool, hint: nat, now: nat})
  .state({has: bool.from(false), attempt: nat.from(0), generation: nat.from(0), retryAt: int.from(0), result: nat.from(0)})
  // :107-113 a paused key fails the check (SourceControlRateLimitPausedError), unless allowPaused
  .assume(({op, has, retryAt, now, allowPaused}) => op.is('check').implies(has.and(Int.of(retryAt).gt(now), allowPaused.not()).not()))
  .step(({op, allowPaused, lease, hinted, hint, now, has, attempt, generation, retryAt}) => {
    void allowPaused
    // :125-136 a rate limit under an older lease only extends the pause, by a later Retry-After
    const stale = has.and(generation.gt(lease))
    const extended = when(hinted.and(Int.of(hint).gt(retryAt)), Int.of(hint), Int.of(retryAt))
    // :138-151 counted: the attempt, the generation past the lease, the pause from the header or the fallback
    const next = when(has, attempt, 0).plus(1)
    const cooldown = when(next.atMost(1), 30_000, when(next.eq(2), 60_000, when(next.eq(3), 120_000, when(next.eq(4), 240_000, when(next.eq(5), 480_000, MAX)))))
    const proposed = when(hinted.and(Int.of(hint).gt(now)), Int.of(hint), Int.of(now).plus(cooldown))
    const counted = when(has.and(Int.of(retryAt).gt(now)), Int.of(retryAt).max(proposed), proposed)
    // :163-171 a success with the current lease, once the pause is over, resets the attempts
    const resets = op.is('recordSuccess').and(has, generation.eq(lease), Int.of(retryAt).atMost(now))
    const rl = op.is('recordRateLimit')
    return {
      has: has.or(rl),
      attempt: when(rl.and(stale.not()), next, when(resets, 0, attempt)),
      generation: when(rl.and(stale.not()), max(when(has, generation, 0), lease).plus(1), generation),
      retryAt: when(rl, when(stale, extended, counted), when(resets, Int.of(0), Int.of(retryAt))),
      // :114 entry?.generation ?? 0
      result: when(op.is('check'), when(has, generation, 0), 0),
    }
  })

const p = pause()
export const items: RealItem[] = [{
  id: 'ratelimit/t3code/SourceControlRateLimit',
  domain: 'rate limit',
  source: {...src, lines: '75-177', export: 'make (SourceControlRateLimit)'},
  summary: 'A rate-limit pause per provider host: a 429 counts an attempt, bumps the key\'s generation and pauses it until the Retry-After or a doubling fallback (30 s to 15 min); check fails while paused and hands out the generation as a lease; a success on the current lease after the pause resets the attempts.',
  expressible: 'partial',
  gaps: [
    {gap: 'scope', blocks: 'part', detail: 'one key: normalizedKey(input, yield* CredentialScope) builds it with a template string from the provider, the host and a context reference; keys are independent'},
  ],
  laws: [
    stepLaw(p, p.stepLaw('a key\'s generation never goes down', ({generation}, after) => after.generation.atLeast(generation), () => yes),
      'step', 'inferred', 'the generation is the lease check hands out (:114); a report under an older lease is told apart by it (:125)'),
    invariant(p, p.law('a key\'s attempts are at most its generation', ({attempt, generation}) => attempt.atMost(generation)),
      'safety', 'inferred', 'each counted rate limit bumps both (:138, :149); a success resets the attempts only (:170)'),
    stepLaw(p, p.stepLaw('a counted rate limit pauses the key past now', ({now}, after) => Int.of(after.retryAt).gt(now), ({op, has, generation, lease}) => op.is('recordRateLimit').and(has.and(generation.gt(lease)).not())),
      'step', 'inferred', ':139-146 the pause is the Retry-After when later than now, else now plus the fallback cooldown'),
    stepLaw(p, p.stepLaw('a rate limit with no Retry-After pauses at most 15 minutes past what was paused', ({retryAt, now}, after) => Int.of(after.retryAt).atMost(Int.of(retryAt).max(Int.of(now).plus(MAX))), ({op, hinted}) => op.is('recordRateLimit').and(hinted.not())),
      'step', 'docs', ':16 MAX_FALLBACK_COOLDOWN = Duration.minutes(15)'),
    stepLaw(p, p.stepLaw('a success on the current lease after the pause ends the backoff', (_, after) => after.attempt.eq(0), ({op, has, generation, lease, retryAt, now}) => op.is('recordSuccess').and(has, generation.eq(lease), Int.of(retryAt).atMost(now))),
      'step', 'inferred', ':163-171 recordSuccess resets attempt to 0 when the lease is the generation and the pause is over'),
  ],
}]
