// Effect's rate limiter store in memory (Effect-TS/effect 4.0.7, the `effect` package's effect/persistence
// RateLimiter.layerStoreMemory): fixedWindow and tokenBucket, each an Effect.sync over a Map of counters read with the
// clock (Effect.clockWith). MIT, (c) Effectful Technologies.
// https://github.com/Effect-TS/effect/blob/b174739b6b39e4bf48f00f38f1d9fde7a6934368/packages/effect/src/persistence/RateLimiter.ts
//
// Mapping, common to the two items:
// - One key. Each call reads and writes the counter of options.key only (:745, :763), so keys are independent.
// - `now: nat` is the clock's time, read once a call (clock.currentTimeMillisUnsafe(), :744, :762).
// - refillRate is a Duration each call gives; RateLimiter.consume passes window / limit (:109), the same for every call
//   of one limiter. It is fixed here at R = 1000 ms: `refillRateMillis * options.tokens` (:755) is a product of two
//   unknowns otherwise (the 'nonlinear' gap); Math.floor(x / R) (:767) is then a floor by a constant, exact.
// - options.tokens is taken as a natural: RateLimiter.consume's default is 1 (:104), and a negative count, a refund, is
//   the caller's (left out by choice).
// research/realworld/repro/conform-effect.ts runs both rules beside the real store (Effect 4.0.7) with the clock set.
import {Int, bool, int, nat, rule, when, yes} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'Effect-TS/effect', commit: 'b174739b6b39e4bf48f00f38f1d9fde7a6934368', licence: 'MIT', author: 'Effectful Technologies', language: 'TypeScript', path: 'packages/effect/src/persistence/RateLimiter.ts'}
export const R = 1000

export const fixedWindow = () => rule('effectFixedWindow')
  // options.limit: `given` when it is a number (consume passes undefined for onExceeded "delay", :131)
  .params({limit: nat, given: bool})
  .inputs({n: nat, now: nat})
  .state({has: bool.from(false), count: int.from(0), expiresAt: int.from(0), returned: int.from(0), ttl: int.from(0)})
  .step(({n, now, limit, given, has, count, expiresAt}) => {
    // :746-749 a missing or expired counter starts over at now (and is stored, whatever follows)
    const reset = has.not().or(Int.of(expiresAt).atMost(now))
    const c0 = when(reset, Int.of(0), Int.of(count)), e0 = when(reset, Int.of(now), Int.of(expiresAt))
    // :750-752 `options.limit && counter.count + options.tokens > options.limit`: a limit of 0 is falsy
    const over = given.and(limit.gt(0)).and(c0.plus(n).gt(limit))
    // :753-755 count += tokens; expiresAt += refillRateMillis * tokens
    const e1 = when(over, e0, e0.plus(Int.of(n).times(R)))
    return {has: yes, count: when(over, c0, c0.plus(n)), expiresAt: e1, returned: c0.plus(n), ttl: e1.minus(now)}
  })

export const tokenBucket = () => rule('effectTokenBucket')
  .params({limit: nat, overflow: bool}) // options.limit, options.allowOverflow (consume: onExceeded === "delay", :176)
  .inputs({n: nat, now: nat})
  .state({has: bool.from(false), tokens: int.from(0), lastRefill: int.from(0), remaining: int.from(0), elapsed: int.from(0)})
  .step(({n, now, limit, overflow, has, tokens, lastRefill}) => {
    // :764-767 a new bucket is full, refilled from now
    const t0 = when(has, Int.of(tokens), Int.of(limit)), l0 = when(has, Int.of(lastRefill), Int.of(now))
    // :768-772 Math.floor((now - lastRefill) / refillRateMillis) whole intervals added, up to the limit
    const add = Int.of(now).minus(l0).divBy(R), refills = add.gt(0)
    const t1 = when(refills, t0.plus(add).min(limit), t0), l1 = when(refills, l0.plus(add.times(R)), l0)
    // :773-775 a full bucket restarts its interval
    const l2 = when(t1.atLeast(limit), Int.of(now), l1)
    // :777-781 the tokens taken where they are there, or always with overflow
    const left = t1.minus(n)
    return {has: yes, tokens: when(overflow.or(left.atLeast(0)), left, t1), lastRefill: l2, remaining: left, elapsed: Int.of(now).minus(l2).max(0)}
  })

const fw = fixedWindow(), tb = tokenBucket()
export const items: RealItem[] = [{
  id: 'ratelimit/effect/fixedWindow',
  domain: 'rate limit',
  source: {...src, lines: '742-759', export: 'layerStoreMemory (fixedWindow)'},
  also: [{...src, lines: '100-168', export: 'make (consume, fixed-window)'}],
  summary: 'A fixed window per key: a window that has expired starts over at now; a request within the limit adds its tokens and extends the window by the refill rate per token; one over the limit is counted in the reply only.',
  expressible: 'partial',
  gaps: [
    {gap: 'nonlinear', blocks: 'part', detail: 'refillRateMillis * options.tokens: the refill rate is fixed at 1000 ms (one limiter\'s window / limit)'},
    {gap: 'scope', blocks: 'part', detail: 'one key (keys are independent); tokens a natural (a negative count, a refund, is left out)'},
  ],
  laws: [
    invariant(fw, fw.law('a window never counts more than the limit given', ({count, limit, given}) => given.implies(Int.of(count).atMost(limit))),
      'safety', 'docs', ':638-639 "If `limit` is provided, the number of taken tokens will be capped at the limit."'),
    stepLaw(fw, fw.stepLaw('a request over the limit leaves the window\'s TTL as it was', ({expiresAt}, after) => Int.of(after.returned).atMost(after.count).or(Int.of(after.expiresAt).eq(expiresAt)), ({has, expiresAt, now, given}) => has.and(Int.of(expiresAt).gt(now), given)),
      'step', 'docs', ':641-642 "In the case the limit is exceeded, the returned count will be greater than the limit, but the TTL will not be updated."'),
    stepLaw(fw, fw.stepLaw('an expired window starts over', ({n}, after) => Int.of(after.count).atMost(n), ({has, expiresAt, now}) => has.and(Int.of(expiresAt).atMost(now))),
      'step', 'inferred', ':747 `counter.expiresAt <= now`: a new counter { count: 0, expiresAt: now }'),
    invariant(fw, fw.law('a window\'s count is never below 0', ({count}) => Int.of(count).atLeast(0)),
      'safety', 'inferred', 'tokens taken are counted up from 0 (:748, :754)'),
  ],
}, {
  id: 'ratelimit/effect/tokenBucket',
  domain: 'rate limit',
  source: {...src, lines: '760-785', export: 'layerStoreMemory (tokenBucket)'},
  also: [{...src, lines: '169-200', export: 'make (consume, token-bucket)'}],
  summary: 'A token bucket per key: a new bucket is full; whole refill intervals since the last refill add tokens up to the limit; a full bucket restarts its interval; a request takes its tokens where they are there (or always, with overflow) and replies with what is left and the time into the interval.',
  expressible: 'partial',
  gaps: [
    {gap: 'nonlinear', blocks: 'part', detail: 'the refill rate fixed at 1000 ms (Math.floor((now - lastRefill) / refillRateMillis) is then a floor by a constant, exact)'},
    {gap: 'scope', blocks: 'part', detail: 'one key; tokens a natural; the limit fixed for the bucket (a call may give another)'},
  ],
  laws: [
    invariant(tb, tb.law('a bucket never holds more than its limit', ({tokens, limit}) => Int.of(tokens).atMost(limit)),
      'safety', 'inferred', ':770 Math.min(options.limit, bucket.tokens + tokensToAdd)'),
    invariant(tb, tb.law('without overflow, a bucket never holds less than nothing', ({tokens, overflow}) => overflow.not().implies(Int.of(tokens).atLeast(0))),
      'safety', 'docs', ':656-657 "A negative count is only persisted when `allowOverflow` is true."'),
    stepLaw(tb, tb.stepLaw('the time into the interval is under the refill rate', (_, after) => Int.of(after.elapsed).lt(R).and(Int.of(after.elapsed).atLeast(0)), () => yes),
      'step', 'docs', ':659-661 "`elapsedMillis` is the time since the current refill interval started ... always at least `0` and less than `Duration.toMillis(refillRate)`."'),
    stepLaw(tb, tb.stepLaw('a request refused for want of tokens takes none', ({tokens}, after) => Int.of(after.remaining).atLeast(0).or(Int.of(after.tokens).atLeast(tokens)), ({has, overflow}) => has.and(overflow.not())),
      'step', 'docs', ':656-657 "A negative count is only persisted when `allowOverflow` is true."'),
  ],
}]
