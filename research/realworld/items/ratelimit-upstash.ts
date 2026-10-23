// @upstash/ratelimit v2.2.0 (upstash/ratelimit-js), the single-region algorithms: fixedWindow, slidingWindow and
// tokenBucket, each a Lua script run atomically on Redis (src/lua-scripts/single.ts) and the TypeScript around it
// (src/single.ts), with the ephemeral in-memory block cache (src/cache.ts) that is on by default (src/ratelimit.ts:152-153).
// MIT, (c) Upstash. https://github.com/upstash/ratelimit-js/tree/fccd840d6e0f893f50bc677107fba4d913a414e3/src
//
// Mapping, common to the three items:
// - One identifier. Every Redis key and cache entry is named by the identifier (single.ts:189, :308, :459), and no step
//   reads another identifier's, so identifiers are independent and one is the whole story.
// - `now: nat` is sent in with each request: the TS reads Date.now() once (single.ts:188, :306, :435) and the cache reads
//   it again (cache.ts:20); both are taken to be this one `now`.
// - `rate` (incrementBy, `rate ?? 1`, single.ts:190) may be negative (a refund, tests in src/negative-rate.test.ts):
//   `refund: bool` and `n: nat` give incrementBy = refund ? -n : n.
// - Lua numbers are doubles; every value here is an integer below 2^53 (ms timestamps, counts), where the scripts'
//   +, -, *, math.floor and math.ceil of quotients are exact for any realistic value (quotient times divisor below 2^52).
// - A floor or ceiling quotient by a param (Math.floor(now / window), math.floor(elapsed / interval)) is carried by the
//   request as an input that `.assume` pins to its definition (d × q ≤ x < d × (q + 1)): the code's value, exactly. (A
//   function known by these facts would say the same, but the searches run no rule that reads one.)
import {type Cond, type Int, type Term, bool, forall, int, max, min, nat, no, rule, same, when, yes} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'upstash/ratelimit-js', commit: 'fccd840d6e0f893f50bc677107fba4d913a414e3', licence: 'MIT', author: 'Upstash'}
const ts = (lines: string, exp: string) => ({...src, path: 'src/single.ts', lines, export: exp, language: 'TypeScript'})
const lua = (lines: string, exp: string) => ({...src, path: 'src/lua-scripts/single.ts', lines, export: exp, language: 'Lua'})
const cache = {...src, path: 'src/cache.ts', lines: '14-37', export: 'Cache', language: 'TypeScript'}

// ---------------------------------------------------------------------------------------------------------------------
// fixedWindow(tokens, window): single.ts:175-238, the script fixedWindowLimitScript (single.ts:1-25).
// The Redis key `identifier:bucket` (single.ts:188-189) is the map `Count` at the bucket floor(now / window). Its TTL
// (PEXPIRE window, script :18-21, set when the INCRBY returns incrementBy, i.e. the key was absent or 0) is not
// modelled: a key of bucket b is first written at some t in [b·window, (b + 1)·window) and expires at t + window or
// later, so it is never read past its TTL (it is read only while now is in bucket b). Counts are integers: a refund
// (negative rate) may take a bucket below 0 (script :17 INCRBY).
export const fixedWindow = () => rule('upstash fixedWindow')
  // single.ts:179-185 tokens, windowDuration = ms(window).
  .params({tokens: nat, window: nat})
  .pre(({window}) => window.atLeast(1))
  // `b`: the bucket, Math.floor(Date.now() / windowDuration) (single.ts:188).
  .inputs({now: nat, refund: bool, n: nat, b: nat})
  .assume(({b, now, window}) => b.mul(window).atMost(now).and(now.lt(b.plus(1).mul(window))))
  // Ghosts: `Admitted`, `Refunded` per bucket (the tokens of the consuming requests that succeeded, the tokens
  // refunded: observed results); `ok`, the last consuming request's success; `top`, the latest bucket a request reached
  // (read only by the liveness law's helpful request).
  .maps({Count: int.from(0), Admitted: 0, Refunded: 0})
  .state({blocked: bool.from(false), blockedUntil: 0, ok: bool.from(false), top: 0})
  .flags(({refund, n, blocked, blockedUntil, now}) => ({
    consume: refund.not().and(n.atLeast(1)),
    refunds: refund.and(n.atLeast(1)),
    // single.ts:193-205, cache.ts:14-25: a consuming request is blocked while the cached reset >= now.
    cacheHit: refund.not().and(n.atLeast(1), blocked, now.atMost(blockedUntil)),
    cacheExpired: refund.not().and(n.atLeast(1), blocked, blockedUntil.lt(now)),
  }))
  .flags(env => {
    const r = incrBy(env.Count.at(env.b), env)
    // single.ts:219 success = usedTokensAfterUpdate <= effectiveLimit (the script always increments, :17).
    return {fits: r.atMost(env.tokens)}
  })
  .step(env => {
    const {b, n, window, Count, Admitted, Refunded, blocked, blockedUntil, ok, top, consume, refunds, cacheHit, cacheExpired, fits} = env
    const runs = cacheHit.not()
    return {
      Count: Count.set(b, when(runs, incrBy(Count.at(b), env), Count.at(b))),
      Admitted: Admitted.set(b, when(runs.and(consume, fits), Admitted.at(b).plus(n), Admitted.at(b))),
      Refunded: Refunded.set(b, when(runs.and(refunds), Refunded.at(b).plus(n), Refunded.at(b))),
      // single.ts:222-229: a failure blocks the cache until reset = (bucket + 1) * windowDuration (:221); a successful
      // refund pops it; cache.ts:20-22 isBlocked deletes an expired entry.
      blocked: when(runs.and(fits.not()), yes, when(runs.and(refunds, fits), no, when(cacheExpired, no, blocked))),
      blockedUntil: when(runs.and(fits.not()), b.plus(1).mul(window), blockedUntil),
      ok: when(consume, runs.and(fits), ok),
      top: max(top, b),
    }
  })
// script :17 INCRBY key incrementBy, incrementBy = refund ? -n : n.
const incrBy = (c: Int, {refund, n}: {refund: Cond, n: Term}) => when(refund, c.minus(n), c.plus(n))
const fw = fixedWindow()

// ---------------------------------------------------------------------------------------------------------------------
// slidingWindow(tokens, window): single.ts:293-359, the script slidingWindowLimitScript (single.ts:50-93). Keys
// `identifier:bucket` as in fixedWindow (single.ts:307-310); their TTL (PEXPIRE window * 2 + 1000, script :90) outlives
// every read of them as the current or the previous bucket, so it is not modelled. Refunds (a negative rate) are left
// out (see the gaps): counts are naturals.
export const slidingWindow = () => rule('upstash slidingWindow')
  .params({tokens: nat, window: nat})
  .pre(({window}) => window.atLeast(1))
  // `b`: currentWindow = Math.floor(now / windowSize) (single.ts:307); `pw`: the previous bucket's weighted count,
  // math.floor((1 - (now % window) / window) * requestsInPreviousWindow) (script :77-79), in doubles: the rule allows
  // the exact floor or one less (what the doubles give, see the gap), pinned by `.assume`.
  .inputs({now: nat, n: nat, b: nat, pw: nat})
  .assume(({b, now, window}) => b.mul(window).atMost(now).and(now.lt(b.plus(1).mul(window))))
  .maps({Count: 0, Admitted: 0})
  .state({blocked: bool.from(false), blockedUntil: 0, ok: bool.from(false), top: 0})
  // script :73-79: requestsInPreviousWindow is the key of bucket - 1 (absent for bucket 0: "identifier:-1").
  .assume(({b, now, window, pw, Count}) => {
    const prev = when(b.eq(0), 0, Count.at(b.minus(1))), x = window.minus(now.minus(b.mul(window))).mul(prev)
    return pw.mul(window).atMost(x).and(x.lt(pw.plus(2).mul(window)))
  })
  .flags(({n, blocked, blockedUntil, now, b, pw, tokens, Count}) => ({
    consume: n.atLeast(1),
    // single.ts:314-326, cache.ts:14-25.
    cacheHit: n.atLeast(1).and(blocked, now.atMost(blockedUntil)),
    cacheExpired: n.atLeast(1).and(blocked, blockedUntil.lt(now)),
    // script :82-84: a consuming request is refused before the INCRBY when previous (weighted) + current >= limit.
    full: n.atLeast(1).and(pw.plus(Count.at(b)).atLeast(tokens)),
    // script :86, :92 and single.ts:340: success = limit - (newValue + weighted previous) >= 0.
    fits: Count.at(b).plus(n).plus(pw).atMost(tokens),
  }))
  .flags(({cacheHit, full, fits}) => ({runs: cacheHit.not().and(full.not()), success: cacheHit.not().and(full.not(), fits)}))
  .step(({b, n, window, Count, Admitted, blocked, blockedUntil, ok, top, consume, cacheHit, cacheExpired, runs, success}) => ({
    Count: Count.set(b, when(runs, Count.at(b).plus(n), Count.at(b))),
    Admitted: Admitted.set(b, when(success, Admitted.at(b).plus(n), Admitted.at(b))),
    // single.ts:343-350: a failure (not a cache hit, which returns at :316) blocks the cache until (currentWindow + 1)
    // * windowSize (:341); cache.ts:20-22 deletes an expired entry.
    blocked: when(cacheHit.not().and(success.not()), yes, when(cacheExpired, no, blocked)),
    blockedUntil: when(cacheHit.not().and(success.not()), b.plus(1).mul(window), blockedUntil),
    ok: when(consume, success, ok),
    top: max(top, b),
  }))
const sw = slidingWindow()

// ---------------------------------------------------------------------------------------------------------------------
// tokenBucket(refillRate, interval, maxTokens): single.ts:414-480, the script tokenBucketLimitScript (single.ts:130-186).
export const tokenBucket = () => rule('upstash tokenBucket')
  // single.ts:414-431 refillRate, interval (ms(interval), :432), maxTokens. The script divides by `interval` (:162) and
  // by `refillRate` (:178): both taken positive (a zero refillRate makes :178 an infinite PEXPIRE, a Redis error).
  .params({maxTokens: nat, interval: nat, refillRate: nat})
  .pre(({interval, refillRate}) => interval.atLeast(1).and(refillRate.atLeast(1)))
  // `k`: numRefills, math.floor((now - refilledAt) / interval) (:162); `c`: math.ceil((maxTokens - remaining) /
  // refillRate) (:178); each pinned by an `.assume` below where the script reads it.
  .inputs({now: nat, refund: bool, n: nat, k: nat, c: nat})
  // The hash `key` {refilledAt, tokens} (:148, :180): `exists`, with its TTL (`ttl`, `expiresAt`: PEXPIRE, :183; Redis
  // treats a key past its TTL as absent). `blocked`, `blockedUntil`: the cache's entry (cache.ts:7, identifier -> reset).
  // Ghosts: `refunded`, the total refunded (observed: the refunds sent); `ok`, the last consuming request's `success`.
  .state({exists: bool.from(false), refilledAt: 0, tokens: 0, ttl: bool.from(false), expiresAt: 0,
    blocked: bool.from(false), blockedUntil: 0, refunded: 0, ok: bool.from(false)})
  .flags(({exists, ttl, now, expiresAt, refund, n}) => ({
    // A key whose TTL has passed is gone (Redis expiry).
    live: exists.and(ttl.not().or(now.lt(expiresAt))),
    // single.ts:438 `if (ctx.cache && incrementBy > 0)`; a refund (incrementBy < 0) pops the cache on success (:468-470).
    consume: refund.not().and(n.atLeast(1)),
    refunds: refund.and(n.atLeast(1)),
  }))
  .flags(({consume, blocked, blockedUntil, now}) => ({
    // cache.ts:14-25 isBlocked: blocked while `reset >= now`; an entry with `reset < now` is deleted.
    cacheHit: consume.and(blocked, now.atMost(blockedUntil)),
    cacheExpired: consume.and(blocked, blockedUntil.lt(now)),
  }))
  .flags(env => ({refills: env.now.atLeast(base(env).ra.plus(env.interval))}))
  .assume(env => {
    const {ra} = base(env), {k, now, interval} = env
    return env.refills.implies(k.mul(interval).atMost(now.minus(ra)).and(now.minus(ra).lt(k.plus(1).mul(interval))))
  })
  .assume(env => {
    const {c, refillRate, maxTokens} = env, d = maxTokens.minus(remainingOf(env))
    return d.gt(0).implies(c.mul(refillRate).atLeast(d).and(c.mul(refillRate).lt(d.plus(refillRate))))
  })
  .flags(env => ({
    // :173-175: reject when consuming and the bucket holds fewer than incrementBy; nothing is written.
    rejects: env.consume.and(env.cacheHit.not(), refilled(env).lt(env.n)),
  }))
  .flags(({cacheHit, rejects}) => ({writes: cacheHit.not().and(rejects.not())}))
  .step(env => {
    const {exists, refilledAt, tokens, ttl, expiresAt, blocked, blockedUntil, refunded, now, n, interval, maxTokens, c,
      live, refunds, cacheHit, cacheExpired, rejects, writes} = env
    const remaining = remainingOf(env)
    // :178, :182-183: PEXPIRE only when expireAt > 0, i.e. maxTokens > remaining.
    const expires = writes.and(maxTokens.gt(remaining))
    return {
      // :180 HSET key refilledAt tokens: a write (re)creates the key; a new key has no TTL until PEXPIRE.
      exists: when(writes, yes, exists),
      refilledAt: when(writes, refilledOf(env), refilledAt),
      tokens: when(writes, remaining, tokens),
      ttl: when(expires, yes, when(writes, live.and(ttl), ttl)),
      expiresAt: when(expires, now.plus(c.mul(interval)), expiresAt),
      // single.ts:465-471: a rejection blocks the cache until reset (:174 refilledAt + interval); a successful refund
      // pops the entry; cache.ts:20-22 isBlocked deletes an expired one.
      blocked: when(rejects, yes, when(writes.and(refunds), no, when(cacheExpired, no, blocked))),
      blockedUntil: when(rejects, refilledOf(env).plus(interval), blockedUntil),
      refunded: when(writes.and(refunds), refunded.plus(n), refunded),
      // :465 success = remaining >= 0, of a consuming request: false on a cache hit (:440-448) or a rejection (:174
      // returns -1).
      ok: when(env.consume, cacheHit.or(rejects).not(), env.ok),
    }
  })

// The bucket as the script reads it (:153-159): absent (or expired), it is full and refilled now.
type Base = {live: Cond, refilledAt: Term, tokens: Term, now: Term, maxTokens: Term}
function base({live, refilledAt, tokens, now, maxTokens}: Base) {
  return {ra: when(live, refilledAt, now), tk: when(live, tokens, maxTokens)}
}
// :161-166, refilled: tokens = min(maxTokens, tokens + numRefills * refillRate), refilledAt += numRefills * interval.
type Refill = Base & {refills: Cond, refillRate: Term, interval: Term, k: Term}
function refilled(env: Refill) {
  const {tk} = base(env)
  return when(env.refills, min(env.maxTokens, tk.plus(env.k.mul(env.refillRate))), tk)
}
function refilledOf(env: Refill) {
  const {ra} = base(env)
  return when(env.refills, ra.plus(env.k.mul(env.interval)), ra)
}
// :177 remaining = tokens - incrementBy (a refund adds).
function remainingOf(env: Refill & {refund: Cond, n: Term}) {
  return when(env.refund, refilled(env).plus(env.n), refilled(env).minus(env.n))
}

const tb = tokenBucket()

export const items: RealItem[] = [{
  id: 'rate limit/upstash-ratelimit/fixedWindow',
  domain: 'rate limit',
  source: ts('175-238', 'RegionRatelimit.fixedWindow'),
  also: [lua('1-25', 'fixedWindowLimitScript'), cache],
  summary: 'A Redis counter per identifier and fixed window (floor(now / window)): every request INCRBYs it by its rate and succeeds while the count after is within the limit; failures are cached in memory until the window ends; a negative rate refunds.',
  expressible: 'partial',
  gaps: [
    {gap: 'nonlinear', blocks: 'law', laws: ['a rejected caller is admitted in a later window'], detail: '(bucket + 1) × window and floor(now / window) × window: the helpful request lands in a fresh window only through the floor\'s facts, products of unknowns'},
    {gap: 'external', blocks: 'part', detail: 'dynamicLimits (single.ts:207-210, script :9-15): the limit read from a Redis key; the rule takes `tokens` as a fixed param (the default)'},
    {gap: 'external', blocks: 'part', detail: 'the bucket\'s TTL runs on the Redis server clock and the bucket on the client clock (Date.now(), single.ts:188); with one clock the TTL is never observed (see the mapping comment), with two it may be'},
  ],
  laws: [
    invariant(fw, fw.law('no window admits more than tokens beyond what was refunded in it', ({Admitted, Refunded, tokens}) => forall(k => Admitted.at(k).atMost(tokens.plus(Refunded.at(k))))),
      'safety', 'docs', 'single.ts:172 "@param tokens - How many requests a user can make in each time window"'),
    stepLaw(fw, fw.stepLaw('a rejected request leaves the window\'s remaining tokens spendable',
      ({Count, tokens}, after) => forall(k => after.Count.at(k).eq(Count.at(k)).or(Count.at(k).atLeast(tokens))),
      ({consume, fits}) => consume.and(fits.not())),
    'step', 'docs', 'PR #156 (single.ts:168-172, tokenBucket): "a rejected request still consumes tokens ... The two tokens the caller was entitled to are gone" (the same failure for this algorithm\'s rate)'),
    stepLaw(fw, fw.stepLaw('a request blocked by the cache changes no count',
      ({Count}, after) => forall(k => after.Count.at(k).eq(Count.at(k))),
      ({cacheHit}) => cacheHit),
    'step', 'docs', 'single.ts:192-205 "Only check cache block": a blocked identifier returns before the script runs'),
    leadsTo(fw, fw.leadsTo('a rejected caller is admitted in a later window', {
      from: ({ok, tokens}) => ok.not().and(tokens.atLeast(1)),
      to: ({ok}) => ok,
      helpful: ({top, window}) => ({refund: 0, n: 1, now: top.plus(2).mul(window), b: top.plus(2)}),
    }), 'docs', 'single.ts:167-170 the window resets: "two windows will be filled with requests quickly"'),
  ],
}, {
  id: 'rate limit/upstash-ratelimit/slidingWindow',
  domain: 'rate limit',
  source: ts('293-359', 'RegionRatelimit.slidingWindow'),
  also: [lua('50-93', 'slidingWindowLimitScript'), cache],
  summary: 'Two fixed-window counters per identifier (current and previous); a request is refused when the previous count, weighted by the part of the previous window still inside the sliding window, plus the current count reaches the limit; otherwise the current counter is INCRBYed and the request succeeds if the weighted total after it is within the limit.',
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'script :77-79 math.floor((1 - (now % window) / window) * previous) in doubles is sometimes one below the exact floor((window - now % window) * previous / window) (window 5, now % window 4, previous 5: 0.9999999999999998 floors to 0, not 1; 52396 of 1.2M sampled cases, never above); the rule lets the weighted count be either'},
    {gap: 'scope', blocks: 'part', detail: 'refunds (a negative rate, script :81-82 skips the check): a bucket may go below 0 and the weighted floor of a negative count is not modelled; the rule sends rates >= 0 only'},
    {gap: 'nonlinear', blocks: 'law', laws: ['a rejected caller is admitted two windows later'], detail: 'bucket × window and (window - now % window) × previous: the helpful request lands in an empty pair of windows only through products of unknowns'},
    {gap: 'external', blocks: 'part', detail: 'dynamicLimits (single.ts:328-331, script :59-66): the limit read from a Redis key; `tokens` is a fixed param (the default)'},
  ],
  laws: [
    invariant(sw, sw.law('no window admits more than tokens', ({Admitted, tokens}) => forall(k => Admitted.at(k).atMost(tokens))),
      'safety', 'docs', 'single.ts:295-296 "@param tokens - How many requests a user can make in each time window"'),
    stepLaw(sw, sw.stepLaw('a rejected request leaves the window\'s remaining tokens spendable',
      ({Count, tokens, pw}, after) => forall(k => after.Count.at(k).eq(Count.at(k)).or(Count.at(k).plus(pw).atLeast(tokens))),
      ({consume, success}) => consume.and(success.not())),
    'step', 'docs', 'PR #156 (single.ts:168-172, tokenBucket): "a rejected request still consumes tokens ... The two tokens the caller was entitled to are gone"; this script checks the limit before adding the rate (:82)'),
    stepLaw(sw, sw.stepLaw('a request blocked by the cache changes no count',
      ({Count}, after) => forall(k => after.Count.at(k).eq(Count.at(k))),
      ({cacheHit}) => cacheHit),
    'step', 'docs', 'single.ts:313-326 "Only check cache block": a blocked identifier returns before the script runs'),
    leadsTo(sw, sw.leadsTo('a rejected caller is admitted two windows later', {
      from: ({ok, tokens}) => ok.not().and(tokens.atLeast(1)),
      to: ({ok}) => ok,
      helpful: ({top, window}) => ({n: 1, now: top.plus(2).mul(window), b: top.plus(2), pw: 0}),
    }), 'docs', 'single.ts:278-280 "a weighted score between two windows": two windows on, both counters are empty'),
  ],
}, {
  id: 'rate limit/upstash-ratelimit/tokenBucket',
  domain: 'rate limit',
  source: lua('130-186', 'tokenBucketLimitScript'),
  also: [ts('414-480', 'RegionRatelimit.tokenBucket'), cache, {...src, path: 'src/negative-rate.test.ts', lines: '100-116', export: 'over-refund', language: 'TypeScript'}],
  summary: 'A Redis hash {refilledAt, tokens} per identifier: refilled by refillRate per whole interval up to maxTokens, a request of `rate` tokens admitted only if the bucket holds them; a refund (negative rate) adds tokens back; rejections are cached in memory until the next refill.',
  expressible: 'partial',
  gaps: [
    {gap: 'nonlinear', blocks: 'law', laws: ['a rejected caller is admitted once it waits for a refill'], detail: 'numRefills × refillRate and numRefills × interval (script :163, :165): given a constant rank, the kernel left the products uninterpreted (a model with interval = refillRate = 1 where numRefills × interval = 2 but numRefills × refillRate = 0), so it cannot see that waiting refills at least one token'},
    {gap: 'external', blocks: 'part', detail: 'dynamicLimits (single.ts:453-455, script :140-146): the limit read from a Redis key another call may change; the rule takes maxTokens as a fixed param (the default, dynamicLimits off)'},
    {gap: 'external', blocks: 'part', detail: 'the key TTL (PEXPIRE, script :183) runs on the Redis server clock, the refill on the client clock (Date.now(), single.ts:435); the rule reads one clock for both'},
  ],
  laws: [
    stepLaw(tb, tb.stepLaw('a rejected request leaves the bucket unchanged',
      ({tokens, refilledAt, exists, ttl, expiresAt}, after) => after.tokens.eq(tokens).and(after.refilledAt.eq(refilledAt), same(after.exists, exists), same(after.ttl, ttl), after.expiresAt.eq(expiresAt)),
      ({writes}) => writes.not()),
    'step', 'docs', 'single.ts:168-172 "a rejected request consumed tokens and a single large rate could lock the identifier out" (the bug fixed in #156)'),
    // Tokens are naturals here (truncated minus), so "tokens never go negative" says nothing: the claim is that the
    // write at :177/:180 never truncates, i.e. remaining + incrementBy is the refilled count.
    stepLaw(tb, tb.stepLaw('an admitted request takes no more tokens than the bucket holds',
      (env, after) => after.tokens.plus(env.n).eq(refilled(env)),
      ({writes, consume}) => writes.and(consume)),
    'step', 'docs', 'single.ts:404-405 "if there is no token to take, the request is rejected"; PR #156 "with 2 tokens left a rate: 5 request set tokens to -3"'),
    stepLaw(tb, tb.stepLaw('only a refund lifts the tokens past maxTokens',
      ({tokens, maxTokens}, after) => after.tokens.atMost(max(maxTokens, tokens)),
      ({refund}) => refund.not()),
    'step', 'docs', 'single.ts:426 "Maximum number of tokens"; script :163 `math.min(effectiveLimit, tokens + numRefills * refillRate)`'),
    invariant(tb, tb.law('tokens never exceed maxTokens plus what was refunded', ({tokens, maxTokens, refunded}) => tokens.atMost(maxTokens.plus(refunded))),
      'safety', 'tests', 'single.ts:426 "Maximum number of tokens"; negative-rate.test.ts:115 an over-refund may pass the limit (toBeGreaterThan(limit))'),
    leadsTo(tb, tb.leadsTo('a rejected caller is admitted once it waits for a refill', {
      from: ({ok, maxTokens}) => ok.not().and(maxTokens.atLeast(1)),
      to: ({ok}) => ok,
      helpful: ({refilledAt, blockedUntil, interval}) => ({refund: 0, n: 1, now: refilledAt.plus(interval.mul(blockedUntil.plus(1))), k: blockedUntil.plus(1)}),
    }), 'docs', 'single.ts:402-403 "a bucket filled with {maxTokens} tokens that refills constantly at {refillRate} per {interval}"'),
  ],
}]
