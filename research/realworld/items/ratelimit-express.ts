// express-rate-limit v8.7.1, the default MemoryStore with the middleware's decision around it. MIT, (c) Nathan Friedly
// and contributors. https://github.com/express-rate-limit/express-rate-limit/tree/c2e30b340189e287123cf5bfd89526dd2ea07d3f/source
//
// A fixed window per client that starts at the client's first hit: `increment` (memory-store.ts:102-112) resets the
// count once the client's resetTime has passed, then adds one; the middleware (rate-limit.ts:426-618) refuses the
// request when the count is above `limit` (:602). With skipFailedRequests / skipSuccessfulRequests a finished request
// is taken back by `decrement` (:537-556), unless its reset time has passed. A timer every windowMs moves `current` to
// `previous` and drops the old `previous` (:71-74, :214-218).
//
// Mapping:
// - Clients by key (a number here; the key generator, :423, is the caller's business). `Where[k]`: 0 not stored, 1 in
//   `previous`, 2 in `current`; `Hits[k]`, `Reset[k]`: the Client's totalHits and resetTime (ms).
// - `now: nat` is sent in with each request (Date.now(), memory-store.ts:105, :172, rate-limit.ts:545), measured from
//   the store's init (when the interval starts, :72); Date.now() never goes back in one process (`.assume`, `clock`).
// - The timer is a request (`tick`) the environment sends at most once per windowMs (setInterval never fires early):
//   `lastTick` (ghost) is when it last fired.
// - A decrement is for one earlier hit (rate-limit.ts:540-544, once per request). The middleware checks the reset time
//   of the object `increment` returned (:545, `resetTime.getTime()`): the Client's own Date, which resetClient changes
//   in place (memory-store.ts:174). So the check reads the client's current Reset whether the hit was in this window or
//   an earlier one, as long as the Client object is the same (not dropped by the timer or resetKey; a dropped Client's
//   Date is no longer updated, is past by then, and its decrement does nothing, which a request of another op already
//   is). `earlier` says which: the request's hit was before the client's last reset. Ghosts `Pend` / `Old` count the
//   hits of this window / of earlier windows of the same Client not yet taken back (the `.assume` only lets a hit be
//   taken back once).
// - Ghosts: `Admitted[k]`, the hits of k's current window let through (`next()`, :618); `Own[k]`, this window's hits
//   taken back by a decrement; `okD`: whether the last hit by client `d` (a param, the client a liveness law watches)
//   was let through.
// - `limit` is a number here (it may be a function of the request, :455-457); `skips`: skipFailedRequests or
//   skipSuccessfulRequests is set (no decrement otherwise).
import {bool, forall, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'express-rate-limit/express-rate-limit', commit: 'c2e30b340189e287123cf5bfd89526dd2ea07d3f', licence: 'MIT', author: 'Nathan Friedly and contributors', language: 'TypeScript'}

export const memoryStore = () => rule('express-rate-limit MemoryStore')
  .params({limit: nat, windowMs: nat, skips: bool, d: nat})
  // validations.windowMs (memory-store.ts:65): a positive window.
  .pre(({windowMs}) => windowMs.atLeast(1))
  .inputs({op: oneOf('hit', 'decrement', 'tick', 'resetKey'), key: nat, now: nat, earlier: bool})
  .maps({Where: 0, Hits: 0, Reset: 0, Admitted: 0, Own: 0, Pend: 0, Old: 0})
  .state({clock: 0, lastTick: 0, okD: bool.from(false)})
  .assume(({now, clock}) => now.atLeast(clock))
  // setInterval(clearExpired, windowMs) (memory-store.ts:72-74): not earlier than windowMs after the last.
  .assume(({op, now, lastTick, windowMs}) => op.is('tick').implies(now.atLeast(lastTick.plus(windowMs))))
  // A decrement takes back one hit not yet taken back (rate-limit.ts:541-553 `decremented`).
  .assume(({op, earlier, key, Pend, Old}) => op.is('decrement').implies(when(earlier, Old.at(key), Pend.at(key)).atLeast(1)))
  .flags(({op, key, now, Where, Reset, skips}) => ({
    hit: op.is('hit'),
    // getClient (memory-store.ts:187-207): a stored client, or a new one with resetTime now + windowMs (:200-201).
    fresh: op.is('hit').and(Where.at(key).eq(0)),
    // :106-108: an expired client is reset (count 0, resetTime now + windowMs).
    expired: op.is('hit').and(Where.at(key).gt(0), Reset.at(key).atMost(now)),
    // rate-limit.ts:545-552: no decrement once the reset time has passed; memory-store.ts:121-125.
    dec: op.is('decrement').and(skips, Where.at(key).gt(0), now.lt(Reset.at(key))),
  }))
  .flags(({fresh, expired}) => ({restarts: fresh.or(expired)}))
  .flags(({hit, restarts, key, Hits, limit}) => ({
    // memory-store.ts:110 totalHits++; rate-limit.ts:602 refused when totalHits > limit.
    passes: hit.and(when(restarts, 0, Hits.at(key)).plus(1).atMost(limit)),
  }))
  .step(({op, key, now, earlier, windowMs, skips, d, Where, Hits, Reset, Admitted, Own, Pend, Old, lastTick, okD, hit, restarts, dec, passes}) => {
    const hits = when(restarts, 0, Hits.at(key)), tick = op.is('tick'), drop = op.is('resetKey')
    return {
      // getClient moves the client to `current` (:190-205); clearExpired shifts every client one map down (:216-217);
      // resetKey deletes it from both (:134-137).
      Where: Where.each(k => when(tick, Where.at(k).minus(1), when(k.eq(key).and(hit.or(dec)), 2, when(k.eq(key).and(drop), 0, Where.at(k))))),
      Hits: Hits.set(key, when(hit, hits.plus(1), when(dec, Hits.at(key).minus(1), Hits.at(key)))),
      Reset: Reset.set(key, when(restarts, now.plus(windowMs), Reset.at(key))),
      Admitted: Admitted.set(key, when(passes, when(restarts, 0, Admitted.at(key)).plus(1), when(restarts, 0, Admitted.at(key)))),
      Own: Own.set(key, when(restarts, 0, when(dec.and(earlier.not()), Own.at(key).plus(1), Own.at(key)))),
      // The hits a decrement may still take back: a hit adds one (with skips); a restart makes this window's earlier;
      // a dropped Client (timer, resetKey) can no longer be taken back.
      Pend: Pend.each(k => when(tick.and(Where.at(k).eq(1)).or(drop.and(k.eq(key))), 0,
        when(k.eq(key).and(hit), when(restarts, 0, Pend.at(k)).plus(when(skips, 1, 0)),
          when(k.eq(key).and(op.is('decrement'), earlier.not()), Pend.at(k).minus(1), Pend.at(k))))),
      Old: Old.each(k => when(tick.and(Where.at(k).eq(1)).or(drop.and(k.eq(key))).or(k.eq(key).and(hit, Where.at(k).eq(0))), 0,
        when(k.eq(key).and(restarts), Old.at(k).plus(Pend.at(k)),
          when(k.eq(key).and(op.is('decrement'), earlier), Old.at(k).minus(1), Old.at(k))))),
      clock: now,
      lastTick: when(tick, now, lastTick),
      okD: when(hit.and(key.eq(d)), passes, okD),
    }
  })

const r = memoryStore()
const cite = (path: string, lines: string, exp: string) => ({...src, path, lines, export: exp})

export const items: RealItem[] = [{
  id: 'rate limit/express-rate-limit/MemoryStore',
  domain: 'rate limit',
  source: cite('source/memory-store.ts', '102-218', 'MemoryStore'),
  also: [cite('source/rate-limit.ts', '426-618', 'rateLimit (the middleware)')],
  summary: 'A per-client fixed window starting at the first hit: each hit resets an expired client and counts one; a hit over `limit` is refused; with skip options a finished request is taken back unless its reset time has passed; a timer drops clients idle for a window.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'the setInterval timer (memory-store.ts:72-74) and the response events that trigger a decrement (rate-limit.ts:558-598) are requests the environment sends: the timer at most once per windowMs, a decrement once per earlier hit'},
    {gap: 'other', blocks: 'part', detail: '`limit` may be a function of the request (rate-limit.ts:455-457); the rule takes it as a fixed param'},
  ],
  laws: [
    invariant(r, r.law('no client window lets through more than limit hits beyond its own hits taken back', ({Admitted, Own, limit}) => forall(k => Admitted.at(k).atMost(limit.plus(Own.at(k))))),
      'safety', 'docs', 'types.ts:268 limit "The maximum number of connections to allow during the `window` before rate limiting the client"; skipped requests are not counted'),
    stepLaw(r, r.stepLaw('a decrement never lowers a count the store has reset',
      ({Hits}, after) => forall(k => after.Hits.at(k).eq(Hits.at(k))),
      ({op, earlier}) => op.is('decrement').and(earlier)),
    'step', 'docs', 'rate-limit.ts:545-546 "Don\'t decrement if the reset time has already passed, as the store will have already reset the count for this key."'),
    stepLaw(r, r.stepLaw('the timer drops only clients whose window has passed',
      ({Where, Reset, now}) => forall(k => Where.at(k).eq(1).implies(Reset.at(k).atMost(now))),
      ({op}) => op.is('tick')),
    'step', 'docs', 'memory-store.ts:34-37 "Once windowMs has elapsed, all clients left in previous ... are known to be expired and can be deleted in bulk."'),
    leadsTo(r, r.leadsTo('a refused client is let through once its window has passed', {
      from: ({okD, limit}) => okD.not().and(limit.atLeast(1)),
      to: ({okD}) => okD,
      helpful: ({d, clock, Reset}) => ({op: 0, key: d, now: clock.plus(Reset.at(d))}),
    }), 'docs', 'memory-store.ts:8-9 "how many times they have hit the endpoint, and when their hit count resets"'),
  ],
}]
