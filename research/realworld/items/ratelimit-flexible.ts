// rate-limiter-flexible v11.2.3, RateLimiterMemory over its MemoryStorage. ISC, (c) Roman Voloboev (animir).
// https://github.com/animir/node-rate-limiter-flexible/tree/d19a457455338b73172d47d004f402bd0b748152/lib
//
// A record per key {value, expiresAt}: `consume` adds the points to it (MemoryStorage.incrby) and refuses the call when
// the value passes `points`, blocking the key for blockDuration the first time; an expired record starts again at the
// points of the call; `penalty`, `reward`, `block`, `set`, `delete` change a record directly.
//
// Mapping:
// - `now: nat` (ms) is sent in with each call (Date.now(), MemoryStorage.js:17, :41); Date.now() never goes back
//   (`clock`, `.assume`). Durations are seconds and become ms by × 1000 (MemoryStorage.js:32), a constant.
// - A record's timer (MemoryStorage.js:45-51, `setTimeout(delete, durationMs)`) deletes it at expiresAt; incrby already
//   treats a record with `msBeforeExpires <= 0` as gone (:16-28), so a record is live while it exists and has no expiry
//   or now < expiresAt, which is what both the timer and incrby give. `Exp[k] = 0` is expiresAt null (no expiry).
// - Values are integers: `reward` adds -points and may take a value below 0 (RateLimiterMemory.js:58-66).
// - Ghosts: per record (reset when a record is made by `set`), `Admitted[k]` the points of consumes let through,
//   `Rewarded[k]` the points rewarded, `Start[k]` the value the record was made with by block/set/a block on refusal
//   (0 when a call's incrby made it, that call's own points being counted as consumed); `okD` whether the last consume
//   of key `d` (a param: the key a liveness law watches) was let through.
// - execEvenly (RateLimiterMemory.js:32-41) only delays the resolve; the decision and the record are the same, and the
//   delay is not modelled.
import {type Cond, type Term, Int, bool, forall, int, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'animir/node-rate-limiter-flexible', commit: 'd19a457455338b73172d47d004f402bd0b748152', licence: 'ISC', author: 'Roman Voloboev (animir)', language: 'JavaScript'}

export const rateLimiterMemory = () => rule('rate-limiter-flexible RateLimiterMemory')
  // RateLimiterAbstract.js:5-9: points, duration (s, 0 = never expires), blockDuration (s, 0 = no block). points may be
  // negative there; here it is a natural.
  .params({points: nat, duration: nat, blockDuration: nat, d: nat})
  // One call: which method, the key, its points, its seconds (block/set's secDuration, consume's
  // options.customDuration when `custom`: RateLimiterAbstract.js:100-104).
  .inputs({op: oneOf('consume', 'penalty', 'reward', 'block', 'set', 'delete'), key: nat, pts: nat, secs: nat, custom: bool, now: nat})
  .maps({Has: 0, Val: int.from(0), Exp: 0, Start: int.from(0), Admitted: 0, Rewarded: 0})
  .state({clock: 0, okD: bool.from(false)})
  .assume(({now, clock}) => now.atLeast(clock))
  .flags(({op, key, now, Has, Exp}) => ({
    // MemoryStorage.js:15-19: a record is changed in place while it has no expiry or msBeforeExpires > 0.
    live: Has.at(key).eq(1).and(Exp.at(key).eq(0).or(now.lt(Exp.at(key)))),
    incr: op.is('consume').or(op.is('penalty'), op.is('reward')),
  }))
  .flags(({op, key, pts, live, incr, Val, points, blockDuration}) => {
    const v = after(op.is('reward'), pts, live, Val.at(key))
    return {
      // RateLimiterMemory.js:25 refused when consumedPoints > points.
      refused: op.is('consume').and(v.gt(points)),
      // :27-30 "Block only first time when consumed more than points".
      blocks: op.is('consume').and(v.gt(points), blockDuration.gt(0), v.atMost(points.plus(pts))),
      // An incrby that makes a new record (MemoryStorage.js:26, :28): ghosts start again.
      fresh: incr.and(live.not()),
    }
  })
  .step(({op, key, pts, secs, custom, now, duration, blockDuration, points, d, Has, Val, Exp, Start, Admitted, Rewarded, okD, live, incr, refused, blocks, fresh}) => {
    const v = after(op.is('reward'), pts, live, Val.at(key))
    // MemoryStorage.js:31-43 set(key, value, durationSec): expiresAt now + durationSec * 1000, or null when that is 0.
    const expiry = (secsOf: typeof secs) => when(secsOf.gt(0), now.plus(secsOf.times(1000)), 0)
    // RateLimiterAbstract.js:100-104 _getKeySecDuration: options.customDuration when given, else duration.
    const dur = when(custom, secs, duration)
    // block (RateLimiterMemory.js:74-82): set(key, points + 1, secDuration); set (:84-91): set(key, points, secDuration).
    const sets = op.is('block').or(op.is('set')), made = sets.or(blocks)
    const startV = when(op.is('block'), Int.of(points.plus(1)), when(op.is('set'), Int.of(pts), v))
    return {
      Has: Has.set(key, when(op.is('delete'), 0, when(incr.or(sets), 1, Has.at(key)))),
      Val: Val.set(key, when(made, startV, when(incr, v, Val.at(key)))),
      Exp: Exp.set(key, when(blocks, expiry(blockDuration), when(sets, expiry(secs), when(fresh, expiry(dur), Exp.at(key))))),
      Start: Start.set(key, when(made, startV, when(fresh, Int.of(0), Start.at(key)))),
      Admitted: Admitted.set(key, when(made.or(fresh), 0, Admitted.at(key)).plus(when(op.is('consume').and(refused.not()), pts, 0))),
      Rewarded: Rewarded.set(key, when(made.or(fresh), 0, Rewarded.at(key)).plus(when(op.is('reward'), pts, 0))),
      clock: now,
      okD: when(op.is('consume').and(key.eq(d)), refused.not(), okD),
    }
  })

// MemoryStorage.incrby (:13-29): the record's value plus the call's points (reward: -points, RateLimiterMemory.js:62),
// or the call's points alone when no live record holds the key.
function after(reward: Cond, pts: Term, live: Cond, val: Int): Int {
  return when(live, val, Int.of(0)).plus(when(reward, Int.of(0).minus(pts), Int.of(pts)))
}

const r = rateLimiterMemory()
const cite = (path: string, lines: string, exp: string) => ({...src, path, lines, export: exp})

export const items: RealItem[] = [{
  id: 'rate limit/rate-limiter-flexible/RateLimiterMemory',
  domain: 'rate limit',
  source: cite('lib/RateLimiterMemory.js', '18-104', 'RateLimiterMemory'),
  also: [cite('lib/component/MemoryStorage/MemoryStorage.js', '13-88', 'MemoryStorage'), cite('lib/RateLimiterAbstract.js', '1-47, 100-104', 'RateLimiterAbstract')],
  summary: 'A fixed window per key from its first call: consume adds points and is refused once the window passes `points`, blocking the key for blockDuration the first time; penalty, reward, block, set and delete change a key directly.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'execEvenly (RateLimiterMemory.js:32-41) resolves a let-through consume after a setTimeout delay; the decision and the record are the same, the delay is not modelled'},
    {gap: 'other', blocks: 'part', detail: 'points may be negative and durations fractional (RateLimiterAbstract.js:5-6, "must be a finite number"); the rule takes naturals, durations in whole seconds'},
  ],
  laws: [
    // Stated first as "no record lets through more than points beyond its start value and its rewards" (start +
    // admitted <= points + rewarded): refuted by `set(key, 2)` with points 0, a record made above the limit with
    // nothing let through (a law error: the start value may pass the limit; repro/rlf-set-start.ts).
    invariant(r, r.law('a record lets through nothing, or no more than points beyond its start value and its rewards', ({Admitted, Start, Rewarded, points}) => forall(k => Admitted.at(k).eq(0).or(Start.at(k).plus(Admitted.at(k)).atMost(Int.of(points).plus(Rewarded.at(k)))))),
      'safety', 'docs', 'RateLimiterAbstract.js:5-6 "points: Number of points" per duration; README:206 reward "Decrease number of consumed points in current duration"'),
    stepLaw(r, r.stepLaw('a key over its points refuses every consume until its record expires',
      (_, after) => after.okD.not(),
      ({op, key, d, Has, Val, Exp, now, points}) => op.is('consume').and(key.eq(d), Has.at(key).eq(1), Val.at(key).gt(points), Exp.at(key).eq(0).or(now.lt(Exp.at(key))))),
    'step', 'docs', 'README:183 blockDuration "Block for N seconds, if consumed more than points"; RateLimiterAbstract.js:7'),
    stepLaw(r, r.stepLaw('a refused consume with blockDuration blocks the key for blockDuration the first time',
      ({key, now, blockDuration}, after) => after.Exp.at(key).eq(now.plus(blockDuration.times(1000))),
      ({blocks}) => blocks),
    'step', 'docs', 'RateLimiterMemory.js:26 "Block only first time when consumed more than points"'),
    leadsTo(r, r.leadsTo('a refused key is let through once its record expires, unless it never expires', {
      from: ({okD, points}) => okD.not().and(points.atLeast(1)),
      to: ({okD, Has, Exp, d}) => okD.or(Has.at(d).eq(1).and(Exp.at(d).eq(0))),
      helpful: ({d, clock, Exp}) => ({op: 0, key: d, pts: 1, custom: 0, now: clock.plus(Exp.at(d))}),
    }), 'docs', 'RateLimiterAbstract.js:6 "duration: Per seconds (... 0 = never expires)"'),
  ],
}]
