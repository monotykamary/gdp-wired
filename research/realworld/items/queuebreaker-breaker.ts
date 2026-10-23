// Circuit breakers from four libraries, each written as the rule its code runs, with the laws a reviewer would ask
// about. Group `queuebreaker`; the sources are in sources/queuebreaker.json.
//
//   - sony/gobreaker v2.4.0 (MIT, (c) 2015 Sony Corporation, Go):
//     https://github.com/sony/gobreaker/tree/0ae90251b774f890e7586c96ea82d61eb74d556d/v2
//   - connor4312/cockatiel v3.2.1 (MIT, (c) 2019 Connor Peet, TypeScript):
//     https://github.com/connor4312/cockatiel/tree/32a70686ef3470f6c94c1325fbc7982d582b8432/src
//   - nodeshift/opossum v10.0.0 (Apache-2.0, Red Hat, Inc., JavaScript):
//     https://github.com/nodeshift/opossum/tree/6c00a87a021daae4639408e1645abb69a530a841/lib
//   - App-vNext/Polly 7.2.4 (BSD-3-Clause, (c) 2015-2020 App vNext, C#):
//     https://github.com/App-vNext/Polly/tree/b1a5a17de8ef5d0bc86e5a4502ad30891e674379/src/Polly/CircuitBreaker
//
// Every library reads a clock inside the call (time.Now(), Date.now(), SystemClock.UtcNow()); here the time is sent in
// with each request as `now`, and requests come in time order (`now` at least the last one's). A call that throws or
// returns early without changing state is a request where every part keeps its value. A protected call is two
// requests, its admission and its outcome, so calls in flight interleave as they do in the code (each library holds a
// lock or runs on one thread for each half, so each half is atomic).
import {type Choice, type Term, bool, count, max, nat, no, oneOf, rule, same, when, yes} from '../../../core/dsl.ts'
import {type RealItem, type Source, invariant, leadsTo, stepLaw} from '../lib.ts'

// ---------------------------------------------------------------------------------------------------------------
// sony/gobreaker v2: CircuitBreaker[T] with the fixed-window counts (Settings.BucketPeriod <= 0, one bucket) and the
// default ReadyToTrip.
const gob = {repo: 'sony/gobreaker', commit: '0ae90251b774f890e7586c96ea82d61eb74d556d', licence: 'MIT', author: 'Sony Corporation', language: 'Go'}

// The lazy transitions currentState(now) makes before every call (gobreaker.go:304-318), shared by the flags and the
// step: a closed window past its expiry starts a new generation (toNewGeneration, :348-366); an open breaker past its
// expiry goes half-open (setState, :333-346, which starts a new generation too).
type GobEnv = {st: Choice<'closed' | 'halfOpen' | 'open'>, expiry: Term, now: Term, generation: Term, requests: Term, successes: Term, failures: Term, exclusions: Term, consecSucc: Term, consecFail: Term, interval: Term}
const gobLazy = (e: GobEnv) => {
  // :307 `!cb.expiry.IsZero() && cb.expiry.Before(now)` (expiry 0 is Go's zero time; every real time is >= 1).
  const closedRolls = e.st.is('closed').and(e.expiry.gt(0), e.expiry.lt(e.now))
  // :313 `cb.expiry.Before(now)`.
  const opens = e.st.is('open').and(e.expiry.lt(e.now))
  const fresh = closedRolls.or(opens)
  const z = (t: Term) => when(fresh, 0, t)
  return {
    closedRolls, opens, fresh,
    halfOpen1: e.st.is('halfOpen').or(opens), open1: e.st.is('open').and(opens.not()), closed1: e.st.is('closed'),
    // :349 `cb.generation++`; :351 `cb.counts.clear()` (counter.go:43-50, :117-125).
    gen1: when(fresh, e.generation.plus(1), e.generation),
    requests1: z(e.requests), successes1: z(e.successes), failures1: z(e.failures), exclusions1: z(e.exclusions),
    consecSucc1: z(e.consecSucc), consecFail1: z(e.consecFail),
    // :355-359 closed: `cb.interval == 0` gives the zero time, else now + interval; :363-364 half-open: zero.
    expiry1: when(closedRolls, when(e.interval.eq(0), 0, e.now.plus(e.interval)), when(opens, 0, e.expiry)),
  }
}

export const gobreaker = () => rule('gobreaker CircuitBreaker')
  // Settings (gobreaker.go:83-93) after NewCircuitBreaker's defaults (:116-172): MaxRequests 0 means 1 (:122-126),
  // Timeout <= 0 means 60 s (:145-149), so both are at least 1 here; Interval <= 0 is 0 (:129-132, :174). `t0`: the
  // time.Now() of the constructor's toNewGeneration (:169), in the clock's unit (any: only order and sums are read).
  .params({maxRequests: nat, interval: nat, timeout: nat, t0: nat})
  .pre(({maxRequests, timeout, t0}) => maxRequests.atLeast(1).and(timeout.atLeast(1), t0.atLeast(1)))
  // One request: beforeRequest (:237-252), afterRequest (:254-274) with the generation its beforeRequest returned and
  // whether the request's error was excluded or successful (IsExcluded, IsSuccessful: any user predicate, so any
  // result), or State() (:195-202), which runs currentState alone.
  .inputs({op: oneOf('before', 'after', 'state'), gen: nat, result: oneOf('success', 'failure', 'excluded'), now: nat})
  // :108-112 state, generation, counts (counter.go:7-14, one bucket: the rollingCounts' totals are its one bucket's),
  // expiry (0: the zero time). :169 the constructor's toNewGeneration: generation 1, expiry t0 + interval or zero.
  .state({
    st: oneOf('closed', 'halfOpen', 'open').from('closed'), generation: 1,
    requests: 0, successes: 0, failures: 0, exclusions: 0, consecSucc: 0, consecFail: 0,
    expiry: ({interval, t0}) => when(interval.eq(0), 0, t0.plus(interval)), last: ({t0}) => t0,
  })
  // The clock only moves forward (Go's monotonic clock); an afterRequest whose generation is the current one (after the
  // lazy transitions) answers a request beforeRequest admitted in it that has not been answered yet: Execute pairs
  // them (:217-235), so a generation's answers never outnumber its admissions.
  .assume(e => {
    const l = gobLazy(e)
    return e.now.atLeast(e.last).and(e.op.is('after').and(e.gen.eq(l.gen1)).implies(l.requests1.gt(l.successes1.plus(l.failures1).plus(l.exclusions1))))
  })
  .flags(e => {
    const l = gobLazy(e), {op, gen, result, maxRequests} = e
    // :244-248 open: ErrOpenState; half-open with `validRequests() >= maxRequests`: ErrTooManyRequests
    // (counter.go:36-41: requests - exclusions, 0 below).
    const admitted = op.is('before').and(l.open1.not(), l.halfOpen1.and(l.requests1.minus(l.exclusions1).atLeast(maxRequests)).not())
    // :260-262 `generation != previous`: ignored.
    const answers = op.is('after').and(gen.eq(l.gen1))
    const excluded = answers.and(result.is('excluded')), succeeded = answers.and(result.is('success')), failed = answers.and(result.is('failure'))
    // :276-286: a success counts in closed and half-open; in half-open, ConsecutiveSuccesses >= maxRequests closes.
    const counted = succeeded.and(l.closed1.or(l.halfOpen1))
    const closes = succeeded.and(l.halfOpen1, l.consecSucc1.plus(1).atLeast(maxRequests))
    // :288-298: a failure counts in closed and trips by ReadyToTrip (the default, :177-179: ConsecutiveFailures > 5);
    // in half-open it opens at once.
    const failCounted = failed.and(l.closed1)
    const trips = failCounted.and(l.consecFail1.plus(1).gt(5)).or(failed.and(l.halfOpen1))
    return {admitted, answers, excluded, succeeded, failed, counted, closes, failCounted, trips}
  })
  .step(e => {
    const l = gobLazy(e), {now, interval, timeout, admitted, excluded, counted, closes, failCounted, trips} = e
    // setState (:333-346) to closed or open: a new generation, the counts cleared, the expiry of the new state (:348-366).
    const moves = closes.or(trips)
    const keep = (t: Term) => when(moves, 0, t)
    return {
      st: when(closes, 'closed', when(trips, 'open', when(l.halfOpen1, 'halfOpen', e.st))),
      generation: when(moves, l.gen1.plus(1), l.gen1),
      // counter.go:16-34 onRequest, onSuccess, onFailure, onExclusion.
      requests: keep(when(admitted, l.requests1.plus(1), l.requests1)),
      successes: keep(when(counted, l.successes1.plus(1), l.successes1)),
      failures: keep(when(failCounted, l.failures1.plus(1), l.failures1)),
      exclusions: keep(when(excluded, l.exclusions1.plus(1), l.exclusions1)),
      consecSucc: keep(when(counted, l.consecSucc1.plus(1), when(failCounted, 0, l.consecSucc1))),
      consecFail: keep(when(failCounted, l.consecFail1.plus(1), when(counted, 0, l.consecFail1))),
      expiry: when(closes, when(interval.eq(0), 0, now.plus(interval)), when(trips, now.plus(timeout), l.expiry1)),
      last: now,
    }
  })

// ---------------------------------------------------------------------------------------------------------------
// cockatiel v3: CircuitBreakerPolicy with a ConsecutiveBreaker and a constant halfOpenAfter.
const cock = {repo: 'connor4312/cockatiel', commit: '32a70686ef3470f6c94c1325fbc7982d582b8432', licence: 'MIT', author: 'Connor Peet', language: 'TypeScript'}

export const cockatiel = () => rule('cockatiel CircuitBreakerPolicy')
  // ConsecutiveBreaker(threshold) (ConsecutiveBreaker.ts:13); `halfOpenAfter` as a number, a ConstantBackoff
  // (CircuitBreakerPolicy.ts:148-151) whose duration is that number at every attempt.
  .params({threshold: nat, halfOpenAfter: nat})
  // One request: execute() entered (:218-265); the outcome of a call admitted while Closed (:225-235) or of the
  // half-open test (:295-319): 'ok' a success, 'handled' a failure the policy handles, 'unhandled' an error it doesn't
  // (executor.invoke throws it: in Closed nothing is counted, in the test it closes, :313-318); isolate() (:184-192);
  // a handle's dispose() (:195-206).
  .inputs({op: oneOf('execute', 'closedDone', 'testDone', 'isolate', 'dispose'), outcome: oneOf('ok', 'handled', 'unhandled'), now: nat})
  // :67-81 innerState: its value, `openedAt`, `attemptNo`, the isolation `counters`; ConsecutiveBreaker.ts:7 `state`
  // (the consecutive failures). Ghost: `inClosed`, calls admitted while Closed and not answered (each holds its own
  // `state` captured at :222); `tests`, half-open tests in flight (the promise at :249; nothing in the code stops a
  // second from starting once a stale failure has reopened the circuit, so they are counted).
  .state({
    st: oneOf('Closed', 'Open', 'HalfOpen', 'Isolated').from('Closed'), openedAt: 0, attemptNo: 0, counters: 0, failures: 0,
    inClosed: 0, tests: 0, last: 0,
  })
  // Date.now() only moves forward; an outcome answers a call in flight (Closed calls, or the one test).
  .assume(({now, last, op, inClosed, tests}) => now.atLeast(last).and(op.is('closedDone').implies(inClosed.gt(0)), op.is('testDone').implies(tests.gt(0))))
  .flags(({op, outcome, st, now, openedAt, halfOpenAfter, threshold, failures, counters}) => {
    // :224-225 Closed: the call runs.
    const runs = op.is('execute').and(st.is('Closed'))
    // :245-257 Open: `Date.now() - state.openedAt < state.backoff.duration` throws; else the call is the half-open test.
    const starts = op.is('execute').and(st.is('Open'), now.atLeast(openedAt.plus(halfOpenAfter)))
    // :226-233 a Closed call's result: success resets the breaker (ConsecutiveBreaker.ts:18-20), a handled failure
    // counts (:25-27 `++this.state >= this.threshold`) and opens when it reaches the threshold.
    const closedOk = op.is('closedDone').and(outcome.is('ok')), closedFail = op.is('closedDone').and(outcome.is('handled'))
    // :303-310 the test: success counts (resets) and closes; a handled failure counts and opens; :313-318 an unhandled
    // error closes.
    const testOk = op.is('testDone').and(outcome.is('ok')), testFail = op.is('testDone').and(outcome.is('handled')), testErr = op.is('testDone').and(outcome.is('unhandled'))
    // open() (:321-337): nothing when Isolated or Open; else Open from now, attemptNo the half-open one's or 1.
    const openable = st.is('Isolated').not().and(st.is('Open').not())
    const opens = openable.and(closedFail.and(failures.plus(1).atLeast(threshold)).or(testFail))
    // close() (:339-345): only from HalfOpen.
    const closes = st.is('HalfOpen').and(testOk.or(testErr))
    // :185-191 isolate: a new Isolated state with counters 0, then counters + 1. :201 dispose: `!--counters` closes.
    const isolates = op.is('isolate')
    const disposes = op.is('dispose').and(st.is('Isolated'), counters.gt(0))
    return {runs, starts, closedOk, closedFail, testOk, testFail, testErr, opens, closes, isolates, disposes}
  })
  .step(({op, now, st, openedAt, attemptNo, counters, failures, inClosed, tests, runs, starts, closedOk, closedFail, testOk, testFail, opens, closes, isolates, disposes}) => {
    const reopensFromHalf = opens.and(st.is('HalfOpen'))
    const freed = disposes.and(counters.eq(1))
    return {
      st: when(isolates, 'Isolated', when(freed, 'Closed', when(opens, 'Open', when(closes, 'Closed', when(starts, 'HalfOpen', st))))),
      openedAt: when(opens, now, openedAt),
      // :254 the half-open state's attemptNo is the open one's + 1; :326-327 open() keeps it from HalfOpen, else 1.
      attemptNo: when(opens, when(reopensFromHalf, attemptNo, 1), when(starts, attemptNo.plus(1), attemptNo)),
      counters: when(isolates, when(st.is('Isolated'), counters.plus(1), 1), when(disposes, counters.minus(1), counters)),
      // ConsecutiveBreaker.ts:18-27: success() sets 0, failure() adds one (the test's too, :304, :308).
      failures: when(closedOk.or(testOk), 0, when(closedFail.or(testFail), failures.plus(1), failures)),
      inClosed: when(runs, inClosed.plus(1), when(op.is('closedDone'), inClosed.minus(1), inClosed)),
      tests: when(starts, tests.plus(1), when(op.is('testDone'), tests.minus(1), tests)),
      last: now,
    }
  })

// ---------------------------------------------------------------------------------------------------------------
// nodeshift/opossum v10: CircuitBreaker with its rolling Status window, errorThresholdPercentage, volumeThreshold,
// allowWarmUp, resetTimeout, and state restored from toJSON() (README "Breaker State Initialization").
const opo = {repo: 'nodeshift/opossum', commit: '6c00a87a021daae4639408e1645abb69a530a841', licence: 'Apache-2.0', author: 'Red Hat, Inc.', language: 'JavaScript'}

export const opossum = () => rule('opossum CircuitBreaker')
  // circuit.js:176-241 options: resetTimeout, errorThresholdPercentage, volumeThreshold, allowWarmUp,
  // rollingCountTimeout, rollingCountBuckets (status.js:56); `t0`: the first breaker's construction time (Date.now()).
  .params({resetTimeout: nat, threshold: nat, volumeThreshold: nat, allowWarmUp: bool, rollingCountTimeout: nat, buckets: nat, t0: nat})
  .pre(({buckets}) => buckets.atLeast(1))
  // One request: fire() (:615-828); a running call's outcome (the action's promise settling, :763-794, or its timeout
  // timer, :733-754), `filtered` being options.errorFilter's answer (:944); the reset timer (:318-320); the warm-up timer
  // (:278-281); close() and open() called by hand (or by healthCheck, :882); a new breaker made from this one's
  // toJSON().state (:535-549, :257-374). `bucket`: how many times the Status window has rotated (setInterval of
  // rotateBucket, status.js:83, 218-221), sent in; `life`: which breaker the request reaches (the last one made).
  .inputs({op: oneOf('fire', 'done', 'resetTimer', 'warmEnd', 'close', 'open', 'restore'), outcome: oneOf('success', 'failure', 'timeout'), filtered: bool, now: nat, bucket: nat, life: nat})
  // :255 STATE, :269 PENDING_CLOSE, :241 WARMING_UP (as `allowWarmUp` and not `warmDone`: it starts as allowWarmUp,
  // :280 clears it, and a restore sets it to the old value or allowWarmUp, :259, which is allowWarmUp again), :316 LAST_TIMER_AT (set once, when the constructor runs
  // `_startTimer(this)`), the reset timer's start (`openedAt`, the 'open' listener's setTimeout) and whether it is
  // armed. Ghost: `born` (this breaker's construction time), `inflight` (calls running), `lives` (breakers made),
  // `trippedAt` (when the breaker last went to OPEN, kept across a restore), `trials` (calls let through since it went
  // half-open).
  .state({
    st: oneOf('closed', 'open', 'halfOpen').from('closed'), pendingClose: bool.from(false), warmDone: bool.from(false),
    lastTimerAt: ({t0}) => t0, openedAt: 0, armed: bool.from(false),
    born: ({t0}) => t0, inflight: 0, lives: 0, trippedAt: 0, trials: 0, last: ({t0}) => t0, lastBucket: 0,
  })
  // The window (status.js:114-159): the 'fire' and 'failure' events (:296-300 increment the newest bucket) of this
  // breaker in the last `buckets` rotations.
  .log('op', 'bucket', 'life')
  .queries({
    fires: (r, {bucket, life, buckets}) => count(r.op.is('fire').and(r.life.eq(life), bucket.lt(r.bucket.plus(buckets)))),
    failures: (r, {bucket, life, buckets}) => count(r.op.is('done').and(r.life.eq(life), bucket.lt(r.bucket.plus(buckets)))),
  })
  .assume(({now, last, bucket, lastBucket, life, lives, op, inflight}) => now.atLeast(last).and(bucket.atLeast(lastBucket), life.eq(lives), op.is('done').implies(inflight.gt(0))))
  .flags(({op, outcome, filtered, st, pendingClose, allowWarmUp, warmDone, armed, now, openedAt, resetTimeout, born, rollingCountTimeout, fires, failures, volumeThreshold, threshold}) => {
    // :711-724 `!this.closed && !this.pendingClose` rejects; else PENDING_CLOSE = false and the call runs.
    const warmUp = allowWarmUp.and(warmDone.not())
    const admitted = op.is('fire').and(st.is('closed').or(pendingClose))
    // :763-784 success, or :941-947 an error errorFilter passes: 'success', whose listener (:349-353) closes a half-open
    // breaker.
    const succeeds = op.is('done').and(outcome.is('success').or(filtered))
    // :941-949 an error errorFilter does not pass (a timeout's too, :748): fail() (:981-998) emits 'failure' (counted in
    // the window with this one), returns under warm-up, returns below volumeThreshold unless half-open, and opens when
    // `failures / fires * 100 > errorThresholdPercentage` or half-open.
    const fails = op.is('done').and(outcome.is('success').not(), filtered.not())
    const rate = failures.plus(1).times(100).gt(threshold.mul(fires))
    const tripsOnFail = fails.and(warmUp.not(), fires.atLeast(volumeThreshold).or(st.is('halfOpen')), rate.or(st.is('halfOpen')))
    // open() (:422-433) does nothing when OPEN. close() (:397-411) nothing when CLOSED.
    const opens = tripsOnFail.or(op.is('open')).and(st.is('open').not())
    const closes = succeeds.and(st.is('halfOpen')).or(op.is('close').and(st.is('closed').not()))
    // :318-320 the reset timer fires resetTimeout after the 'open' event; _halfOpen (:333-346).
    const timer = op.is('resetTimer').and(armed, now.atLeast(openedAt.plus(resetTimeout)))
    const warmEnds = op.is('warmEnd').and(warmUp, now.atLeast(born.plus(rollingCountTimeout)))
    return {admitted, succeeds, fails, tripsOnFail, opens, closes, timer, warmEnds}
  })
  .keep(({op, fails}) => op.is('fire').or(fails))
  .step(({op, now, bucket, st, pendingClose, warmDone, lastTimerAt, openedAt, armed, born, inflight, lives, trippedAt, trials, resetTimeout, admitted, opens, closes, timer, warmEnds}) => {
    // A breaker made from toJSON().state (:257-374): a new instance (born now, its own window, nothing running, its
    // LAST_TIMER_AT now), CLOSED when the state was; HALF_OPEN with PENDING_CLOSE when it was half-open (:263, :371-373);
    // else open: half-open at once when `Date.now() - state.lastTimerAt > resetTimeout` (:364-367), else open() (:369),
    // which arms a new timer from now. Its warm-up is the old one's or allowWarmUp (:259).
    const restores = op.is('restore')
    const restoredHalf = restores.and(st.is('open'), now.gt(lastTimerAt.plus(resetTimeout)))
    const restoredOpen = restores.and(st.is('open'), restoredHalf.not())
    const toHalf = timer.or(restoredHalf)
    return {
      st: when(restores, when(restoredHalf, 'halfOpen', st), when(opens, 'open', when(closes, 'closed', when(timer, 'halfOpen', st)))),
      pendingClose: when(restores, st.is('halfOpen').or(restoredHalf), when(opens.or(closes), no, when(timer, yes, when(admitted, no, pendingClose)))),
      warmDone: when(restores, no, when(warmEnds, yes, warmDone)),
      lastTimerAt: when(restores, now, lastTimerAt),
      openedAt: when(opens.or(restoredOpen), now, openedAt),
      armed: when(restores, restoredOpen, when(opens, yes, when(closes.or(timer), no, armed))),
      born: when(restores, now, born),
      inflight: when(restores, 0, when(admitted, inflight.plus(1), when(op.is('done'), inflight.minus(1), inflight))),
      lives: when(restores, lives.plus(1), lives),
      trippedAt: when(opens, now, trippedAt),
      trials: when(toHalf.or(restores), 0, when(admitted.and(st.is('halfOpen')), trials.plus(1), trials)),
      last: now, lastBucket: bucket,
    }
  })

// ---------------------------------------------------------------------------------------------------------------
// App-vNext/Polly 7.2.4: the consecutive-count circuit breaker (Policy.Handle<E>().CircuitBreaker(n, durationOfBreak)).
const pol = {repo: 'App-vNext/Polly', commit: 'b1a5a17de8ef5d0bc86e5a4502ad30891e674379', licence: 'BSD-3-Clause', author: 'App vNext', language: 'C#'}

export const polly = () => rule('Polly ConsecutiveCountCircuitController')
  // ConsecutiveCountCircuitController.cs:8-20 `_exceptionsAllowedBeforeBreaking`, CircuitStateController.cs:9
  // `_durationOfBreak`, in ticks. CircuitBreakerSyntax.cs:199-200: the count must be > 0, the duration >= 0.
  .params({allowed: nat, durationOfBreak: nat})
  .pre(({allowed}) => allowed.atLeast(1))
  // One request: OnActionPreExecute (CircuitStateController.cs:157-173, CircuitBreakerEngine.cs:19); the action's
  // outcome: OnActionSuccess, OnActionFailure (a handled exception or result, CircuitBreakerEngine.cs:25-44) or an
  // unhandled exception (:38-41, rethrown with no call to the controller); Isolate() (:87-95), Reset() (:112), and the
  // CircuitState getter (:35-54). `now`: SystemClock.UtcNow().Ticks.
  .inputs({op: oneOf('execute', 'success', 'failure', 'unhandled', 'isolate', 'reset', 'state'), now: nat})
  // :10-11 `_blockedTill`, `_circuitState`; ConsecutiveCountCircuitController.cs:9 `_consecutiveFailureCount`. The
  // constructor's Reset() (:31-32): Closed, count 0, blockedTill DateTime.MinValue (0 here). Ghost: `inflight`, calls
  // admitted and not answered.
  .state({st: oneOf('Closed', 'Open', 'HalfOpen', 'Isolated').from('Closed'), blockedTill: 0, failures: 0, inflight: 0, last: 0})
  .assume(({now, last, op, inflight}) => now.atLeast(last).and(op.is('success').or(op.is('failure'), op.is('unhandled')).implies(inflight.gt(0))))
  .flags(({op, now, st, blockedTill, failures, allowed}) => {
    // :39-52 the getter: Open and `!IsInAutomatedBreak` (:83 `UtcNow().Ticks < _blockedTill`) is HalfOpen now. Only the
    // getter does this: OnActionSuccess and OnActionFailure read `_circuitState` as it is.
    const lazyHalf = op.is('execute').or(op.is('state')).and(st.is('Open'), now.atLeast(blockedTill))
    const half1 = st.is('HalfOpen').or(lazyHalf)
    // :161-170 Closed passes; HalfOpen passes when PermitHalfOpenCircuitTest (:127-137: `UtcNow().Ticks >=
    // _blockedTill`, then blockedTill moved to now + durationOfBreak, one winner by CompareExchange); Open and Isolated
    // throw.
    const trial = op.is('execute').and(half1, now.atLeast(blockedTill))
    const admitted = op.is('execute').and(st.is('Closed')).or(trial)
    // ConsecutiveCountCircuitController.cs:32-54: HalfOpen resets (closes, count 0, blockedTill MinValue, :114-125);
    // Closed sets the count to 0; Open and Isolated do nothing.
    const resets = op.is('success').and(st.is('HalfOpen')).or(op.is('reset'))
    // :56-84: HalfOpen breaks; Closed counts and breaks at `_exceptionsAllowedBeforeBreaking`; Open, Isolated nothing.
    const counts = op.is('failure').and(st.is('Closed'))
    const breaks = op.is('failure').and(st.is('HalfOpen')).or(counts.and(failures.plus(1).atLeast(allowed)))
    return {lazyHalf, trial, admitted, resets, counts, breaks}
  })
  .step(({op, now, st, blockedTill, failures, inflight, durationOfBreak, lazyHalf, trial, admitted, resets, counts, breaks}) => ({
    // Break_NeedsLock (:97-110): blocked till now + durationOfBreak, Open (the DateTime.MaxValue clamp, :101-104, is
    // past any time here); Isolate (:87-95) breaks for TimeSpan.MaxValue and sets Isolated: its blockedTill is never read
    // before a Reset overwrites it (only PermitHalfOpenCircuitTest and the Open getter read it), so it is kept.
    st: when(op.is('isolate'), 'Isolated', when(resets, 'Closed', when(breaks, 'Open', when(lazyHalf, 'HalfOpen', st)))),
    blockedTill: when(resets, 0, when(breaks.or(trial), now.plus(durationOfBreak), blockedTill)),
    failures: when(op.is('reset').or(resets), 0, when(op.is('success').and(st.is('Closed')), 0, when(counts, failures.plus(1), failures))),
    inflight: when(admitted, inflight.plus(1), when(op.is('success').or(op.is('failure'), op.is('unhandled')), inflight.minus(1), inflight)),
    last: now,
  }))

const g = gobreaker()
const gobCite = (path: string, lines: string, exp: string): Source => ({...gob, path, lines, export: exp})
const c = cockatiel()
const cockCite = (path: string, lines: string, exp: string): Source => ({...cock, path, lines, export: exp})

export const items: RealItem[] = [{
  id: 'circuit breaker/gobreaker/CircuitBreaker',
  domain: 'circuit breaker',
  source: gobCite('v2/gobreaker.go', '115-366', 'CircuitBreaker'),
  also: [gobCite('v2/counter.go', '1-50', 'Counts')],
  summary: 'Closed / half-open / open breaker with generations: counts cleared on every state change and every closed interval, open for Timeout, half-open admitting MaxRequests, a stale answer (older generation) ignored.',
  expressible: 'partial',
  gaps: [
    {gap: 'unbounded-collection', blocks: 'part', detail: 'the rolling window (Settings.BucketPeriod > 0): a ring of per-bucket Counts rolled by age, with subtract() rescanning every bucket (counter.go:52-212); only the fixed window (one bucket, BucketPeriod <= 0) is modelled'},
    {gap: 'scope', blocks: 'part', detail: 'ReadyToTrip is a user function of Counts; the default (ConsecutiveFailures > 5, gobreaker.go:177-179) is modelled'},
  ],
  laws: [
    invariant(g, g.law('half-open admits at most maxRequests requests', ({st, requests, exclusions, maxRequests}) => st.is('halfOpen').implies(requests.minus(exclusions).atMost(maxRequests))),
      'safety', 'docs', 'gobreaker.go:47-48 "MaxRequests is the maximum number of requests allowed to pass through when the CircuitBreaker is half-open"'),
    stepLaw(g, g.stepLaw('an open breaker admits no request before its timeout', ({admitted}) => admitted.not(), ({st, now, expiry}) => st.is('open').and(now.atMost(expiry))),
      'step', 'docs', 'gobreaker.go:60-61 "Timeout is the period of the open state, after which the state of the CircuitBreaker becomes half-open"'),
    stepLaw(g, g.stepLaw('a failure in half-open opens the breaker', (_, after) => after.st.is('open'), ({st, failed}) => st.is('halfOpen').and(failed)),
      'step', 'tests', 'gobreaker.go:295-296 `case StateHalfOpen: cb.setState(StateOpen, now)` (TestCircuitBreakerStateTransitions)'),
    stepLaw(g, g.stepLaw('the breaker closes only from half-open', ({st}, after) => after.st.is('closed').implies(st.is('closed').or(st.is('halfOpen')))),
      'step', 'inferred', 'onSuccess (:280-284) is the only setState(StateClosed): from half-open after enough successes'),
    stepLaw(g, g.stepLaw('a state change starts a new generation', ({st, generation}, after) => same(after.st, st).or(after.generation.gt(generation))),
      'step', 'docs', 'counter.go:4-6 "CircuitBreaker clears the internal Counts either on the change of the state or at the closed-state intervals. Counts ignores the results of the requests sent before clearing."'),
    stepLaw(g, g.stepLaw('a state change clears the failure counts', ({st}, after) => same(after.st, st).or(after.failures.eq(0).and(after.consecFail.eq(0), after.successes.eq(0)))),
      'step', 'docs', 'counter.go:4-5 "CircuitBreaker clears the internal Counts either on the change of the state or at the closed-state intervals"'),
    leadsTo(g, g.leadsTo('an open breaker goes half-open once its timeout passes', {
      from: ({st}) => st.is('open'),
      to: ({st}) => st.is('open').not(),
      helpful: ({expiry, last}) => ({op: 2, now: max(expiry.plus(1), last)}),
    }), 'docs', 'gobreaker.go:60-61 "after which the state of the CircuitBreaker becomes half-open"; State() at a time past the expiry'),
  ],
}, {
  id: 'circuit breaker/cockatiel/ConsecutiveBreaker',
  domain: 'circuit breaker',
  source: cockCite('src/CircuitBreakerPolicy.ts', '88-346', 'CircuitBreakerPolicy'),
  also: [cockCite('src/breaker/ConsecutiveBreaker.ts', '3-28', 'ConsecutiveBreaker')],
  summary: 'Closed / Open / HalfOpen / Isolated policy: a ConsecutiveBreaker opens it after `threshold` failures in a row, the first call after halfOpenAfter is the half-open test, isolate() holds it open until every handle is disposed.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'a call made while HalfOpen awaits the test and calls execute() again (CircuitBreakerPolicy.ts:237-243): modelled as a request that changes nothing, the caller retrying with a later request'},
    {gap: 'scope', blocks: 'part', detail: 'halfOpenAfter as a backoff factory (a user IBackoff whose duration varies with attemptNo) and initialState hydration (:153-177) are not modelled; a constant halfOpenAfter is'},
  ],
  laws: [
    stepLaw(c, c.stepLaw('an open circuit stays open on a call before halfOpenAfter', (_, after) => after.st.is('Open'), ({op, st, now, openedAt, halfOpenAfter}) => op.is('execute').and(st.is('Open'), now.lt(openedAt.plus(halfOpenAfter)))),
      'step', 'docs', 'CircuitBreakerPolicy.ts:245-247 Open: `Date.now() - state.openedAt < state.backoff.duration` throws BrokenCircuitError'),
    invariant(c, c.law('at most one half-open test runs at a time', ({tests}) => tests.atMost(1)),
      'safety', 'docs', 'CircuitBreakerPolicy.ts:110-113 "Event emitted when the circuit breaker is half open (running a test call)"; :238 other calls await the one test'),
    stepLaw(c, c.stepLaw('a successful test closes a half-open circuit', (_, after) => after.st.is('Closed'), ({st, testOk}) => st.is('HalfOpen').and(testOk)),
      'step', 'tests', 'CircuitBreakerPolicy.ts:303-305 success: `this.close()`'),
    stepLaw(c, c.stepLaw('a half-open circuit reopens only on its test failing', ({op, outcome}, after) => after.st.is('Open').implies(op.is('testDone').and(outcome.is('handled'))), ({st}) => st.is('HalfOpen')),
      'step', 'docs', 'CircuitBreakerPolicy.ts:21-25 HalfOpen: "Success of subsequent action/s controls onward transition to Open or Closed state"'),
    stepLaw(c, c.stepLaw('isolation ends only by a dispose', ({op}, after) => after.st.is('Isolated').or(op.is('dispose')), ({st}) => st.is('Isolated')),
      'step', 'docs', 'CircuitBreakerPolicy.ts:181-182 "Manually holds open the circuit breaker. @returns A handle that keeps the breaker open until `.dispose()` is called."'),
    invariant(c, c.law('an isolated circuit holds a handle', ({st, counters}) => st.is('Isolated').implies(counters.atLeast(1))),
      'safety', 'inferred', 'CircuitBreakerPolicy.ts:186-191, :201: Isolated with `counters` handles, closed when the count reaches 0'),
    leadsTo(c, c.leadsTo('an open circuit lets a test through once halfOpenAfter passes', {
      from: ({st}) => st.is('Open'),
      to: ({st}) => st.is('Open').not(),
      helpful: ({openedAt, halfOpenAfter, last}) => ({op: 0, now: max(openedAt.plus(halfOpenAfter), last)}),
    }), 'docs', 'CircuitBreakerPolicy.ts:55-58 "When to (potentially) enter the HalfOpen state from the Open state"'),
  ],
}]

const o = opossum()
const opoCite = (path: string, lines: string, exp: string): Source => ({...opo, path, lines, export: exp})
const pl = polly()
const polCite = (file: string, lines: string, exp: string): Source => ({...pol, path: `src/Polly/CircuitBreaker/${file}`, lines, export: exp})

items.push({
  id: 'circuit breaker/opossum/CircuitBreaker',
  domain: 'circuit breaker',
  source: opoCite('lib/circuit.js', '176-998', 'CircuitBreaker'),
  also: [opoCite('lib/status.js', '51-237', 'Status'), opoCite('README.md', '166-198', 'Breaker State Initialization')],
  summary: 'Closed / open / half-open breaker over a rolling window of fires and failures (errorThresholdPercentage, volumeThreshold, warm-up), a reset timer that lets one trial call through, and a breaker remade from toJSON().state.',
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'fail() compares `stats.failures / stats.fires * 100 > errorThresholdPercentage` in binary floating point (circuit.js:993-994); written as the exact failures * 100 > threshold * fires, which differs at some points (7 / 25 * 100 is 28.000000000000004 > 28)'},
    {gap: 'nonlinear', blocks: 'part', detail: 'the threshold test multiplies the errorThresholdPercentage param by the window\'s fire count, two unknowns'},
    {gap: 'async', blocks: 'part', detail: 'the window rotates on a setInterval (status.js:83) and the reset and warm-up timers are setTimeouts (circuit.js:278, :318): sent in as requests (the rotation count with each request; the timers as events at a time past their delay)'},
    {gap: 'scope', blocks: 'part', detail: 'not modelled: the semaphore (capacity, default Number.MAX_SAFE_INTEGER), the cache and coalescing (off by default), enable()/disable(), shutdown(), fallbacks (they change what the caller gets, not the state), and a restore that also passes `status`'},
  ],
  laws: [
    stepLaw(o, o.stepLaw('an open breaker rejects every call', ({admitted}) => admitted.not(), ({op, st}) => op.is('fire').and(st.is('open'))),
      'step', 'docs', 'circuit.js:414-416 "Each time the breaker is fired while the circuit is opened, a failed Promise is returned"'),
    stepLaw(o, o.stepLaw('no call is let through within resetTimeout of the breaker opening', ({admitted}) => admitted.not(), ({op, st, now, trippedAt, resetTimeout}) => op.is('fire').and(st.is('closed').not(), now.lt(trippedAt.plus(resetTimeout)))),
      'step', 'docs', 'circuit.js:42-43 "resetTimeout The time in milliseconds to wait before setting the breaker to `halfOpen` state"; README 166-198: a breaker remade from toJSON().state'),
    invariant(o, o.law('half-open lets one call through', ({st, trials}) => st.is('halfOpen').implies(trials.atMost(1))),
      'safety', 'tests', 'test/state-test.js:113 "When half-open, the circuit only allows one request through"'),
    stepLaw(o, o.stepLaw('a failure in half-open reopens the breaker', (_, after) => after.st.is('open'), ({st, fails}) => st.is('halfOpen').and(fails)),
      'step', 'docs', 'circuit.js:337-340 halfOpen: "allowing for a single attempt to call the service again. If that attempt is successful, the circuit will be closed. Otherwise it remains open."'),
    stepLaw(o, o.stepLaw('a success in half-open closes the breaker', (_, after) => after.st.is('closed'), ({st, succeeds}) => st.is('halfOpen').and(succeeds)),
      'step', 'docs', 'circuit.js:337-340 "If that attempt is successful, the circuit will be closed"'),
    stepLaw(o, o.stepLaw('a failing call opens a closed breaker only past the threshold', ({fires, failures, threshold, volumeThreshold}) => failures.plus(1).times(100).gt(threshold.mul(fires)).and(fires.atLeast(volumeThreshold)),
      ({op, st, tripsOnFail}) => op.is('done').and(st.is('closed'), tripsOnFail)),
      'step', 'docs', 'circuit.js:63-67 "errorThresholdPercentage the error percentage at which to open the circuit"; :74-76 volumeThreshold "the minimum number of requests within the rolling statistical window that must exist before the circuit breaker can open"'),
    leadsTo(o, o.leadsTo('an open breaker goes half-open once resetTimeout passes', {
      from: ({st}) => st.is('open'),
      to: ({st}) => st.is('open').not(),
      helpful: ({openedAt, resetTimeout, last, lives, lastBucket}) => ({op: 2, now: max(openedAt.plus(resetTimeout), last), life: lives, bucket: lastBucket}),
    }), 'docs', 'circuit.js:338-339 halfOpen is "Emitted after `options.resetTimeout` has elapsed"'),
    leadsTo(o, o.leadsTo('a half-open breaker closes or reopens', {
      from: ({st}) => st.is('halfOpen'),
      to: ({st}) => st.is('halfOpen').not(),
      helpful: [
        {when: ({pendingClose}) => pendingClose, request: ({last, lives, lastBucket}) => ({op: 0, now: last, life: lives, bucket: lastBucket})},
        {when: ({pendingClose, inflight}) => pendingClose.not().and(inflight.gt(0)), request: ({last, lives, lastBucket}) => ({op: 1, outcome: 1, filtered: 0, now: last, life: lives, bucket: lastBucket})},
      ],
    }), 'docs', 'circuit.js:337-340 "a single attempt to call the service again. If that attempt is successful, the circuit will be closed. Otherwise it remains open."'),
  ],
}, {
  id: 'circuit breaker/polly/ConsecutiveCountCircuitController',
  domain: 'circuit breaker',
  source: polCite('CircuitStateController.cs', '7-180', 'CircuitStateController'),
  also: [polCite('ConsecutiveCountCircuitController.cs', '6-85', 'ConsecutiveCountCircuitController'), polCite('CircuitBreakerEngine.cs', '9-52', 'CircuitBreakerEngine.Implementation'), polCite('CircuitBreakerSyntax.cs', '12-24', 'CircuitBreaker')],
  summary: 'Closed / Open / HalfOpen / Isolated breaker: n handled failures in a row break it for durationOfBreak, then one trial call per durationOfBreak while half-open; a late result while Open changes nothing.',
  expressible: 'full',
  gaps: [],
  laws: [
    stepLaw(pl, pl.stepLaw('an open circuit admits no call before the break ends', ({admitted}) => admitted.not(), ({op, st, now, blockedTill}) => op.is('execute').and(st.is('Open'), now.lt(blockedTill))),
      'step', 'docs', 'CircuitBreakerSyntax.cs:16-18 "The circuit will stay broken for the durationOfBreak. Any attempt to execute this policy while the circuit is broken, will immediately throw"'),
    stepLaw(pl, pl.stepLaw('a half-open circuit admits no call while a trial blocks it', ({admitted}) => admitted.not(), ({op, st, now, blockedTill}) => op.is('execute').and(st.is('HalfOpen'), now.lt(blockedTill))),
      'step', 'docs', 'CircuitStateController.cs:132-134 "It\'s time to permit a / another trial call in the half-open state ... we have to ensure only _one_ thread wins the race to own this next call"'),
    stepLaw(pl, pl.stepLaw('a success in half-open closes the circuit', (_, after) => after.st.is('Closed'), ({op, st}) => op.is('success').and(st.is('HalfOpen'))),
      'step', 'docs', 'CircuitBreakerSyntax.cs:20-21 "If the first action after the break duration period results in a handled exception, the circuit will break again for another durationOfBreak; if no exception is thrown, the circuit will reset."'),
    stepLaw(pl, pl.stepLaw('a failure in half-open breaks the circuit for another durationOfBreak', ({now, durationOfBreak}, after) => after.st.is('Open').and(after.blockedTill.eq(now.plus(durationOfBreak))), ({op, st}) => op.is('failure').and(st.is('HalfOpen'))),
      'step', 'docs', 'CircuitBreakerSyntax.cs:20-21 "the circuit will break again for another durationOfBreak"'),
    stepLaw(pl, pl.stepLaw('a late result while open does not extend the break', ({blockedTill}, after) => after.st.is('Open').and(after.blockedTill.eq(blockedTill)), ({op, st}) => op.is('success').or(op.is('failure')).and(st.is('Open'))),
      'step', 'docs', 'ConsecutiveCountCircuitController.cs:78 "A failure call result may arrive when the circuit is open ... we do not want to extend time for which the circuit is broken"'),
    invariant(pl, pl.law('a closed circuit has fewer consecutive failures than allowed', ({st, failures, allowed}) => st.is('Closed').implies(failures.lt(allowed))),
      'safety', 'docs', 'CircuitBreakerSyntax.cs:14-15 "The circuit will break if exceptionsAllowedBeforeBreaking exceptions that are handled by this policy are raised consecutively"'),
    stepLaw(pl, pl.stepLaw('an isolated circuit stays isolated until reset', ({op}, after) => after.st.is('Isolated').or(op.is('reset')), ({st}) => st.is('Isolated')),
      'step', 'docs', 'CircuitStateController.cs:91 "The circuit is manually held open and is not allowing calls."'),
    leadsTo(pl, pl.leadsTo('an open circuit goes half-open once the break ends', {
      from: ({st}) => st.is('Open'),
      to: ({st}) => st.is('Open').not(),
      helpful: ({blockedTill, last}) => ({op: 6, now: max(blockedTill, last)}),
    }), 'docs', 'ConsecutiveCountCircuitController.cs:48 "only time passing governs transitioning from Open to HalfOpen state"'),
  ],
})
