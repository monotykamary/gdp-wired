// Job queues and retries from four libraries, each written as the rule its code runs, with the laws a reviewer would
// ask about. Group `queuebreaker`; the sources are in sources/queuebreaker.json.
//
//   - taskforcesh/bullmq v6.4.0 (MIT, (c) 2018 BullForce Labs AB and contributors, TypeScript and Redis Lua):
//     https://github.com/taskforcesh/bullmq/tree/253bc4b1acd9c6030c01817b38ae65e067666ed4/src
//   - graphile/worker v0.18.0 (MIT, (c) 2019 Benjie Gillam, TypeScript and SQL):
//     https://github.com/graphile/worker/tree/4cda192c5df254392a1dff350e5d73f7d2c18a85/src/sql
//   - timgit/pg-boss 12.38.0 (MIT, (c) 2016 Tim Jones, TypeScript and SQL):
//     https://github.com/timgit/pg-boss/blob/2c1005b744952360e999c2000e155a1bfebb8951/src/plans.ts
//   - sindresorhus/p-retry v8.0.1 (MIT, (c) Sindre Sorhus, JavaScript):
//     https://github.com/sindresorhus/p-retry/blob/81cd2f0e523faeeff685c5878224a0d7390ff0db/index.js
//
// Each queue rule follows one job through its life (the per-job state the scripts and statements read and write; other
// jobs only decide when a fetch happens, which the requests choose). The clock (Date.now() in Lua's ARGV, Postgres's
// now(), performance.now()) is sent in with each request as `now`, and requests come in time order. A call that
// throws, returns an error code, or matches no row is a request where every part keeps its value.
import {bool, fn, forall, max, min, nat, oneOf, recur, rule, same, when, yes} from '../../../core/dsl.ts'
import {type RealItem, type Source, invariant, leadsTo, stepLaw} from '../lib.ts'

// ---------------------------------------------------------------------------------------------------------------
// BullMQ: one job's attempts, retries and backoff (Job.moveToFailed and the Lua scripts it runs).
const bull = {repo: 'taskforcesh/bullmq', commit: '253bc4b1acd9c6030c01817b38ae65e067666ed4', licence: 'MIT', author: 'BullForce Labs AB and contributors', language: 'TypeScript'}

// backoffs.ts:23-33 exponential, no jitter: Math.round(2 ** (attemptsMade - 1) * delay), read at attemptsMade + 1
// (job.ts:721-727), so 2^k · delay at the job's attemptsMade k: exact for integer delays. No lemma is stated.
export const bullExpo = () => recur('bullExpo', {args: ['delay'], zero: ({delay}) => delay, next: (_, d) => d.times(2)})

export const bullmq = () => rule('BullMQ job retry')
  // JobsOptions: attempts (job.ts:208-212, default 0 here, documented default 1), backoff (backoffs.ts:37-48: a number
  // is fixed; none, fixed or exponential), backoff.delay; WorkerOptions maxStartedAttempts (0: unset) and
  // maxStalledCount (worker.ts:307, default 1).
  .params({attempts: nat, backoff: oneOf('none', 'fixed', 'exponential'), delay: nat, maxStartedAttempts: nat, maxStalledCount: nat})
  // One request: moveToActive (a worker takes the job, prepareJobForProcessing.lua:10-42); moveToCompleted (job.ts:652-690,
  // moveToFinished-14.lua); moveToFailed (job.ts:743-829) with whether the error is an UnrecoverableError (:708-709);
  // promoteDelayedJobs (promoteDelayedJobs.lua:13-36, run by moveToActive, retryJob and the delay marker); the stalled
  // checker finding the job's lock gone (moveStalledJobsToWait-9.lua:60-107).
  .inputs({op: oneOf('fetch', 'complete', 'fail', 'promote', 'stall'), unrecoverable: bool, now: nat})
  // The job hash's attemptsMade ("atm"), attemptsStarted ("ats"), stalledCounter ("stc"), deferred failure ("defa"),
  // the list or set it is in, and its delayed timestamp (getDelayedScore.lua:7-24: the score is it times 0x1000 plus a
  // counter below 0x1000, so promoteDelayedJobs' `<= (now + 1) * 0x1000 - 1` is `until <= now`).
  .state({st: oneOf('wait', 'active', 'delayed', 'completed', 'failed').from('wait'), atm: 0, ats: 0, stc: 0, defa: bool.from(false), until: 0, last: 0})
  .fns({expo: bullExpo()})
  // worker.ts:1072-1095: a job with a deferred failure, or started more than maxStartedAttempts times
  // (getUnrecoverableErrorMessage, :1157-1169), is failed by the worker with an UnrecoverableError before the
  // processor runs, so it is never completed then.
  .assume(({now, last, op, defa, ats, maxStartedAttempts}) => now.atLeast(last).and(op.is('complete').implies(defa.not().and(maxStartedAttempts.eq(0).or(ats.atMost(maxStartedAttempts))))))
  .flags(({op, unrecoverable, st, atm, ats, defa, until, now, attempts, maxStartedAttempts}) => {
    const fetches = op.is('fetch').and(st.is('wait'))
    const completes = op.is('complete').and(st.is('active'))
    const failing = op.is('fail').and(st.is('active'))
    // job.ts:708-719 shouldRetryJob: `attemptsMade + 1 < attempts`, not unrecoverable, not
    // `maxStartedAttempts <= attemptsStarted`; the worker's own unrecoverable failures (worker.ts:1157-1169).
    const unrec = unrecoverable.or(defa, maxStartedAttempts.gt(0).and(maxStartedAttempts.lt(ats)))
    const retries = failing.and(atm.plus(1).lt(attempts), unrec.not(), maxStartedAttempts.gt(0).and(maxStartedAttempts.atMost(ats)).not())
    const fails = failing.and(retries.not())
    const promotes = op.is('promote').and(st.is('delayed'), until.atMost(now))
    const stalls = op.is('stall').and(st.is('active'))
    return {fetches, completes, failing, retries, fails, promotes, stalls}
  })
  .step(({now, backoff, delay, maxStalledCount, st, atm, ats, stc, defa, until, expo, fetches, completes, failing, retries, fails, promotes, stalls}) => {
    // backoffs.ts:50-62, :9-35: no backoff gives undefined (job.ts:729: a retry with no delay); fixed its delay;
    // exponential 2^atm · delay.
    const wait = when(backoff.is('fixed'), delay, when(backoff.is('exponential'), expo(atm, delay), 0))
    // job.ts:775-799: a delay moves the job to delayed (moveToDelayed-11.lua:54-60: until now + delay, "atm" + 1); none
    // retries at once (retryJob-11.lua:56-61: back to wait, "atm" + 1); else moveToFinished failed (:166, "atm" + 1).
    const delayed = retries.and(wait.gt(0))
    // moveStalledJobsToWait-9.lua:75-101: "stc" + 1, a deferred failure past maxStalledCount, back to wait.
    return {
      st: when(fetches, 'active', when(completes, 'completed', when(delayed, 'delayed', when(retries, 'wait', when(fails, 'failed', when(promotes.or(stalls), 'wait', st)))))),
      atm: when(completes.or(failing), atm.plus(1), atm),
      ats: when(fetches, ats.plus(1), ats),
      stc: when(stalls, stc.plus(1), stc),
      defa: when(stalls.and(stc.plus(1).gt(maxStalledCount)), yes, defa),
      until: when(delayed, now.plus(wait), until),
      last: now,
    }
  })

// ---------------------------------------------------------------------------------------------------------------
// graphile-worker: one job's row through get_job, complete_job, fail_job, return_job and the 4-hour lock reset.
const gw = {repo: 'graphile/worker', commit: '4cda192c5df254392a1dff350e5d73f7d2c18a85', licence: 'MIT', author: 'Benjie Gillam', language: 'TypeScript'}

// failJobs.ts:123 `exp(least(attempts, 10)) * interval '1 second'`, a float rounded to Postgres's microseconds: known
// here only by bounds (website/docs/exponential-backoff.md:21-30 lists them: 2.718282 s at attempt 1, 06:07:06.465795
// from attempt 10).
const gwBackoff = fn(1, (x: number) => Math.round(Math.exp(x) * 1e6), {facts: f => ({
  'at least e seconds from attempt 1': forall(x => x.atLeast(1).implies(f(x).atLeast(2718282))),
  'at most e^10 seconds up to attempt 10': forall(x => x.atMost(10).implies(f(x).atMost(22026465795))),
})})
const fourHours = 4 * 3600 * 1_000_000

export const graphileWorker = () => rule('graphile-worker job')
  // sql/000011.sql:58 `max_attempts smallint default 25 ... check (max_attempts >= 1)`; `t0`: the row's run_at when
  // added (default now(), :56), in microseconds.
  .params({maxAttempts: nat, t0: nat})
  .pre(({maxAttempts}) => maxAttempts.atLeast(1))
  // One request, by the worker pool `pool` (>= 1; locked_by holds its id): get_job (getJobs.ts:230-251), complete
  // (completeJobs.ts:51-60, a delete), fail (failJobs.ts:116-138), return (returnJobs.ts:53-63, a pool shutting down
  // gives back what it fetched), and the sweep of locks older than 4 hours (resetLockedAt.ts:20-28).
  .inputs({op: oneOf('get', 'complete', 'fail', 'return', 'reset'), pool: nat, now: nat})
  // The row (sql/000011.sql:50-68): attempts, run_at, locked_at, locked_by (0: null) and whether it was deleted.
  // Ghost: `Running`, the pools that fetched it and have not finished with it (a worker completes, fails or returns
  // only a job it got).
  .state({attempts: 0, runAt: ({t0}) => t0, lockedAt: 0, lockedBy: 0, deleted: bool.from(false), last: ({t0}) => t0})
  .maps({Running: 0})
  .fns({backoff: gwBackoff})
  .assume(({now, last, op, pool, Running}) => now.atLeast(last).and(pool.atLeast(1), op.is('complete').or(op.is('fail'), op.is('return')).implies(Running.at(pool).eq(1))))
  .flags(({op, pool, now, attempts, runAt, lockedAt, lockedBy, deleted, maxAttempts}) => {
    // getJobs.ts:233-243 `is_available = true and run_at <= now`; is_available is `locked_at is null and attempts <
    // max_attempts` (sql/000011.sql:67).
    const gets = op.is('get').and(deleted.not(), lockedBy.eq(0), attempts.lt(maxAttempts), runAt.atMost(now))
    const holds = deleted.not().and(lockedBy.eq(pool))
    // failJobs.ts:126 and returnJobs.ts:62 `locked_by = $poolId`; completeJobs.ts:55-56 deletes by id alone.
    const completes = op.is('complete').and(deleted.not())
    const fails = op.is('fail').and(holds)
    const returns = op.is('return').and(holds)
    // resetLockedAt.ts:24 `locked_at < now - interval '4 hours'` (null never is).
    const resets = op.is('reset').and(deleted.not(), lockedBy.gt(0), lockedAt.plus(fourHours).lt(now))
    return {gets, completes, fails, returns, resets}
  })
  .step(({op, pool, now, attempts, runAt, lockedAt, lockedBy, deleted, Running, backoff, gets, completes, fails, returns, resets}) => ({
    // getJobs.ts:245-249 attempts + 1, locked by the pool at now.
    attempts: when(gets, attempts.plus(1), when(returns, attempts.minus(1), attempts)),
    // failJobs.ts:123 `greatest(now(), run_at) + exp(least(attempts, 10)) seconds`; resetLockedAt.ts:23
    // `greatest(run_at, now)`.
    runAt: when(fails, max(now, runAt).plus(backoff(min(attempts, 10))), when(resets, max(runAt, now), runAt)),
    lockedAt: when(gets, now, when(fails.or(returns, resets), 0, lockedAt)),
    lockedBy: when(gets, pool, when(fails.or(returns, resets), 0, lockedBy)),
    deleted: when(completes, yes, deleted),
    Running: Running.set(pool, when(gets, 1, when(op.is('complete').or(op.is('fail'), op.is('return')), 0, Running.at(pool)))),
    last: now,
  }))

// ---------------------------------------------------------------------------------------------------------------
// pg-boss: one job through fetch, complete, fail (by a worker or by expiry), cancel, resume and retry.
const pgb = {repo: 'timgit/pg-boss', commit: '2c1005b744952360e999c2000e155a1bfebb8951', licence: 'MIT', author: 'Tim Jones', language: 'TypeScript'}
const us = 1_000_000

export const pgBoss = () => rule('pg-boss job')
  // The job's retry_limit as sent (plans.ts:3147, default 2), retry_delay (s), retry_backoff, retry_delay_max (s, or
  // none: LEAST ignores a null), expire_seconds; `t0`: its start_after when sent, in microseconds.
  .params({retryLimit0: nat, retryDelay: nat, retryBackoff: bool, hasDelayMax: bool, retryDelayMax: nat, expireSeconds: nat, t0: nat})
  // One request: fetchNextJob (plans.ts:2813-2817), complete (completeJobs, :2883-2897, includeQueued false), fail
  // (failJobsById, :3235-3240), the expiry sweep (failJobsByTimeout, :3244-3261), cancel (:2986-3009), resume
  // (:3011-3035), retry (retryJobs, :4140-4155). A worker's settle is fenced by the retry_count it fetched (`rc`,
  // attemptFence :2846-2849) or not (`fenced`). `wait`: the jittered backoff in microseconds, `GREATEST(retry_delay, 1)
  // * (2 ^ LEAST(16, retry_count + 1) / 2 + ... * random())` seconds (:3401-3404), which the rule takes as given.
  .inputs({op: oneOf('fetch', 'complete', 'fail', 'expire', 'cancel', 'resume', 'retry'), fenced: bool, rc: nat, wait: nat, now: nat})
  // The row: state (JOB_STATES, :52-59, in that order), retry_count, retry_limit (retryJobs raises it), started_on
  // (`started`, and when), start_after. Ghost: `claims`, the fetches; `resumed`, whether resume() was ever called.
  .state({
    st: oneOf('created', 'retry', 'active', 'completed', 'cancelled', 'failed').from('created'), retryCount: 0, retryLimit: ({retryLimit0}) => retryLimit0,
    started: bool.from(false), startedOn: 0, startAfter: ({t0}) => t0, claims: 0, resumed: bool.from(false), last: ({t0}) => t0,
  })
  .assume(({now, last}) => now.atLeast(last))
  .flags(({op, fenced, rc, now, st, retryCount, startedOn, startAfter, expireSeconds}) => {
    const queued = st.is('created').or(st.is('retry')), open = queued.or(st.is('active'))
    // :2696-2703 `state < 'active' AND start_after <= job_now()`.
    const fetches = op.is('fetch').and(queued, startAfter.atMost(now))
    // attemptFence: `state = 'active' AND id:retry_count` the one fetched.
    const fence = fenced.not().or(st.is('active').and(rc.eq(retryCount)))
    const completes = op.is('complete').and(st.is('active'), fence)
    // :3236 `state < 'completed'`; :3245-3246 `state = 'active' AND started_on + expire_seconds < job_now()`.
    const failsNow = op.is('fail').and(open, fence).or(op.is('expire').and(st.is('active'), startedOn.plus(expireSeconds.times(us)).lt(now)))
    const cancels = op.is('cancel').and(open)
    const resumes = op.is('resume').and(st.is('cancelled'))
    const retriesByHand = op.is('retry').and(st.is('failed'))
    return {fetches, completes, failsNow, cancels, resumes, retriesByHand}
  })
  .step(({now, wait, retryDelay, retryBackoff, hasDelayMax, retryDelayMax, st, retryCount, retryLimit, started, startedOn, startAfter, claims, resumed, fetches, completes, failsNow, cancels, resumes, retriesByHand}) => {
    // failJobsBody (:3331-3420): retry while `retry_count < retry_limit`, else failed; start_after kept when
    // `retry_count = retry_limit`, else now + retry_delay seconds, or with backoff now + LEAST(retry_delay_max, the
    // jittered product) seconds.
    const again = failsNow.and(retryCount.lt(retryLimit))
    const nextStart = when(retryCount.eq(retryLimit), startAfter, when(retryBackoff.not(), now.plus(retryDelay.times(us)), now.plus(when(hasDelayMax, min(retryDelayMax.times(us), wait), wait))))
    return {
      st: when(fetches, 'active', when(completes, 'completed', when(again, 'retry', when(failsNow, 'failed', when(cancels, 'cancelled', when(resumes, 'created', when(retriesByHand, 'retry', st))))))),
      // :2817 `retry_count = CASE WHEN started_on IS NOT NULL THEN retry_count + 1 ELSE retry_count END`.
      retryCount: when(fetches.and(started), retryCount.plus(1), retryCount),
      // :4145 `retry_limit = retry_limit + 1`.
      retryLimit: when(retriesByHand, retryLimit.plus(1), retryLimit),
      started: when(fetches, yes, started),
      startedOn: when(fetches, now, startedOn),
      // :3025 and :4147 `GREATEST(start_after, job_now())`.
      startAfter: when(failsNow, nextStart, when(resumes.or(retriesByHand), max(startAfter, now), startAfter)),
      claims: when(fetches, claims.plus(1), claims),
      resumed: when(resumes, yes, resumed),
      last: now,
    }
  })

// ---------------------------------------------------------------------------------------------------------------
// p-retry: one pRetry(input, options) call, a request per attempt.
const pr = {repo: 'sindresorhus/p-retry', commit: '81cd2f0e523faeeff685c5878224a0d7390ff0db', licence: 'MIT', author: 'Sindre Sorhus', language: 'JavaScript'}

// index.js:66-74 calculateDelay without randomize: Math.round(minTimeout * factor ** (attempt - 1)) at attempt
// max(1, retriesConsumed + 1), so minTimeout · factor^k at k retries consumed (exact for integers); :228-231 a factor
// that isn't > 0 is 1. No lemma is stated.
export const pRetryDelay = () => recur('pRetryDelay', {args: ['minTimeout', 'factor'], zero: ({minTimeout}) => minTimeout, next: (_, d, {factor}) => d.mul(max(factor, 1))})

export const pRetry = () => rule('p-retry')
  // Options (index.js:209-217): retries (or Infinity: `forever`), factor, minTimeout, maxTimeout (or Infinity),
  // maxRetryTime (or Infinity), randomize false.
  .params({retries: nat, forever: bool, factor: nat, minTimeout: nat, hasMaxTimeout: bool, maxTimeout: nat, hasMaxRetryTime: bool, maxRetryTime: nat})
  // One attempt (:239-261): the input resolves (`ok`), or throws: an AbortError (:114-116), a TypeError that isn't a
  // network error (:170-172), or another error; shouldConsumeRetry's and shouldRetry's answers (any user function);
  // `now`, performance.now() - startTime when shouldRetry has answered (:178; the earlier reads at :124, :160, :164 are
  // no later, and each rejects only when this one would too).
  .inputs({ok: bool, abort: bool, typeError: bool, consume: bool, retry: bool, now: nat})
  // :235-236 attemptNumber, retriesConsumed; the call's outcome. Ghost: `waited`, the last delayForRetry (:189-193),
  // and `resumeAt`, when it ends: the next attempt starts no earlier.
  .state({st: oneOf('running', 'resolved', 'rejected').from('running'), attempts: 0, consumed: 0, waited: 0, resumeAt: 0})
  .fns({delay: pRetryDelay()})
  .assume(({now, resumeAt}) => now.atLeast(resumeAt))
  .flags(({ok, abort, typeError, consume, retry, now, st, consumed, retries, forever, hasMaxRetryTime, maxRetryTime}) => {
    const running = st.is('running')
    const resolves = running.and(ok)
    const fails = running.and(ok.not())
    // :118-120 retriesLeft; :126, :160, :166, :180 out of time; :166 none left; :170 a TypeError; :174 shouldRetry.
    const left = forever.or(consumed.lt(retries))
    const outOfTime = hasMaxRetryTime.and(now.atLeast(maxRetryTime))
    const rejects = fails.and(abort.or(outOfTime, left.not(), typeError, retry.not()))
    // :184-197 a retry: without consuming one when shouldConsumeRetry says no, else after the delay.
    const again = fails.and(rejects.not())
    const consumes = again.and(consume)
    return {resolves, rejects, again, consumes}
  })
  .step(({now, st, attempts, consumed, waited, resumeAt, minTimeout, factor, hasMaxTimeout, maxTimeout, hasMaxRetryTime, maxRetryTime, delay, resolves, rejects, again, consumes}) => {
    // :123 calculateDelay(retriesConsumed); :71 `Math.min(timeout, maxTimeout)`; :189 `Math.min(effectiveDelay,
    // remainingTimeAfterShouldRetry)`.
    const d = when(hasMaxTimeout, min(delay(consumed, minTimeout, factor), maxTimeout), delay(consumed, minTimeout, factor))
    const final = when(hasMaxRetryTime, min(d, maxRetryTime.minus(now)), d)
    return {
      st: when(resolves, 'resolved', when(rejects, 'rejected', st)),
      attempts: when(st.is('running'), attempts.plus(1), attempts),
      consumed: when(consumes, consumed.plus(1), consumed),
      waited: when(consumes, final, when(again, 0, waited)),
      resumeAt: when(consumes, now.plus(final), when(again, now, resumeAt)),
    }
  })

const b = bullmq(), bullCite = (path: string, lines: string, exp: string, language = 'TypeScript'): Source => ({...bull, path, lines, export: exp, language})
const w = graphileWorker(), gwCite = (path: string, lines: string, exp: string, language = 'TypeScript'): Source => ({...gw, path, lines, export: exp, language})
const q = pgBoss(), pgbCite = (path: string, lines: string, exp: string): Source => ({...pgb, path, lines, export: exp})
const r = pRetry(), prCite = (path: string, lines: string, exp: string): Source => ({...pr, path, lines, export: exp})

export const items: RealItem[] = [{
  id: 'queue/bullmq/jobRetry',
  domain: 'queue',
  source: bullCite('src/classes/job.ts', '706-829', 'Job.moveToFailed'),
  also: [
    bullCite('src/classes/backoffs.ts', '9-62', 'Backoffs'),
    bullCite('src/classes/worker.ts', '1072-1095', 'Worker.processJob'), bullCite('src/classes/worker.ts', '1157-1169', 'getUnrecoverableErrorMessage'),
    bullCite('src/commands/moveToDelayed-11.lua', '43-79', 'moveToDelayed', 'Lua'), bullCite('src/commands/retryJob-11.lua', '38-69', 'retryJob', 'Lua'),
    bullCite('src/commands/moveToFinished-14.lua', '77-210', 'moveToFinished', 'Lua'), bullCite('src/commands/moveStalledJobsToWait-9.lua', '44-122', 'moveStalledJobsToWait', 'Lua'),
    bullCite('src/commands/includes/prepareJobForProcessing.lua', '10-42', 'prepareJobForProcessing', 'Lua'), bullCite('src/commands/includes/promoteDelayedJobs.lua', '13-36', 'promoteDelayedJobs', 'Lua'),
    bullCite('src/commands/includes/getDelayedScore.lua', '7-24', 'getDelayedScore', 'Lua'),
  ],
  summary: 'One job: taken by a worker (attemptsStarted + 1), completed, or failed and retried (wait or delayed by a fixed or exponential backoff) while attemptsMade + 1 < attempts; an unrecoverable error, a deferred stall failure or maxStartedAttempts fails it for good.',
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'backoff jitter (backoffs.ts:13-16, :25-29: Math.floor(Math.random() * ...)) is not modelled; jitter 0, the default, is'},
    {gap: 'other', blocks: 'part', detail: 'a custom backoffStrategy (a user function, its -1 meaning no retry, job.ts:729), repeatable jobs exempt from the stall limit (moveStalledJobsToWait-9.lua:77-99), lock tokens (removeLock) and flows (parent/child dependencies) are not modelled'},
    {gap: 'async', blocks: 'part', detail: 'the stalled checker runs on a timer in two passes (marking active jobs, then moving those whose lock expired): written as one stall event on an active job'},
  ],
  laws: [
    invariant(b, b.law('a job is finished at most max(attempts, 1) times', ({atm, attempts}) => atm.atMost(max(attempts, 1))),
      'safety', 'docs', 'base-job-options.ts:30-34 "The total number of attempts to try the job until it completes."'),
    stepLaw(b, b.stepLaw('a completed job is never retried', (_, after) => after.st.is('completed'), ({st}) => st.is('completed')),
      'step', 'inferred', 'moveToFinished-14.lua:2-3 "A job can only be moved to completed if it was active"; no script takes a job out of completed but job.retry'),
    stepLaw(b, b.stepLaw('an unrecoverable error fails the job for good', (_, after) => after.st.is('failed'), ({failing, unrecoverable}) => failing.and(unrecoverable)),
      'step', 'docs', 'errors/unrecoverable-error.ts:5-6 "Error to move a job to failed even if the attemptsMade are lower than the expected limit."'),
    stepLaw(b, b.stepLaw('a job started maxStartedAttempts times is not retried', (_, after) => after.st.is('failed'), ({failing, maxStartedAttempts, ats}) => failing.and(maxStartedAttempts.gt(0), maxStartedAttempts.atMost(ats))),
      'step', 'docs', 'job.ts:710-711 "A job that has been started as many times as `maxStartedAttempts` allows must not be retried again, regardless of its remaining attempts."'),
    stepLaw(b, b.stepLaw('an exponential retry waits at least the base delay', ({now, delay}, after) => after.until.atLeast(now.plus(delay)), ({backoff, retries}) => backoff.is('exponential').and(retries)),
      'step', 'inferred', 'backoffs.ts:31 `Math.round(Math.pow(2, attemptsMade - 1) * delay)` at attemptsMade >= 1: the first retry waits `delay`, each later one longer'),
    leadsTo(b, b.leadsTo('a delayed job is promoted once its delay passes', {
      from: ({st}) => st.is('delayed'),
      to: ({st}) => st.is('delayed').not(),
      helpful: ({until, last}) => ({op: 3, now: max(until, last)}),
    }), 'docs', 'promoteDelayedJobs.lua:2-3 "Updates the delay set, by moving delayed jobs that should be processed now to wait"'),
    leadsTo(b, b.leadsTo('every job completes or fails for good', {
      from: ({st}) => st.is('completed').not().and(st.is('failed').not()),
      to: ({st}) => st.is('completed').or(st.is('failed')),
      helpful: [
        {when: ({st}) => st.is('wait'), request: ({last}) => ({op: 0, now: last})},
        {when: ({st}) => st.is('active'), request: ({last}) => ({op: 2, unrecoverable: 0, now: last})},
        {when: ({st}) => st.is('delayed'), request: ({until, last}) => ({op: 3, now: max(until, last)})},
      ],
    }), 'docs', 'base-job-options.ts:30-34 attempts "until it completes"; worker.ts:307 maxStalledCount: a job that keeps stalling is failed'),
  ],
}, {
  id: 'queue/graphile-worker/jobLifecycle',
  domain: 'queue',
  source: gwCite('src/sql/failJobs.ts', '101-140', 'failJobs'),
  also: [
    gwCite('src/sql/getJobs.ts', '90-251', 'constructQuery'), gwCite('src/sql/completeJobs.ts', '6-84', 'batchCompleteJobs'),
    gwCite('src/sql/returnJobs.ts', '25-65', 'returnJobs'), gwCite('src/sql/resetLockedAt.ts', '20-28', 'resetLockedAt'),
    gwCite('sql/000011.sql', '50-68', 'jobs', 'SQL'), gwCite('website/docs/exponential-backoff.md', '6-30', 'Exponential backoff', 'Markdown'),
  ],
  summary: 'One job row: taken while unlocked, due and below max_attempts (attempts + 1, locked), completed (deleted), failed by its lock holder (unlocked, run_at pushed back by exp(least(attempts, 10)) seconds), returned, or unlocked by the 4-hour sweep.',
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'the backoff `exp(least(attempts, 10)) * interval \'1 second\'` (failJobs.ts:123) is a float rounded to microseconds: known only by its bounds, e seconds from attempt 1 and e^10 seconds up to attempt 10'},
    {gap: 'other', blocks: 'part', detail: 'named job queues (the queue row locked with the job), priorities, task ids and forbidden flags only choose which job a fetch takes; admin functions (complete_jobs, permanently_fail_jobs, reschedule_jobs) and add_job\'s job_key replace are not modelled'},
  ],
  laws: [
    invariant(w, w.law('a job is attempted at most max_attempts times', ({attempts, maxAttempts}) => attempts.atMost(maxAttempts)),
      'safety', 'docs', 'website/docs/library/add-job.md:34 "`maxAttempts`: the maximum number of attempts we\'ll give the job"'),
    stepLaw(w, w.stepLaw('a failed attempt waits at least e seconds', ({now}, after) => after.runAt.atLeast(now.plus(2718282)), ({fails}) => fails),
      'step', 'docs', 'website/docs/exponential-backoff.md:6-7 "We currently use the formula `exp(least(10, attempt))` to determine the delays between attempts"; :21 attempt 1: 2.718282 s'),
    stepLaw(w, w.stepLaw('a failed attempt waits at most e^10 seconds', ({now, runAt}, after) => after.runAt.atMost(max(now, runAt).plus(22026465795)), ({fails}) => fails),
      'step', 'docs', 'website/docs/exponential-backoff.md:9-10 "after ~4 hours attempts will be made every ~6 hours"'),
    stepLaw(w, w.stepLaw('a completed job is never run again', ({attempts}, after) => after.deleted.and(after.attempts.eq(attempts)), ({deleted}) => deleted),
      'step', 'inferred', 'completeJobs.ts:55-56 a completed job is deleted'),
    stepLaw(w, w.stepLaw('only the lock holder or the 4-hour sweep unlocks a job', ({op, pool, lockedBy}, after) => after.lockedBy.gt(0).or(after.deleted, op.is('reset'), pool.eq(lockedBy)), ({lockedBy, deleted}) => lockedBy.gt(0).and(deleted.not())),
      'access', 'docs', 'failJobs.ts:126 and returnJobs.ts:62 `locked_by = $poolId`; website/docs/error-handling.md:32-34 locks of a crashed worker are swept after 4 hours'),
    leadsTo(w, w.leadsTo('a locked job is eventually unlocked', {
      from: ({lockedBy, deleted}) => lockedBy.gt(0).and(deleted.not()),
      to: ({lockedBy, deleted}) => lockedBy.eq(0).or(deleted),
      helpful: ({lockedAt, last}) => ({op: 4, pool: 1, now: max(lockedAt.plus(fourHours + 1), last)}),
    }), 'docs', 'website/docs/error-handling.md:33-34 "Every 8-10 minutes a worker will sweep for jobs that have been locked for more than 4 hours and will make them available to be processed again automatically."'),
  ],
}, {
  id: 'queue/pg-boss/retry',
  domain: 'queue',
  source: pgbCite('src/plans.ts', '3331-3420', 'failJobsBody'),
  also: [
    pgbCite('src/plans.ts', '2606-2826', 'fetchNextJob'), pgbCite('src/plans.ts', '2828-2897', 'attemptFence, completeJobsUpdate'),
    pgbCite('src/plans.ts', '2986-3035', 'cancelJobs, resumeJobs'), pgbCite('src/plans.ts', '3235-3285', 'failJobsById, failJobsByTimeout'),
    pgbCite('src/plans.ts', '4140-4155', 'retryJobs'), pgbCite('docs/api/jobs.md', '30-47', 'Retry options'),
  ],
  summary: 'One job: fetched when due (retry_count + 1 after its first claim), completed, failed by a worker (fenced by the attempt it fetched) or by expiry into retry while retry_count < retry_limit (start_after pushed by a fixed or capped jittered backoff) else failed; cancel, resume and retry by hand.',
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'the backoff\'s jitter, `2 ^ LEAST(16, retry_count + 1) / 2 * random()` seconds (plans.ts:3401-3404), is a float the rule takes as an input (`wait`); only LEAST(retry_delay_max, it) is said'},
    {gap: 'nonlinear', blocks: 'part', detail: 'GREATEST(retry_delay, 1) times 2^LEAST(16, retry_count + 1): a param times a function of the state, not constrained on `wait`'},
    {gap: 'other', blocks: 'part', detail: 'queue policies (singleton, stately, groups, key_strict_fifo), dependencies, heartbeats, dead letters and restore() are not modelled'},
  ],
  laws: [
    // Stated first for every run ('a job is claimed at most retryLimit + 1 times'), this law was refuted: fetch, cancel,
    // resume, fetch claims a job twice at retry_limit 0 (resumeJobs puts it back to created, and the claim after it
    // counts; plans.ts:2817, :3011-3035). A law error: resume() is a deliberate re-run by hand, not a retry.
    invariant(q, q.law('without a resume, a job is claimed at most retryLimit + 1 times', ({claims, retryLimit, resumed}) => resumed.or(claims.atMost(retryLimit.plus(1)))),
      'safety', 'docs', 'docs/api/jobs.md:33-35 "retryLimit, int. Default: 2. Number of retries to complete a job."'),
    stepLaw(q, q.stepLaw('a completed job is never retried', (_, after) => after.st.is('completed'), ({st}) => st.is('completed')),
      'step', 'inferred', 'plans.ts:2994, :3236 cancel and fail only `state < completed`; resume only cancelled, retry only failed'),
    stepLaw(q, q.stepLaw('a job with no retries left fails for good', (_, after) => after.st.is('failed'), ({failsNow, retryCount, retryLimit}) => failsNow.and(retryCount.atLeast(retryLimit))),
      'step', 'docs', 'plans.ts:3334-3337 `WHEN retry_count < retry_limit THEN retry ELSE failed`'),
    stepLaw(q, q.stepLaw('a backoff retry waits at most retryDelayMax', ({now, retryDelayMax}, after) => after.startAfter.atMost(now.plus(retryDelayMax.times(us))), ({failsNow, retryCount, retryLimit, retryBackoff, hasDelayMax}) => failsNow.and(retryCount.lt(retryLimit), retryBackoff, hasDelayMax)),
      'step', 'docs', 'docs/api/jobs.md:45-47 "retryDelayMax, int. Default: no limit. Maximum delay between retries of failed jobs, in seconds. Only used when retryBackoff is true."'),
    stepLaw(q, q.stepLaw('a stale settle never touches a newer attempt', ({st, retryCount}, after) => same(after.st, st).and(after.retryCount.eq(retryCount)), ({op, fenced, rc, retryCount}) => op.is('complete').or(op.is('fail')).and(fenced, rc.eq(retryCount).not())),
      'access', 'docs', 'plans.ts:2828-2834 "Every claim increments retry_count (fetchNextJob), so the value a worker fetched names its attempt ... a job whose retry_count has moved on is left alone"'),
    leadsTo(q, q.leadsTo('an expired active job is failed or retried', {
      from: ({st}) => st.is('active'),
      to: ({st}) => st.is('active').not(),
      helpful: ({startedOn, expireSeconds, last}) => ({op: 3, now: max(startedOn.plus(expireSeconds.times(us)).plus(1), last)}),
    }), 'docs', 'plans.ts:3244-3247 failJobsByTimeout: `state = active AND (started_on + expire_seconds * interval 1s) < job_now()`'),
  ],
}, {
  id: 'queue/p-retry/pRetry',
  domain: 'queue',
  source: prCite('index.js', '66-265', 'pRetry'),
  also: [prCite('readme.md', '135-205', 'options')],
  summary: 'One pRetry call: each failed attempt consumes a retry (or not, by shouldConsumeRetry) and waits min(minTimeout · factor^consumed, maxTimeout), capped by the time left of maxRetryTime; AbortError, a plain TypeError, shouldRetry, no retries or no time left reject.',
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'randomize (index.js:68: Math.random() + 1) and a factor that is not an integer are not modelled; integer factors without randomize, the default, are'},
    {gap: 'async', blocks: 'part', detail: 'an AbortSignal aborting during an attempt or a wait (:89-106, :185-195) is not modelled'},
  ],
  laws: [
    invariant(r, r.law('the retries consumed never exceed retries', ({consumed, retries, forever}) => forever.or(consumed.atMost(retries))),
      'safety', 'docs', 'readme.md:162-167 "retries: The maximum amount of times to retry the operation."'),
    stepLaw(r, r.stepLaw('no retry waits longer than maxTimeout', ({maxTimeout}, after) => after.waited.atMost(maxTimeout), ({consumes, hasMaxTimeout}) => consumes.and(hasMaxTimeout)),
      'step', 'docs', 'readme.md:185-190 "maxTimeout: The maximum number of milliseconds between two retries."'),
    stepLaw(r, r.stepLaw('no retry waits past maxRetryTime', ({maxRetryTime}, after) => after.resumeAt.atMost(maxRetryTime), ({consumes, hasMaxRetryTime}) => consumes.and(hasMaxRetryTime)),
      'step', 'docs', 'readme.md:199-205 "maxRetryTime: The maximum time (in milliseconds) that the retried operation is allowed to run."'),
    stepLaw(r, r.stepLaw('an uncapped retry waits at least minTimeout', ({minTimeout}, after) => after.waited.atLeast(minTimeout), ({consumes, hasMaxTimeout, hasMaxRetryTime}) => consumes.and(hasMaxTimeout.not(), hasMaxRetryTime.not())),
      'step', 'docs', 'readme.md:176-183 "minTimeout: The number of milliseconds before starting the first retry."; the delay grows by `factor`'),
    stepLaw(r, r.stepLaw('an AbortError stops retrying', (_, after) => after.st.is('rejected'), ({st, ok, abort}) => st.is('running').and(ok.not(), abort)),
      'step', 'docs', 'index.js:114-116 `if (normalizedError instanceof AbortError) throw normalizedError.originalError`'),
    stepLaw(r, r.stepLaw('a settled call is never attempted again', ({attempts}, after) => after.attempts.eq(attempts), ({st}) => st.is('running').not()),
      'step', 'inferred', 'index.js:249 the result is returned, :137, :161-182 the error thrown: the loop ends'),
    leadsTo(r, r.leadsTo('with finite retries every call settles', {
      from: ({st, forever}) => st.is('running').and(forever.not()),
      to: ({st}) => st.is('running').not(),
      helpful: ({resumeAt}) => ({ok: 0, abort: 0, typeError: 0, consume: 1, retry: 1, now: resumeAt}),
    }), 'docs', 'readme.md:162-167 retries "The maximum amount of times to retry the operation"'),
  ],
}]
