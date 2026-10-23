// Keycloak 26.8.1, brute-force detection: DefaultBruteForceProtector (failure, success, isTemporarilyDisabled,
// isPermanentlyLockedOut) with the JPA UserLoginFailureAdapter it writes through. Apache-2.0, (c) Red Hat, Inc. and
// the Keycloak authors (file author Bill Burke).
// https://github.com/keycloak/keycloak/tree/24ed1dadf3f246a555adb6d3d4a99e9b3003fb3b/services/src/main/java/org/keycloak/services/managers
//
// Mapping:
// - One user of one realm: every UserLoginFailureModel is per (realm, user) (:184-187) and no step reads another's.
// - Time: Time.currentTimeMillis() (:265 for a failure, :275 for a check) is `now: nat`, in ms, sent in with each
//   request; `now / 1000` (Java long division of a non-negative value: the floor) is divBy(1000).
// - The realm's settings are params. Java ints and longs are taken as naturals: the settings are non-negative, and
//   `deltaTime` (:95, which may be negative when the clock goes back) enters only through `> 0` and `< quick` tests,
//   written for the two signs. waitSeconds (:112, :114) is <= 0 exactly when its natural (truncated) form is 0.
// - permanentUserLockOut (:167-181) disables the user (`enabled`) and sets the reason (`permReason`); the user exists.
import {type Cond, type Term, bool, divBy, fn, forall, min, nat, no, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'keycloak/keycloak', commit: '24ed1dadf3f246a555adb6d3d4a99e9b3003fb3b', licence: 'Apache-2.0', author: 'Keycloak authors (Bill Burke)', language: 'Java'}
const INT_MAX = 2147483647

// x / d for d >= 1 (Java long division of non-negatives), known by its defining facts.
const floorDiv = fn(2, (x: number, d: number) => Math.floor(x / d), {facts: f => ({
  'd * (x / d) <= x < d * (x / d + 1)': forall((x, d) => d.atLeast(1).implies(f(x, d).mul(d).atMost(x).and(x.lt(f(x, d).plus(1).mul(d))))),
})})


// :101 clearFailures (UserLoginFailureAdapter.java:99-110) zeroes numFailures (and notBefore, numTemporaryLockouts,
// lastFailure) when the last failure is stale; :106 incrementFailures.
const count1 = ({stale, exists, fails}: {stale: Cond, exists: Cond, fails: Term}) => when(stale.and(exists), 0, fails).plus(1)
// :110-116 waitSeconds (0 for permanent-only lockout; MULTIPLE: inc * (n / factor); LINEAR: inc * (1 + n - factor)).
const wait = (env: {stale: Cond, exists: Cond, fails: Term, perm: Cond, maxTemp: Term, multiple: Cond, inc: Term, factor: Term, floorDiv: (x: Term, d: Term) => Term}) => {
  const n1 = count1(env)
  return when(env.perm.and(env.maxTemp.eq(0)), 0, when(env.multiple, env.inc.mul(env.floorDiv(n1, env.factor)), env.inc.mul(n1.plus(1).minus(env.factor))))
}

export const bruteForce = () => rule('keycloak DefaultBruteForceProtector')
  .params({
    // RealmModel: isPermanentLockout, getMaxTemporaryLockouts, getBruteForceStrategy (MULTIPLE, the default, or
    // LINEAR), getWaitIncrementSeconds, getFailureFactor, getMaxDeltaTimeSeconds, getQuickLoginCheckMilliSeconds,
    // getMinimumQuickLoginWaitSeconds, getMaxFailureWaitSeconds, getMaxSecondaryAuthFailures.
    perm: bool, maxTemp: nat, multiple: bool, inc: nat, factor: nat, maxDeltaSec: nat, quickMs: nat, minQuickSec: nat, maxWaitSec: nat, maxSec: nat,
  })
  // :112 divides by the failure factor: zero throws ArithmeticException under MULTIPLE; taken positive.
  .pre(({factor}) => factor.atLeast(1))
  // One call: failedLogin (:228-239), successfulLogin (:242-249), each with its authentication categories: none (null),
  // a set with OTP, a set with password or recovery codes but not OTP, or a set disjoint from those three.
  .inputs({op: oneOf('failure', 'success'), cat: oneOf('none', 'password', 'otp', 'other'), now: nat})
  .fns({sec: divBy(1000), floorDiv})
  // LoginFailureEntity: whether it exists, numFailures, lastFailure (ms), failedLoginNotBefore (s), numTemporaryLockouts,
  // numSecondaryAuthFailures; the user's enabled flag and DISABLED_REASON = permanent lockout.
  // Ghost `nowSec`: now / 1000 of the last request (the second :137 and :275 compare against).
  .state({nowSec: 0, exists: bool.from(false), fails: 0, last: 0, notBefore: 0, temps: 0, secFails: 0, enabled: bool.from(true), permReason: bool.from(false)})
  .flags(({op, cat, now, last, perm, maxTemp, maxDeltaSec, quickMs}) => ({
    // :229 a failure is skipped only for categories disjoint from the allowed ones; :243 a success also for null.
    fails1: op.is('failure').and(cat.is('other').not()),
    succeeds: op.is('success').and(cat.is('password').or(cat.is('otp'))),
    // :98-103 clear failures when the last one is more than maxDelta ago (and not permanent-only lockout).
    stale: perm.and(maxTemp.eq(0)).not().and(last.gt(0), now.gt(last), now.minus(last).gt(maxDeltaSec.times(1000))),
    // :123 `last > 0 && deltaTime < quickLoginCheckMilliSeconds` (deltaTime negative when the clock went back).
    quick0: last.gt(0).and(now.lt(last).or(now.minus(last).lt(quickMs))),
  }))
  .flags(env => ({
    // :121-128 quick login: only when waitSeconds <= 0.
    quick: env.fails1.and(wait(env).eq(0), env.quick0),
  }))
  .step(env => {
    const {fails1, succeeds, stale, quick, now, cat, perm, maxTemp, factor, minQuickSec, maxWaitSec, maxSec, sec, exists, fails, last, notBefore, temps, secFails, enabled, permReason} = env
    const clear = stale.and(exists), n1 = count1(env), w = wait(env)
    const w1 = when(quick, minQuickSec, w)
    // :129-132 capped at maxFailureWaitSeconds unless permanent-only lockout.
    const w2 = when(perm.not().or(maxTemp.gt(0)), min(maxWaitSec, w1), w1)
    const locking = fails1.and(w1.gt(0))
    // :133-135 a temporary lockout is counted unless it is a quick-login one.
    const t1 = when(clear, 0, temps).plus(when(locking.and(quick.not()), 1, 0))
    // :136-143 notBefore = min(now / 1000 + wait, Integer.MAX_VALUE).
    const setsNb = locking.and(quick.or(perm.not(), t1.atMost(maxTemp)))
    const nb = min(sec(now).plus(w2), INT_MAX)
    // :146-155 OTP failures, a permanent lockout past maxSecondaryAuthFailures.
    const s1 = secFails.plus(when(cat.is('otp'), 1, 0))
    const otpLock = cat.is('otp').and(maxSec.gt(0), s1.gt(maxSec))
    // :157-164 permanent lockout.
    const permLock = perm.and(t1.gt(maxTemp).or(maxTemp.eq(0).and(n1.atLeast(factor))))
    const disable = fails1.and(otpLock.or(permLock))
    // :211-225 success: nothing without a failure record; clearFailures, and the OTP count too with the OTP category.
    const ok = succeeds.and(exists)
    return {
      nowSec: sec(now),
      exists: exists.or(fails1),
      fails: when(fails1, n1, when(ok, 0, fails)),
      last: when(fails1, now, when(ok, 0, last)),
      notBefore: when(fails1, when(setsNb, nb, when(clear, 0, notBefore)), when(ok, 0, notBefore)),
      temps: when(fails1, t1, when(ok, 0, temps)),
      secFails: when(fails1, s1, when(ok.and(cat.is('otp')), 0, secFails)),
      enabled: when(disable, no, enabled),
      permReason: permReason.or(disable),
    }
  })

const r = bruteForce()
const cite = (lines: string) => ({...src, path: 'services/src/main/java/org/keycloak/services/managers/DefaultBruteForceProtector.java', lines, export: 'DefaultBruteForceProtector'})
export const items: RealItem[] = [{
  id: 'auth/keycloak/bruteForceProtector',
  domain: 'auth',
  source: cite('83-298'),
  also: [{...src, path: 'model/jpa/src/main/java/org/keycloak/loginfailures/jpa/UserLoginFailureAdapter.java', lines: '66-154', export: 'UserLoginFailureAdapter', language: 'Java'}],
  summary: 'Counts failed logins per user: past the failure factor the user is temporarily disabled for a growing wait (multiple or linear), a quick retry gets a minimum wait, too many temporary lockouts or OTP failures disable the user permanently; a success clears the counts.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'failedLogin and successfulLogin hand the update to a single "bruteforce" executor thread (:251-268), so a check may run before an earlier failure is recorded; the rule records each failure at once'},
  ],
  laws: [
    stepLaw(r, r.stepLaw('past the failure factor, a failure disables the user at once', (_, after) => after.nowSec.lt(after.notBefore),
      env => env.fails1.and(env.perm.not(), env.inc.atLeast(1), env.maxWaitSec.atLeast(1), count1(env).atLeast(env.factor))),
      'safety', 'docs', 'Keycloak docs (brute force, temporary lockout): "a user is temporarily disabled ... after the number of login failures reaches the Failure Factor"'),
    stepLaw(r, r.stepLaw('a temporary lockout waits at most maxFailureWaitSeconds', ({maxWaitSec, notBefore}, after) => after.notBefore.atMost(after.nowSec.plus(maxWaitSec)).or(after.notBefore.eq(notBefore)),
      ({fails1, perm}) => fails1.and(perm.not())),
      'safety', 'docs', ':131 `waitSeconds = Math.min(realm.getMaxFailureWaitSeconds(), waitSeconds)`; docs "Max Wait: the maximum time a user is temporarily disabled"'),
    invariant(r, r.law('too many OTP failures disable the user', ({maxSec, secFails, enabled}) => maxSec.gt(0).and(secFails.gt(maxSec)).implies(enabled.not())),
      'safety', 'docs', ':151-153 "permanently lock user account anyway" when numSecondaryAuthFailures > maxSecondaryAuthFailures'),
    invariant(r, r.law('with permanent lockout, too many temporary lockouts disable the user', ({perm, temps, maxTemp, enabled}) => perm.and(temps.gt(maxTemp)).implies(enabled.not())),
      'safety', 'docs', ':161-163 numTemporaryLockouts > maxTemporaryLockouts: permanentUserLockOut'),
    stepLaw(r, r.stepLaw('a successful login clears the failure count', (_, after) => after.fails.eq(0).and(after.notBefore.eq(0)), ({succeeds}) => succeeds),
      'step', 'docs', ':218-224 "clearing primary failures"'),
    stepLaw(r, r.stepLaw('a permanent lockout is never lifted by a login', (_, after) => after.enabled.not(), ({enabled}) => enabled.not()),
      'step', 'docs', ':167-181 permanentUserLockOut disables the user; only an administrator re-enables (cleanUpPermanentLockout, :301-309)'),
  ],
}]
