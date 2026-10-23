// better-auth v1.7.12, the two-factor OTP: sendOTP and verifyOTP (packages/better-auth/src/plugins/two-factor/otp/index.ts)
// with the per-account lockout they share with the other factors (two-factor/verify-two-factor.ts) and the
// verification store's consume (db/internal-adapter.ts consumeVerificationValue). MIT, (c) Better Auth contributors.
// https://github.com/better-auth/better-auth/tree/f4260a95cddc0a7640f57c37cf624de019df324f/packages/better-auth/src
//
// Mapping:
// - One challenge (the identifier `2fa-otp-${key}`) and one account. consumeVerificationValue takes the latest row for
//   the identifier and deletes every row (internal-adapter.ts:1482-1517), so the latest row is all there is: `row`.
// - Time: Date.now() / new Date() (otp/index.ts:223, internal-adapter.ts:1541, verify-two-factor.ts:244, :295) is
//   `now: nat`, in ms, sent in with each request.
// - The OTP: generateRandomString (otp/index.ts:218) is the input `code` of a send; storeOTP / decryptOrHashForComparison
//   and constantTimeEqual (:363-370) compare the stored code with the guess, which is equality of the codes.
// - `lockOn`: the account-level lockout applies (verify-two-factor.ts:215-229 `enabled`, a sign-in, otp/index.ts:325-333
//   a twoFactor row exists); a param, since none of the three changes over the run.
import {bool, nat, no, oneOf, rule, when, yes} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'better-auth/better-auth', commit: 'f4260a95cddc0a7640f57c37cf624de019df324f', licence: 'MIT', author: 'Better Auth contributors', language: 'TypeScript'}
const pkg = 'packages/better-auth/src'

export const twoFactorOTP = () => rule('better-auth two-factor OTP')
  // otp/index.ts:124 period in ms; :351 `options?.allowedAttempts || 5`; verify-two-factor.ts:221-227
  // maxFailedAttempts, durationSeconds * 1000.
  .params({period: nat, allowedOpt: nat, lockOn: bool, maxFailed: nat, durationMs: nat})
  .inputs({op: oneOf('send', 'verify'), code: nat, guess: nat, now: nat})
  // `row`: the latest verification row {code, attempts, exp} (`has` for its presence: `rowCode`, `attempts`, `exp`).
  // twoFactor.failedVerificationCount (`failed`) and lockedUntil (`isLocked` for non-null, `lockedUntil`). Ghosts:
  // `compared`, the guesses compared with the current code since it was sent; `accepted`, how often it was accepted;
  // `ok`, whether the last verify succeeded.
  .state({has: bool.from(false), rowCode: 0, attempts: 0, exp: 0, failed: 0, isLocked: bool.from(false), lockedUntil: 0, compared: 0, accepted: 0, ok: bool.from(false)})
  .flags(({op, now, lockOn, isLocked, lockedUntil}) => ({
    // verify-two-factor.ts:236-262 assertTwoFactorNotLocked: throws while lockedUntil > now, clears an expired lock.
    blocked: op.is('verify').and(lockOn, isLocked, now.lt(lockedUntil)),
    unlocks: op.is('verify').and(lockOn, isLocked, lockedUntil.atMost(now)),
  }))
  .flags(({op, now, blocked, has, exp, attempts, allowedOpt, rowCode, guess}) => {
    // otp/index.ts:334-349 consume: the row is deleted whatever follows; none, or one past its expiry
    // (internal-adapter.ts:1541 `consumed.expiresAt < new Date()`), is OTP_HAS_EXPIRED.
    const consumes = op.is('verify').and(blocked.not())
    const live = consumes.and(has, now.atMost(exp))
    // otp/index.ts:351-359 the attempt budget.
    const within = live.and(attempts.lt(when(allowedOpt.eq(0), 5, allowedOpt)))
    return {consumes, compares: within, right: within.and(guess.eq(rowCode)), wrong: within.and(guess.eq(rowCode).not())}
  })
  .step(({op, code, now, period, lockOn, maxFailed, durationMs, has, rowCode, attempts, exp, failed, isLocked, lockedUntil, compared, accepted, ok, unlocks, consumes, compares, right, wrong}) => {
    const sends = op.is('send')
    // verify-two-factor.ts:254-261 an expired lock is cleared (count 0, lockedUntil null) before anything else.
    const f0 = when(unlocks, 0, failed)
    // :271-298 recordTwoFactorFailure: count + 1, and lockedUntil = now + duration once the count reaches the max;
    // :307-319 resetTwoFactorFailures on a right code.
    const f1 = f0.plus(1), locks = lockOn.and(wrong, f1.atLeast(maxFailed))
    return {
      // otp/index.ts:220-224 a send writes a fresh row {code, 0, now + period}; a verify consumes the row (deleted);
      // :411-415 a wrong guess within budget writes it again with the count + 1 and the original expiry.
      has: when(sends, yes, when(consumes, wrong, has)),
      rowCode: when(sends, code, rowCode),
      attempts: when(sends, 0, when(wrong, attempts.plus(1), attempts)),
      exp: when(sends, now.plus(period), exp),
      failed: when(lockOn.and(wrong), f1, when(lockOn.and(right), 0, f0)),
      isLocked: when(locks, yes, when(lockOn.and(right).or(unlocks), no, isLocked)),
      lockedUntil: when(locks, now.plus(durationMs), when(lockOn.and(right).or(unlocks), 0, lockedUntil)),
      compared: when(sends, 0, when(compares, compared.plus(1), compared)),
      accepted: when(sends, 0, when(right, accepted.plus(1), accepted)),
      ok: when(op.is('verify'), right, ok),
    }
  })

const r = twoFactorOTP()
export const items: RealItem[] = [{
  id: 'auth/better-auth/twoFactorOTP',
  domain: 'auth',
  source: {...src, path: `${pkg}/plugins/two-factor/otp/index.ts`, lines: '207-420', export: 'otp2fa'},
  also: [{...src, path: `${pkg}/plugins/two-factor/verify-two-factor.ts`, lines: '215-319', export: 'assertTwoFactorNotLocked, recordTwoFactorFailure, resetTwoFactorFailures'},
    {...src, path: `${pkg}/db/internal-adapter.ts`, lines: '1425-1543', export: 'consumeVerificationValue'}],
  summary: 'A one-time code per challenge, consumed on every try: wrong guesses re-arm it with one more attempt counted until the budget is spent; expired codes are refused; failures also count toward a per-account lock that blocks every factor until it lapses.',
  expressible: 'partial',
  gaps: [
    {gap: 'external', blocks: 'part', detail: 'the store\'s ordering: consume takes the latest row by createdAt (internal-adapter.ts:1487-1492), a Date in ms, so two sends in one ms leave the row it takes to the database; the rule keeps the last send'},
  ],
  laws: [
    invariant(r, r.law('at most allowedAttempts guesses are compared per code', ({compared, allowedOpt}) => compared.atMost(when(allowedOpt.eq(0), 5, allowedOpt))),
      'safety', 'docs', 'otp/index.ts:68-72 "The number of allowed attempts for the OTP"'),
    invariant(r, r.law('a code is accepted at most once', ({accepted}) => accepted.atMost(1)),
      'safety', 'docs', 'otp/index.ts:375 "Leave the row consumed: a valid OTP is single-use."'),
    stepLaw(r, r.stepLaw('an expired code is never accepted', ({now, exp}) => now.atMost(exp), ({right}) => right),
      'safety', 'docs', 'internal-adapter.ts:1417-1419 "Rows past their expiresAt are treated as already invalid"'),
    stepLaw(r, r.stepLaw('a locked account accepts no code', (_, after) => after.ok.not(), ({op, lockOn, isLocked, lockedUntil, now}) => op.is('verify').and(lockOn, isLocked, now.lt(lockedUntil))),
      'access', 'docs', 'verify-two-factor.ts:232-234 "Reject the verification when the account is locked"'),
    invariant(r, r.law('maxFailedAttempts failures lock the account', ({lockOn, failed, maxFailed, isLocked}) => lockOn.and(maxFailed.atLeast(1), failed.atLeast(maxFailed)).implies(isLocked)),
      'safety', 'docs', 'verify-two-factor.ts:266-268 "lock the account once the budget is spent"'),
    stepLaw(r, r.stepLaw('a right code clears the account\'s failures', (_, after) => after.failed.eq(0).and(after.isLocked.not()), ({lockOn, right}) => lockOn.and(right)),
      'step', 'docs', 'verify-two-factor.ts:301-303 "Clear the account-level failure budget after a successful verification"'),
  ],
}]
