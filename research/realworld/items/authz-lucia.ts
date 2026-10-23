// Lucia v3.2.2 (lucia-auth/lucia, branch v3), the session core: createSession, validateSession (with its expiry
// extension once half the session's life has passed), invalidateSession and invalidateUserSessions
// (packages/lucia/src/core.ts, with date.ts). MIT, (c) pilcrowOnPaper and the Lucia contributors.
// https://github.com/lucia-auth/lucia/tree/fc016ca8deb62b1925298ac2625254afa5ae1531/packages/lucia/src
//
// Mapping:
// - Time: Date.now() (date.ts:39-45) is `now: nat`, in ms, sent in with each request.
// - The adapter (database.ts:7-17) is the store: a map from session id to {live, user, exp}. Session ids are random
//   (crypto.ts generateIdFromEntropySize(25), core.ts:163): the n-th created session gets id n (`next`), so a new id
//   is never one already used. A custom `options.sessionId` (core.ts:163) is left out (see gaps).
// - `userExists`: whether getSessionAndUser's join finds the session's user (core.ts:122, :126), from the users table.
// - Dates: `expiresAt - sessionExpiresIn / 2` (core.ts:134-136) is new Date(x) of a value that is a whole number or a
//   half; new Date truncates to whole ms, so `now < activePeriodExpirationDate` is 2 * now + 2 <= 2 * expiresAt - E
//   for integers (and false when 2 * expiresAt < E, where the date is not after 0): exact.
import {bool, forall, nat, no, oneOf, record, rule, when, yes} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'lucia-auth/lucia', commit: 'fc016ca8deb62b1925298ac2625254afa5ae1531', licence: 'MIT', author: 'pilcrowOnPaper (lucia-auth)', language: 'TypeScript'}

export const Session = record({live: bool, user: nat, exp: nat})
export const lucia = () => rule('lucia v3 sessions')
  // core.ts:79 sessionExpiresIn (30 days by default), in ms.
  .params({E: nat})
  .inputs({op: oneOf('create', 'validate', 'invalidate', 'invalidateUser'), sid: nat, user: nat, now: nat, userExists: bool})
  // `next`: the id the next created session gets. Ghosts: `clock`, the latest time seen; `valid`, `fresh`: what the
  // last validateSession returned (a session or null; Session.fresh). `Ended`: whether the adapter deleted a live
  // session at that id (an observed effect: deleteSession / deleteUserSessions on it).
  .state({next: 0, clock: 0, valid: bool.from(false), fresh: bool.from(false)})
  .maps({Sess: Session.from({live: false, user: 0, exp: 0}), Ended: bool.from(false)})
  .flags(({op, sid, now, userExists, E, Sess}) => {
    const s = Sess.at(sid)
    return {
      creates: op.is('create'),
      // core.ts:122-125 no session: null, nothing changes.
      looks: op.is('validate').and(s.live),
      // core.ts:126-129 no user, :130-133 expired (date.ts:39-41 `Date.now() < date.getTime()`): delete, null.
      drops: op.is('validate').and(s.live, userExists.not().or(s.exp.atMost(now))),
      // core.ts:144 not within the active period: extend.
      extends: op.is('validate').and(s.live, userExists, now.lt(s.exp), now.times(2).plus(2).atMost(s.exp.times(2).minus(E)).not()),
      // core.ts:181-183 adapter.deleteSession.
      kills: op.is('invalidate').and(s.live),
      // core.ts:185-187 adapter.deleteUserSessions.
      killsUser: op.is('invalidateUser'),
    }
  })
  .step(({op, sid, user, now, E, next, clock, valid, fresh, Sess, Ended, creates, looks, drops, extends: ext, kills, killsUser}) => ({
    next: when(creates, next.plus(1), next),
    clock: when(now.gt(clock), now, clock),
    // core.ts:149-153 a session is returned: found, a user, unexpired.
    valid: when(op.is('validate'), looks.and(drops.not()), valid),
    fresh: when(op.is('validate'), ext, fresh),
    Sess: Sess.each(k => {
      const s = Sess.at(k)
      const gone = killsUser.and(s.user.eq(user)).or(k.eq(sid).and(drops.or(kills)))
      // core.ts:163-170 createDate(sessionExpiresIn): now + E; core.ts:146-147 the extension writes now + E too.
      return when(creates.and(k.eq(next)), {live: yes, user, exp: now.plus(E)},
        when(gone, {live: no, user: s.user, exp: s.exp},
          when(ext.and(k.eq(sid)), {live: s.live, user: s.user, exp: now.plus(E)}, s)))
    }),
    Ended: Ended.each(k => Ended.at(k).or(Sess.at(k).live.and(killsUser.and(Sess.at(k).user.eq(user)).or(k.eq(sid).and(drops.or(kills)))))),
  }))

const r = lucia()
export const items: RealItem[] = [{
  id: 'auth/lucia/validateSession',
  domain: 'auth',
  source: {...src, path: 'packages/lucia/src/core.ts', lines: '119-191', export: 'Lucia'},
  also: [{...src, path: 'packages/lucia/src/date.ts', lines: '1-46', export: 'TimeSpan, isWithinExpirationDate, createDate'}, {...src, path: 'packages/lucia/src/database.ts', lines: '7-17', export: 'Adapter'}],
  summary: 'Database sessions: created with a fixed lifetime, validated (deleted when expired or their user is gone, extended to a full lifetime once past half of it), invalidated one by one or per user.',
  expressible: 'partial',
  gaps: [
    {gap: 'external', blocks: 'part', detail: 'deleteExpiredSessions (core.ts:189-191) is the adapter\'s own query (each adapter package writes its SQL); left out. A caller-chosen options.sessionId (core.ts:163) is left out too: the adapter\'s insert decides what a duplicate id does'},
  ],
  laws: [
    stepLaw(r, r.stepLaw('an expired session is never validated', ({sid, now, Sess}) => now.lt(Sess.at(sid).exp), ({op, looks, drops}) => op.is('validate').and(looks, drops.not())),
      'safety', 'docs', 'core.ts:130-133 `if (!isWithinExpirationDate(databaseSession.expiresAt))` delete and return null'),
    stepLaw(r, r.stepLaw('validation never shortens a session', ({sid, Sess}, after) => Sess.at(sid).exp.atMost(after.Sess.at(sid).exp), ({op, looks, drops}) => op.is('validate').and(looks, drops.not())),
      'step', 'docs', 'Lucia v3 docs: sessions are "extended" when validated in the second half of their life'),
    invariant(r, r.law('no session outlives sessionExpiresIn past the latest time seen', ({Sess, clock, E}) => forall(k => Sess.at(k).live.implies(Sess.at(k).exp.atMost(clock.plus(E))))),
      'safety', 'docs', 'core.ts:79, :146, :164 every expiry written is createDate(this.sessionExpiresIn): now + sessionExpiresIn'),
    invariant(r, r.law('a deleted session never comes back', ({Sess, Ended}) => forall(k => Ended.at(k).implies(Sess.at(k).live.not()))),
      'safety', 'inferred', 'core.ts:181-187 invalidateSession / invalidateUserSessions delete it; ids are random, never reissued'),
    stepLaw(r, r.stepLaw('invalidateUserSessions ends every session of the user', ({user}, after) => forall(k => after.Sess.at(k).user.eq(user).implies(after.Sess.at(k).live.not())), ({op}) => op.is('invalidateUser')),
      'step', 'docs', 'Lucia docs "invalidateUserSessions(): Invalidates all sessions of the user"'),
  ],
}]
