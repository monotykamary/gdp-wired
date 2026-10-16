// Access control and identity: role grants, login lockout, one-time tokens, API quotas, reset-email rate limits,
// session and step-up decisions, attribute-based access, delegation that only narrows, a key rotation sweep.
import {type Bool, type Choice, type Maybe, type Term, bool, count, forall, loop, maybe, min, nat, no, oneOf, relation, rule, upTo, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// Role grants: a user is promoted to admin only if already a member, and removing a member removes their admin role
// with it. Each map is written once per step, at the request's user.
const roles = rule('role grants')
  .inputs({op: oneOf('addMember', 'addAdmin', 'removeMember', 'removeAdmin'), user: nat})
  .maps({Member: 0, Admin: 0})
  .flags(({op, user, Member}) => ({promote: op.is('addAdmin').and(Member.at(user).eq(1))}))
  .step(({op, user, promote, Member, Admin}) => ({
    Member: Member.set(user, when(op.is('addMember'), 1, when(op.is('removeMember'), 0, Member.at(user)))),
    Admin: Admin.set(user, when(promote, 1, when(op.is('removeAdmin').or(op.is('removeMember')), 0, Admin.at(user)))),
  }))
const adminIsMember = (r: typeof roles) => r.law('every admin is a member', ({Admin, Member}) => forall(u => Admin.at(u).atMost(Member.at(u))))
const roleLaws = [adminIsMember(roles), roles.law('membership is a yes or no', ({Member}) => forall(u => Member.at(u).atMost(1)))]
const removeKeepsAdmin = roles.step(({op, user, promote, Member, Admin}) => ({
  Member: Member.set(user, when(op.is('addMember'), 1, when(op.is('removeMember'), 0, Member.at(user)))),
  Admin: Admin.set(user, when(promote, 1, when(op.is('removeAdmin'), 0, Admin.at(user)))),
}))
const promoteAnyone = roles.flags(({op}) => ({promote2: op.is('addAdmin')})).step(({op, user, promote2, Member, Admin}) => ({
  Member: Member.set(user, when(op.is('addMember'), 1, when(op.is('removeMember'), 0, Member.at(user)))),
  Admin: Admin.set(user, when(promote2, 1, when(op.is('removeAdmin').or(op.is('removeMember')), 0, Admin.at(user)))),
}))

// Lockout: each failed login while unlocked counts; the one that reaches maxFails locks the account. A success while
// unlocked clears the count; only an administrator's unlock clears a lock.
const lockout = rule('login lockout')
  .params({maxFails: nat})
  .pre(({maxFails}) => maxFails.atLeast(1))
  .inputs({kind: oneOf('fail', 'success', 'unlock')})
  .state({fails: 0, locked: 0})
  .flags(({locked}) => ({open: locked.eq(0)}))
  .step(({kind, maxFails, fails, locked, open}) => ({
    fails: when(kind.is('fail').and(open), fails.plus(1), when(kind.is('success').and(open).or(kind.is('unlock')), 0, fails)),
    locked: when(kind.is('fail').and(open, fails.plus(1).atLeast(maxFails)), 1, when(kind.is('unlock'), 0, locked)),
  }))
const lockoutLawsOf = (r: typeof lockout) => [
  r.law('an unlocked account is below maxFails', ({locked, fails, maxFails}) => locked.eq(0).implies(fails.lt(maxFails))),
  r.law('failures never pass maxFails', ({fails, maxFails}) => fails.atMost(maxFails)),
]
const lockoutOffByOne = lockout.step(({kind, maxFails, fails, locked, open}) => ({
  fails: when(kind.is('fail').and(open), fails.plus(1), when(kind.is('success').and(open).or(kind.is('unlock')), 0, fails)),
  locked: when(kind.is('fail').and(open, fails.atLeast(maxFails)), 1, when(kind.is('unlock'), 0, locked)),
}))
const lockoutCountsWhileLocked = lockout.step(({kind, maxFails, fails, locked, open}) => ({
  fails: when(kind.is('fail'), fails.plus(1), when(kind.is('success').and(open).or(kind.is('unlock')), 0, fails)),
  locked: when(kind.is('fail').and(open, fails.plus(1).atLeast(maxFails)), 1, when(kind.is('unlock'), 0, locked)),
}))

// One-time password-reset tokens: a token is issued once and redeemed at most once, and only if it was issued.
const tokens = rule('one-time reset tokens')
  .inputs({op: oneOf('issue', 'redeem'), token: nat})
  .maps({Issued: 0, Used: 0})
  .flags(({op, token, Issued, Used}) => ({
    issue: op.is('issue').and(Issued.at(token).eq(0)),
    redeem: op.is('redeem').and(Issued.at(token).eq(1), Used.at(token).eq(0)),
  }))
  .step(({token, issue, redeem, Issued, Used}) => ({Issued: Issued.bump(token, issue), Used: Used.bump(token, redeem)}))
const tokenLawsOf = (r: typeof tokens) => [
  r.law('every token is used at most as often as issued', ({Used, Issued}) => forall(t => Used.at(t).atMost(Issued.at(t)))),
  r.law('every token is issued at most once', ({Issued}) => forall(t => Issued.at(t).atMost(1))),
]
const tokenReplay = tokens.flags(({op, token, Issued}) => ({redeem2: op.is('redeem').and(Issued.at(token).eq(1))}))
  .step(({token, issue, redeem2, Issued, Used}) => ({Issued: Issued.bump(token, issue), Used: Used.bump(token, redeem2)}))
const tokenUnissued = tokens.flags(({op, token, Used}) => ({redeem3: op.is('redeem').and(Used.at(token).eq(0))}))
  .step(({token, issue, redeem3, Issued, Used}) => ({Issued: Issued.bump(token, issue), Used: Used.bump(token, redeem3)}))

// An API quota per tenant: a call is served only if the tenant's usage plus its cost stays within the quota; a refund
// gives back the cost of a failed call.
const quota = rule('API quota per tenant')
  .params({quota: nat})
  .inputs({op: oneOf('call', 'refund'), tenant: nat, cost: nat})
  .maps({Used: 0})
  .flags(({op, tenant, cost, Used, quota}) => ({served: op.is('call').and(Used.at(tenant).plus(cost).atMost(quota))}))
  .step(({op, tenant, cost, served, Used}) => ({Used: Used.set(tenant, when(served, Used.at(tenant).plus(cost), when(op.is('refund'), Used.at(tenant).minus(cost), Used.at(tenant))))}))
const quotaLawOf = (r: typeof quota) => r.law('every tenant stays within the quota', ({Used, quota}) => forall(t => Used.at(t).atMost(quota)))
const quotaChecksRemaining = quota.flags(({op, tenant, Used, quota}) => ({served2: op.is('call').and(Used.at(tenant).lt(quota))}))
  .step(({op, tenant, cost, served2, Used}) => ({Used: Used.set(tenant, when(served2, Used.at(tenant).plus(cost), when(op.is('refund'), Used.at(tenant).minus(cost), Used.at(tenant))))}))

// Reset emails per account per hour: a request for account `acct` at time t is sent only if fewer than `cap` emails
// went to that account in the hour before it (`sent`, read from the log). For any account `who`, `lastHour` sums the
// emails it got in the hour ending at now.
const resetMails = (window: (r: {t: Term}, t: Term, hour: Term) => Term) => rule('reset emails per hour')
  .params({hour: nat, cap: nat, now: nat, who: nat})
  .inputs({acct: nat, t: nat})
  .log('acct', 't')
  .sums({lastHour: (r, {now, hour, who}) => count(r.acct.eq(who).and(r.t.atMost(now), now.lt(r.t.plus(hour))))})
  .queries({sent: (r, {t, hour, acct}) => when(r.acct.eq(acct), window(r, t, hour), 0)})
  .flags(({sent, cap}) => ({send: sent.plus(1).atMost(cap)}))
  .keep(({send}) => send)
  .relations(({t, now, acct, who, lastHour, sent}) => [relation(lastHour.atMost(sent), t.atMost(now).and(acct.eq(who)))])
const mails = resetMails((r, t, hour) => count(t.lt(r.t.plus(hour))))
const mailsLawOf = (r: typeof mails) => r.law('emails to who in the hour ending at now <= cap', ({lastHour, cap}) => lastHour.atMost(cap))
const mailsShortWindow = resetMails((r, t, hour) => count(t.plus(1).lt(r.t.plus(hour))))

// Session validity: within the absolute lifetime, with known last activity within the idle window (four times longer
// with remember-me). Step-up: what an action needs, given risk, how recent the last MFA was, and the device.
const session = rule('session validity')
  .params({ttl: nat, idle: nat})
  .inputs({issuedAt: nat, now: nat, lastSeen: maybe(nat), remember: bool})
type SessionEnv = {ttl: Term, idle: Term, issuedAt: Term, now: Term, lastSeen: Maybe<Term>, remember: Bool}
const valid = ({ttl, idle, issuedAt, now, lastSeen, remember}: SessionEnv) =>
  now.lt(issuedAt.plus(ttl)).and(lastSeen.match({none: () => no, some: l => l.atMost(now).and(now.lt(l.plus(when(remember, idle.times(4), idle))))}))
const validRememberBypass = (env: SessionEnv) => env.remember.or(valid(env))
const stepUp = rule('step-up authentication')
  .params({fresh: nat})
  .inputs({action: oneOf('read', 'write', 'transfer'), risk: upTo(100), mfaAge: maybe(nat), trusted: bool})
type StepEnv = {fresh: Term, action: Choice<'read' | 'write' | 'transfer'>, risk: Term, mfaAge: Maybe<Term>, trusted: Bool}
const recent = ({fresh, mfaAge}: StepEnv) => mfaAge.match({none: () => no, some: a => a.atMost(fresh)})
const allow = (env: StepEnv) => env.action.match({
  read: () => env.risk.lt(80).or(recent(env)),
  write: () => recent(env).or(env.trusted.and(env.risk.lt(30))),
  transfer: () => recent(env).and(env.trusted),
})
const allowTrustedTransfer = (env: StepEnv) => env.action.match({
  read: () => env.risk.lt(80).or(recent(env)),
  write: () => recent(env).or(env.trusted.and(env.risk.lt(30))),
  transfer: () => recent(env).or(env.trusted),
})
const sessionDecisions = [
  session.decide('past the absolute lifetime, never valid', ({now, issuedAt, ttl}) => now.atLeast(issuedAt.plus(ttl)), env => valid(env).not()),
  session.decide('no activity on record, not valid', ({lastSeen}) => lastSeen.isNone, env => valid(env).not()),
  session.decide('without remember-me, idle past the window is invalid', ({remember, lastSeen, now, idle}) => [remember.not(), lastSeen.match({none: () => no, some: l => now.atLeast(l.plus(idle))})], env => valid(env).not()),
  stepUp.decide('a transfer always needs a fresh MFA', env => [env.action.is('transfer'), allow(env)], env => recent(env)),
  stepUp.decide('high risk always needs a fresh MFA', env => [env.risk.atLeast(80), allow(env)], env => recent(env)),
  stepUp.decide('no MFA on record: no transfer', env => [env.mfaAge.isNone, allow(env)], env => env.action.is('transfer').not()),
]

// Attribute-based access: guests read public documents; staff need a clearance covering the document's level and a
// known same-department fact; admins need the clearance. Missing facts fail closed.
const doc = rule('document access')
  .inputs({role: oneOf('guest', 'staff', 'admin'), clearance: maybe(upTo(3)), level: upTo(3), sameDept: maybe(bool)})
type DocEnv = {role: Choice<'guest' | 'staff' | 'admin'>, clearance: Maybe<Term>, level: Term, sameDept: Maybe<Bool>}
const cleared = ({clearance, level}: DocEnv) => clearance.match({none: () => no, some: c => level.atMost(c)})
const inDept = ({sameDept}: DocEnv) => sameDept.match({none: () => no, some: d => d})
const permit = (env: DocEnv) => env.role.match({guest: () => env.level.eq(0), staff: () => cleared(env).and(inDept(env)), admin: () => cleared(env)})
const permitAdminBypass = (env: DocEnv) => env.role.match({guest: () => env.level.eq(0), staff: () => cleared(env).and(inDept(env)), admin: () => yes})
const permitDeptDefault = (env: DocEnv) => env.role.match({guest: () => env.level.eq(0), staff: () => cleared(env).and(env.sameDept.match({none: () => yes, some: d => d})), admin: () => cleared(env)})
const docDecisions = [
  doc.decide('without a clearance on file, only public documents', env => [env.clearance.isNone, permit(env)], ({level}) => level.eq(0)),
  doc.decide('above public, the clearance covers the level', env => [permit(env), env.level.gt(0)], env => cleared(env)),
  doc.decide('staff need a known same-department fact', env => [env.role.is('staff'), permit(env)], env => inDept(env)),
]

// Delegation: the root grants a level up to rootLevel; a holder delegates to another principal at most their own level
// (the requested level, narrowed by min), one hop deeper, and never past maxDepth hops.
const delegation = rule('delegation narrows')
  .params({rootLevel: nat, maxDepth: nat})
  .inputs({op: oneOf('root', 'delegate'), from: nat, to: nat, lvl: nat})
  .maps({Level: 0, Depth: 0})
  .flags(({op, from, Depth, maxDepth}) => ({hop: op.is('delegate').and(Depth.at(from).lt(maxDepth))}))
  .step(({op, from, to, lvl, hop, rootLevel, Level, Depth}) => ({
    Level: Level.set(to, when(op.is('root'), min(lvl, rootLevel), when(hop, min(Level.at(from), lvl), Level.at(to)))),
    Depth: Depth.set(to, when(op.is('root'), 0, when(hop, Depth.at(from).plus(1), Depth.at(to)))),
  }))
const delegationLawsOf = (r: typeof delegation) => [
  r.law('nobody holds more than the root level', ({Level, rootLevel}) => forall(p => Level.at(p).atMost(rootLevel))),
  r.law('no chain is deeper than maxDepth', ({Depth, maxDepth}) => forall(p => Depth.at(p).atMost(maxDepth))),
]
const delegationUnclamped = delegation.step(({op, from, to, lvl, hop, rootLevel, Level, Depth}) => ({
  Level: Level.set(to, when(op.is('root'), min(lvl, rootLevel), when(hop, lvl, Level.at(to)))),
  Depth: Depth.set(to, when(op.is('root'), 0, when(hop, Depth.at(from).plus(1), Depth.at(to)))),
}))
const delegationDepthOffByOne = delegation.flags(({op, from, Depth, maxDepth}) => ({hop2: op.is('delegate').and(Depth.at(from).atMost(maxDepth))}))
  .step(({op, from, to, lvl, hop2, rootLevel, Level, Depth}) => ({
    Level: Level.set(to, when(op.is('root'), min(lvl, rootLevel), when(hop2, min(Level.at(from), lvl), Level.at(to)))),
    Depth: Depth.set(to, when(op.is('root'), 0, when(hop2, Depth.at(from).plus(1), Depth.at(to)))),
  }))

// Key rotation: every key of every tenant is rotated, a batch of at least one key per turn; when a tenant is done the
// sweep moves to the next one with a full set of keys. The rank is the pair (tenants left, keys left in this one).
const rotation = (advances: boolean) => loop(advances ? 'key rotation sweep' : 'key rotation sweep, stuck on a tenant')
  .params({tenants: nat, keys: nat})
  .inputs({batch: nat})
  .state({t: ({tenants}) => tenants, k: ({keys}) => keys})
  .assume(({batch}) => batch.atLeast(1))
  .while(({t}) => t.gt(0))
  .body(({t, k, keys, batch}) => ({k: when(k.gt(0), k.minus(min(k, batch)), keys), t: when(k.gt(0), t, advances ? t.minus(1) : t)}))
  .rank(({t, k}) => [t, k])
const rotationLawsOf = (l: ReturnType<typeof rotation>) => [
  l.law('keys left <= keys per tenant', ({k, keys}) => k.atMost(keys)),
  l.law('tenants left <= tenants', ({t, tenants}) => t.atMost(tenants)),
]

export const domain: Domain = {
  domain: 'access',
  about: 'role grants, lockout, one-time tokens, quotas, reset-email limits, sessions, step-up, ABAC, delegation, key rotation',
  cases: [
    machineCase('role grants', 'every admin is a member, through promotions and removals', roles, roleLaws, [
      {name: 'removal keeps the admin role', why: 'removing a member forgets to revoke their admin role', rule: removeKeepsAdmin, laws: [adminIsMember(removeKeepsAdmin)]},
      {name: 'promotes anyone', why: 'a promotion forgets to check membership', rule: promoteAnyone, laws: [adminIsMember(promoteAnyone)]},
    ]),
    machineCase('login lockout', 'the failure that reaches maxFails locks the account, and a locked account counts no more', lockout, lockoutLawsOf(lockout), [
      {name: 'locks one failure late', why: 'the lock compares the count before this failure (off by one)', rule: lockoutOffByOne, laws: lockoutLawsOf(lockoutOffByOne)},
      {name: 'counts while locked', why: 'failures keep counting on a locked account', rule: lockoutCountsWhileLocked, laws: lockoutLawsOf(lockoutCountsWhileLocked)},
    ]),
    machineCase('one-time reset tokens', 'a token is redeemed at most once, and only after it was issued', tokens, tokenLawsOf(tokens), [
      {name: 'replayable token', why: 'a redemption forgets to check the token was already used', rule: tokenReplay, laws: tokenLawsOf(tokenReplay)},
      {name: 'redeems unissued tokens', why: 'a redemption forgets to check the token was issued', rule: tokenUnissued, laws: tokenLawsOf(tokenUnissued)},
    ]),
    machineCase('API quota per tenant', 'every tenant stays within its quota, refunds included', quota, [quotaLawOf(quota)], [
      {name: 'checks remaining only', why: 'a call is served while any quota remains, ignoring its cost', rule: quotaChecksRemaining, laws: [quotaLawOf(quotaChecksRemaining)]},
    ]),
    machineCase('reset emails per hour', 'no account gets more than cap reset emails in any hour ending at now, read from the log', mails, [mailsLawOf(mails)], [
      {name: 'window a minute short', why: 'the lookback forgets the oldest minute of the hour', rule: mailsShortWindow, laws: [mailsLawOf(mailsShortWindow)]},
    ]),
    decisionCase('sessions and step-up', 'expired or unknown sessions fail closed, and transfers and risky actions need a fresh MFA', sessionDecisions, [
      {name: 'remember-me skips every check', why: 'remember-me also bypasses the absolute lifetime', decision: session.decide('past the absolute lifetime, never valid', ({now, issuedAt, ttl}) => now.atLeast(issuedAt.plus(ttl)), env => validRememberBypass(env).not())},
      {name: 'trusted device skips MFA on transfers', why: 'a trusted device replaces the fresh MFA instead of adding to it', decision: stepUp.decide('a transfer always needs a fresh MFA', env => [env.action.is('transfer'), allowTrustedTransfer(env)], env => recent(env))},
    ]),
    decisionCase('document access', 'missing clearances and department facts fail closed, and no role reads above its clearance', docDecisions, [
      {name: 'admins skip the clearance', why: 'the admin role is let through without a clearance', decision: doc.decide('above public, the clearance covers the level', env => [permitAdminBypass(env), env.level.gt(0)], env => cleared(env))},
      {name: 'missing department read as same', why: 'an unknown department defaults to the same department', decision: doc.decide('staff need a known same-department fact', env => [env.role.is('staff'), permitDeptDefault(env)], env => inDept(env))},
    ]),
    machineCase('delegation narrows', 'a delegated level never passes the root level, and chains stay within maxDepth hops', delegation, delegationLawsOf(delegation), [
      {name: 'copies the requested level', why: 'the delegate gets the requested level, not narrowed to the delegator\'s', rule: delegationUnclamped, laws: delegationLawsOf(delegationUnclamped)},
      {name: 'one hop too deep', why: 'the depth check lets a holder at maxDepth delegate (off by one)', rule: delegationDepthOffByOne, laws: delegationLawsOf(delegationDepthOffByOne)},
    ]),
    loopCase('key rotation sweep', 'the sweep ends, rank (tenants left, keys left) dropping every turn', rotation(true), rotationLawsOf(rotation(true)), [
      {name: 'stuck on a tenant', why: 'a finished tenant refills its keys without moving to the next tenant', loop: rotation(false), laws: rotationLawsOf(rotation(false))},
    ]),
  ],
}
