// The gdp-ts adapter (gdp.ts): proofs minted only where the proven condition holds, guards and gates refused when a law
// isn't proven, and requests outside what was proven failing closed.
import {expect, test} from 'bun:test'
import {defineProof, name} from '@gdp-ts/core'
import {type Bool, type Choice, type Cond, type Maybe, type Term, bool, count, forall, fun, maybe, nat, no, oneOf, relation, rule, upTo, when} from './dsl.ts'
import {Unproven, gate, guard} from './gdp.ts'

// Document access (examples/domains/access.ts, as a function): guests read public documents; staff need a clearance
// covering the level and a known same-department fact; admins need the clearance. Missing facts fail closed.
type DocEnv = {role: Choice<'guest' | 'staff' | 'admin'>, clearance: Maybe<Term>, level: Term, sameDept: Maybe<Bool>}
const cleared = ({clearance, level}: DocEnv) => clearance.match({none: () => no, some: c => level.atMost(c)})
const inDept = ({sameDept}: DocEnv) => sameDept.match({none: () => no, some: d => d})
const permit = (env: DocEnv) => env.role.match({guest: () => env.level.eq(0), staff: () => cleared(env).and(inDept(env)), admin: () => cleared(env)})
const adminBypass = (env: DocEnv) => env.role.match({guest: () => env.level.eq(0), staff: () => cleared(env).and(inDept(env)), admin: () => cleared(env).or(env.role.is('admin'))})
const docFun = (p: (env: DocEnv) => Cond) => fun('document access')
  .inputs({role: oneOf('guest', 'staff', 'admin'), clearance: maybe(upTo(3)), level: upTo(3), sameDept: maybe(bool)})
  .returns(env => ({permit: p(env)}))
const access = docFun(permit)
const coversLevel = (f: typeof access) => f.law('above public, the clearance covers the level', (env, out) => [out.permit, env.level.gt(0)], (_, env) => cleared(env))
const accessLaws = [
  access.law('without a clearance on file, only public documents', (env, out) => [env.clearance.isNone, out.permit], (_, env) => env.level.eq(0)),
  coversLevel(access),
  access.law('staff need a known same-department fact', (env, out) => [env.role.is('staff'), out.permit], (_, env) => inDept(env)),
]

test('a guard mints exactly where the proven condition holds', () => {
  const CanRead = defineProof('CanRead')
  const mint = guard(CanRead, access, 'permit', {laws: accessLaws})
  name(7, 42, (user, doc) => {
    expect(mint({role: 'staff', clearance: 2, level: 1, sameDept: true}, user, doc)?.kind).toBe('CanRead')
    expect(mint({role: 'guest', clearance: null, level: 0, sameDept: null}, user, doc)?.kind).toBe('CanRead')
    expect(mint({role: 'staff', clearance: 2, level: 1, sameDept: null}, user, doc)).toBeNull()
    expect(mint({role: 'admin', clearance: null, level: 2, sameDept: null}, user, doc)).toBeNull()
    expect(mint({role: 'admin', clearance: 1, level: 2, sameDept: true}, user, doc)).toBeNull()
  })
})

test('a guard whose law fails is refused, with the counterexample', () => {
  const bypass = docFun(adminBypass)
  const made = () => guard(defineProof('CanRead'), bypass, 'permit', {laws: [coversLevel(bypass)]})
  expect(made).toThrow(Unproven)
  try { made() } catch (e) { expect((e as Unproven).verdict.witness).toBeDefined() }
})

test('a guard takes only laws stated about its own function', () => {
  const bypass = docFun(adminBypass)
  expect(() => guard(defineProof('CanRead'), access, 'permit', {laws: [coversLevel(bypass)]})).toThrow(/not stated about this function/)
  expect(() => guard(defineProof('CanRead'), access, 'permit', {laws: []})).toThrow(/needs a law/)
})

test('arguments outside what was proven mint nothing, and values outside their kinds are refused', () => {
  const capped = fun('capped').params({cap: nat}).inputs({ask: upTo(10)}).assume(({ask}) => ask.atLeast(1)).returns(({ask, cap}) => ({ok: ask.atMost(cap)}))
  const mint = guard(defineProof('Fits'), capped, 'ok', {laws: [capped.law('a grant is within the cap', (_, out) => out.ok, (_, {ask, cap}) => ask.atMost(cap))], params: {cap: 5}})
  name('req', r => {
    expect(mint({ask: 3}, r)?.kind).toBe('Fits')
    expect(mint({ask: 6}, r)).toBeNull()
    expect(mint({ask: 0}, r)).toBeNull() // assume: ask >= 1
    expect(() => mint({ask: 11}, r)).toThrow(RangeError) // not a value of upTo(10)
  })
})

// One-time reset tokens: issued once, redeemed at most once, and only if issued.
const tokenRule = (replay: boolean) => rule(replay ? 'replayable tokens' : 'one-time tokens')
  .inputs({op: oneOf('issue', 'redeem'), token: nat})
  .maps({Issued: 0, Used: 0})
  .flags(({op, token, Issued, Used}) => ({
    issue: op.is('issue').and(Issued.at(token).eq(0)),
    redeem: replay ? op.is('redeem').and(Issued.at(token).eq(1)) : op.is('redeem').and(Issued.at(token).eq(1), Used.at(token).eq(0)),
  }))
  .step(({token, issue, redeem, Issued, Used}) => ({Issued: Issued.bump(token, issue), Used: Used.bump(token, redeem)}))
const tokenLaws = (r: ReturnType<typeof tokenRule>) => [
  r.law('every token is used at most as often as issued', ({Used, Issued}) => forall(t => Used.at(t).atMost(Issued.at(t)))),
  r.law('every token is issued at most once', ({Issued}) => forall(t => Issued.at(t).atMost(1))),
]

test('a gate mints once per step that takes its flag', () => {
  const tokens = tokenRule(false), redeemed = gate(defineProof('Redeemed'), tokens, 'redeem', {laws: tokenLaws(tokens)})
  name(7, t => {
    expect(redeemed.request({op: 'redeem', token: 7}, t)).toBeNull() // not issued yet
    expect(redeemed.request({op: 'issue', token: 7}, t)).toBeNull() // a step, not a redemption
    expect(redeemed.request({op: 'redeem', token: 7}, t)?.kind).toBe('Redeemed')
    expect(redeemed.request({op: 'redeem', token: 7}, t)).toBeNull() // used
  })
  expect(redeemed.state.maps['Used']?.get(7)).toBe(1)
})

test('a gate whose law fails is refused', () => {
  const replay = tokenRule(true)
  expect(() => gate(defineProof('Redeemed'), replay, 'redeem', {laws: tokenLaws(replay)})).toThrow(Unproven)
  expect(() => gate(defineProof('Redeemed'), replay, 'nope' as never, {laws: tokenLaws(replay)})).toThrow(/no flag nope/)
})

test('a gate refuses requests outside what was proven, and resumes from a saved state', () => {
  const quota = rule('quota').params({q: nat}).inputs({cost: upTo(10)}).state({used: 0})
    .assume(({cost}) => cost.atLeast(1))
    .flags(({used, cost, q}) => ({served: used.plus(cost).atMost(q)}))
    .step(({used, cost, served}) => ({used: when(served, used.plus(cost), used)}))
  const laws = [quota.law('usage stays within the quota', ({used, q}) => used.atMost(q))]
  const Served = defineProof('Served'), g = gate(Served, quota, 'served', {laws, params: {q: 8}})
  name('tenant', tenant => {
    expect(g.request({cost: 5}, tenant)?.kind).toBe('Served')
    expect(g.request({cost: 0}, tenant)).toBeNull() // assume: cost >= 1
    expect(() => g.request({cost: 11}, tenant)).toThrow(RangeError) // not a value of upTo(10): refused as the runtimes refuse it
    expect(g.values()).toEqual({used: 5})
    expect(g.request({cost: 4}, tenant)).toBeNull() // 9 > 8: a step that doesn't serve
    const again = gate(Served, quota, 'served', {laws, params: {q: 8}, state: g.state})
    expect(again.request({cost: 3}, tenant)?.kind).toBe('Served')
    expect(again.values()).toEqual({used: 8})
  })
})

test('a gate over a history: at most cap emails to an account in any hour', () => {
  const mails = rule('reset emails per hour')
    .params({hour: nat, cap: nat, now: nat, who: nat})
    .inputs({acct: nat, t: nat})
    .log('acct', 't')
    .sums({lastHour: (r, {now, hour, who}) => count(r.acct.eq(who).and(r.t.atMost(now), now.lt(r.t.plus(hour))))})
    .queries({sent: (r, {t, hour, acct}) => when(r.acct.eq(acct), count(t.lt(r.t.plus(hour))), 0)})
    .flags(({sent, cap}) => ({send: sent.plus(1).atMost(cap)}))
    .keep(({send}) => send)
    .relations(({t, now, acct, who, lastHour, sent}) => [relation(lastHour.atMost(sent), t.atMost(now).and(acct.eq(who)))])
  const laws = [mails.law('emails to who in the hour ending at now <= cap', ({lastHour, cap}) => lastHour.atMost(cap))]
  const g = gate(defineProof('MaySend'), mails, 'send', {laws, params: {hour: 60, cap: 2, now: 0, who: 0}})
  const sent = name('a@b.c', a => [0, 10, 20, 59, 61, 75, 80].map(t => g.request({acct: 1, t}, a) !== null))
  expect(sent).toEqual([true, true, false, false, true, true, false])
  expect(g.request({acct: 2, t: 80})).not.toBeNull() // another account's hour is its own
})

test('a guard on a condition inside a record of the result', () => {
  const decide = fun('decide').inputs({level: upTo(3), cleared: bool}).returns(({level, cleared}) => ({verdict: {ok: cleared.or(level.eq(0)), level}}))
  const mint = guard(defineProof('Ok'), decide, 'verdict.ok', {laws: [decide.law('above public, cleared', ({level}, out) => [out.verdict.ok, level.gt(0)], (_, {cleared}) => cleared)]})
  name(1, x => {
    expect(mint({level: 2, cleared: true}, x)?.kind).toBe('Ok')
    expect(mint({level: 2, cleared: false}, x)).toBeNull()
  })
})
