// Laws about two runs (relational.ts): each construction proves what holds and refutes what doesn't, the refutation a
// real pair of runs; the rule built runs as its two sides do.
import {expect, test} from 'bun:test'
import {interpret, type State} from './machine.ts'
import {nat, oneOf, rule, when} from './dsl.ts'
import {agreement, isolation, noninterference, proveTwoRuns, twoRuns} from './relational.ts'

// A claim desk: a claim is submitted with an amount and a diagnosis (kept in notes), then decided by the amount.
const desk = (leak: boolean, refuseBySecret = false) => rule('desk')
  .inputs({op: oneOf('submit', 'decide'), amount: nat, diagnosis: nat})
  .state({status: oneOf('none', 'pending', 'approved', 'denied').from('none'), total: 0, notes: 0})
  .assume(({op, diagnosis}) => (refuseBySecret ? op.is('decide').or(diagnosis.atMost(9)) : op.is('decide').or(op.is('submit'))))
  .step(({op, amount, diagnosis, status, total, notes}) => {
    const approve = leak ? diagnosis.lt(5) : amount.atMost(100)
    return {
      status: when(op.is('submit'), 'pending', when(status.is('pending'), when(approve, status.of('approved'), 'denied'), status)),
      total: when(op.is('submit'), total.plus(amount), total),
      notes: when(op.is('submit'), diagnosis, notes),
    }
  })

test('noninterference: the diagnosis never reaches the status, the total or the refusals', () => {
  const l = noninterference(desk(false), {secret: ['diagnosis'], visible: ['status', 'total']})
  const v = proveTwoRuns(l, {search: {ms: 5000}})
  expect(v.proven && v.checked).toBe(true)
})
test('noninterference: a decision by the diagnosis is refuted by two runs', () => {
  const l = noninterference(desk(true), {secret: ['diagnosis'], visible: ['status', 'total']})
  const v = proveTwoRuns(l, {search: {ms: 5000}})
  expect(v.proven).toBe(false)
  expect(v.run).toBeDefined()
  const last = v.run!.trace.at(-1)!
  expect(last.a_diagnosis === last.b_diagnosis).toBe(false)
})
test('noninterference: a refusal by the secret is a difference', () => {
  const l = noninterference(desk(false, true), {secret: ['diagnosis'], visible: ['status']})
  const v = proveTwoRuns(l, {search: {ms: 5000}})
  expect(v.proven).toBe(false)
  expect(v.goal).toContain('refuse the same requests')
  // ... and with refusals assumed, only the state is compared
  expect(proveTwoRuns(noninterference(desk(false, true), {secret: ['diagnosis'], visible: ['status'], refusals: 'assumed'}), {search: {ms: 5000}}).proven).toBe(true)
})

// A lockout: each user's failures counted, a login refused at 3 (per user), or at 10 failures of anyone (global).
const lockout = (global: boolean) => rule('lockout')
  .inputs({op: oneOf('fail', 'login'), user: nat})
  .state({total: 0})
  .maps({Fails: 0})
  .assume(({op, user, Fails, total}) => op.is('fail').or(Fails.at(user).lt(3)).and(global ? op.is('fail').or(total.lt(10)) : op.is('fail').or(op.is('login'))))
  .step(({op, user, Fails, total}) => ({Fails: Fails.set(user, when(op.is('fail'), Fails.at(user).plus(1), Fails.at(user))), total: when(op.is('fail'), total.plus(1), total)}))

test('isolation: a per-user lockout keeps each user\'s cell and refusals whatever the others do', () => {
  const v = proveTwoRuns(isolation(lockout(false), {owner: 'user'}), {search: {ms: 5000}})
  expect(v.proven && v.checked).toBe(true)
})
test('isolation: a global lockout lets the others lock B out', () => {
  const v = proveTwoRuns(isolation(lockout(true), {owner: 'user'}), {search: {ms: 5000}})
  expect(v.proven).toBe(false)
  expect(v.goal).toContain('refuse the same requests')
  expect(v.run).toBeDefined()
})

// A cap, and two refactors of it: one the same rule, one with the boundary moved.
const cap = (variant: 0 | 1 | 2) => rule('cap').params({limit: nat}).inputs({cost: nat}).state({used: 0})
  .step(({cost, used, limit}) => ({used: variant === 0 ? when(used.plus(cost).atMost(limit), used.plus(cost), used)
    : variant === 1 ? when(limit.lt(used.plus(cost)), used, used.plus(cost)) : when(used.plus(cost).lt(limit), used.plus(cost), used)}))

test('agreement: a refactor agrees on every history; a moved boundary is refuted', () => {
  expect(proveTwoRuns(agreement(cap(0), cap(1)), {search: {ms: 5000}}).proven).toBe(true)
  const v = proveTwoRuns(agreement(cap(0), cap(2)), {search: {ms: 5000}})
  expect(v.proven).toBe(false)
  expect(v.run).toBeDefined()
})

test('two runs side by side run as their sides do', () => {
  const r = desk(false), p = twoRuns(r, r, {shared: ['op', 'amount'], refusals: 'assumed'})
  const one = interpret(r.machine), two = interpret(p.machine)
  let a: State = one.init({}), b: State = one.init({}), ab: State = two.init({})
  const reqs = [{op: 0, amount: 50, diagnosis: 3, d2: 7}, {op: 1, amount: 0, diagnosis: 1, d2: 2}, {op: 0, amount: 200, diagnosis: 8, d2: 0}, {op: 1, amount: 0, diagnosis: 0, d2: 0}]
  for (const q of reqs) {
    a = one.step({}, a, {op: q.op, amount: q.amount, diagnosis: q.diagnosis})
    b = one.step({}, b, {op: q.op, amount: q.amount, diagnosis: q.d2})
    ab = two.step({}, ab, {op: q.op, amount: q.amount, a_diagnosis: q.diagnosis, b_diagnosis: q.d2})
    for (const [n, x] of Object.entries(a.scalars)) expect(ab.scalars[`a_${n}`]).toBe(x)
    for (const [n, x] of Object.entries(b.scalars)) expect(ab.scalars[`b_${n}`]).toBe(x)
  }
})
