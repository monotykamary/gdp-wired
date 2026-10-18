// Values beyond naturals (core/dsl.ts): integers and decimals (int, decimal, .ints, .decimals), each kept as two
// naturals, and strings (str), kept as an interned name, a length and one bit per declared pattern; so the kernel and
// the Lean twin see nothing new. An account that may go negative down to a limit, a fee in cents, functions with signed
// results, and host and user checks over strings: proven, the broken variants refused, the runtimes agreeing with plain
// arithmetic and string matching, and the Lean export.
import {expect, test} from 'bun:test'
import {Decimal, Int, bool, decimal, fun, globMatch, int, intern, interned, nat, oneOf, proveDecision, proveRule, proveSteps, rule, str, when, yes} from './dsl.ts'
import {checkCase, decisionCase, machineCase} from '../examples/harness.ts'
import {toLean} from '../lean-kernel/emit.ts'

const account = (bug?: 'checks only the balance') => rule('account').params({limit: nat}).inputs({op: oneOf('deposit', 'withdraw'), amount: nat})
  .ints({balance: 0})
  .flags(({op, amount, balance, limit}) => ({
    ok: op.is('deposit').or(bug ? balance.atLeast(0) : balance.minus(amount).atLeast(Int.of(limit).negate())),
  }))
  .step(({op, amount, balance, ok}) => ({balance: when(ok, when(op.is('deposit'), balance.plus(amount), balance.minus(amount)), balance)}))
const floor = (r: ReturnType<typeof account>) => r.law('the balance never goes below −limit', ({balance, limit}) => balance.atLeast(Int.of(limit).negate()))

test('an integer state variable: proven, the broken variant refused, runs agree with plain arithmetic', () => {
  expect(proveRule(account(), [floor(account())])).toMatchObject({proven: true, checked: true})
  const broken = proveRule(account('checks only the balance'), [floor(account('checks only the balance'))])
  expect(broken.proven).toBe(false)
  const r = account(), gen = r.compiled(), run = r.interpreter(), ps = r.encodeParams({limit: 50})
  let st = gen.init(ps), si = run.init(ps), want = 0
  for (const [op, amount] of [['withdraw', 30], ['withdraw', 15], ['withdraw', 10], ['deposit', 5], ['deposit', 100], ['withdraw', 155], ['withdraw', 110]] as const) {
    st = gen.step(ps, st, r.encodeInput({op, amount})); si = run.step(ps, si, r.encodeInput({op, amount}))
    if (op === 'deposit' || want - amount >= -50) want += op === 'deposit' ? amount : -amount
    expect(r.decode(st)).toEqual({balance: want})
    expect(r.decode(si)).toEqual({balance: want})
    // Normalized: at most one part is nonzero.
    expect(Math.min(st.scalars.balance!, st.scalars.balance$neg!)).toBe(0)
  }
  expect(want).toBe(-50)
  // Step laws read the after state as an integer too.
  const up = r.stepLaw('a deposit raises the balance by the amount', ({balance, amount}, after) => after.balance.eq(balance.plus(amount)), ({op}) => op.is('deposit'))
  expect(proveSteps(r, [floor(r)], [up])).toMatchObject({proven: true, checked: true})
  // The triple check: random runs (inputs drawn as integers) and the broken variant broken by one.
  const findings = checkCase(machineCase('account', 'overdraft', r, [floor(r)], [{name: 'checks only the balance', why: 'overdraft', rule: account('checks only the balance'), laws: [floor(account('checks only the balance'))]}]))
  expect(findings.filter(f => !f.ok).map(f => f.detail)).toEqual([])
  // Lean: the export is the twin's, over the two parts.
  expect(toLean([{id: 'account', machine: r.machine, laws: [floor(r)]}])).toContain('theorem account_laws')
})

test('decimals: scaled exactly, compared with numbers, mixed places refused', () => {
  const fee = (bug?: 'may go negative') => fun('fee').inputs({price: decimal(2), coupon: decimal(2)})
    .returns(({price, coupon}) => ({total: bug ? price.minus(coupon) : price.minus(coupon).max(0), covered: price.minus(coupon).isNegative.not()}))
  const never = (f: ReturnType<typeof fee>) => f.law('the total is never negative', () => [], o => o.total.atLeast(0))
  expect(proveDecision(never(fee()))).toMatchObject({proven: true, checked: true})
  expect(proveDecision(never(fee('may go negative'))).proven).toBe(false)
  expect(fee().run({price: '12.50', coupon: 2.25})).toEqual({total: 10.25, covered: true})
  expect(fee().run({price: 1, coupon: '2.5'})).toEqual({total: 0, covered: false})
  expect(fee('may go negative').run({price: 1, coupon: '2.5'})).toEqual({total: -1.5, covered: false})
  // 0.1 + 0.2 is 0.3 at two places; a third place is refused, as is a malformed number.
  expect(fee().run({price: 0.1 + 0.2, coupon: 0})).toEqual({total: 0.3, covered: true})
  expect(() => fee().run({price: '1.234', coupon: 0})).toThrow('needs more than 2 decimal places')
  expect(() => fee().run({price: '1,5', coupon: 0})).toThrow('is not a decimal')
  // A literal in a law is scaled to the decimal's places.
  const cap = fun('cap').inputs({price: decimal(2)}).returns(({price}) => ({paid: price.min(19.99)}))
  expect(proveDecision(cap.law('never more than 19.99', () => [], o => o.paid.atMost(19.99)))).toMatchObject({proven: true, checked: true})
  expect(proveDecision(cap.law('never more than 19.98', () => [], o => o.paid.atMost(19.98))).proven).toBe(false)
  const a = new Decimal(Int.of(0), 2), b = new Decimal(Int.of(0), 3)
  expect(() => a.plus(b)).toThrow("decimals with 2 and 3 places don't mix")
  // Decimal state, starting from a string.
  const wallet = rule('wallet').inputs({spend: decimal(2)}).decimals(2, {left: '20.00'}).assume(({spend}) => spend.atLeast(0))
    .step(({spend, left}) => ({left: when(spend.atMost(left), left.minus(spend), left)}))
  expect(proveRule(wallet, [wallet.law('never overspent', ({left}) => left.atLeast(0))])).toMatchObject({proven: true, checked: true})
  const g = wallet.compiled()
  let st = g.init({})
  for (const spend of ['7.25', '13.00', '12.75']) st = g.step({}, st, wallet.encodeInput({spend}))
  expect(wallet.decode(st)).toEqual({left: 0})
})

test('integers in functions: negation, times by a negative constant, abs', () => {
  const f = fun('f').inputs({x: int}).returns(({x}) => ({y: x.times(-3).plus(7), a: x.abs, sign: x.isNegative}))
  expect(f.run({x: -4})).toEqual({y: 19, a: 4, sign: true})
  expect(f.run({x: 5})).toEqual({y: -8, a: 5, sign: false})
  expect(proveDecision(f.law('abs is at least the value', () => [], (o, {x}) => x.atMost(o.a)))).toMatchObject({proven: true, checked: true})
  expect(() => f.law('mixed', () => [], (o, {x}) => o.a.atLeast(x as never))).toThrow('a natural is expected here')
  expect(proveDecision(f.law('y falls as x rises', ({x}) => x.atLeast(3), o => o.y.atMost(-2)))).toMatchObject({proven: true, checked: true})
  expect(proveDecision(f.law('y is never negative', () => [], o => o.y.atLeast(0))).proven).toBe(false)
  expect(() => f.run({x: 1.5})).toThrow('must be an integer')
})

test('strings: patterns computed from the string, equality carries them, laws proven and refused', () => {
  for (const [p, t, want] of [['*.example.com', 'api.example.com', true], ['*.example.com', 'example.com', false], ['a*b*c', 'abc', true], ['a*b*c', 'acb', false],
    ['*', '', true], ['x\\*y', 'x*y', true], ['x\\*y', 'xzy', false], ['ab*ba', 'aba', false], ['ab*ba', 'abba', true]] as const) expect([p, t, globMatch(p, t)]).toEqual([p, t, want])
  const access = (bug?: 'admin open to anyone') => fun('access').inputs({host: str({like: ['*.internal']}), user: str({maxLength: 32}), staff: bool})
    .returns(({host, user, staff}) => ({allowed: host.like('*.internal').implies(staff).and(user.isEmpty.not(), bug ? yes : host.ne('admin.internal').or(user.eq('root')))}))
  const laws = (f: ReturnType<typeof access>) => [
    f.law('internal hosts need staff', ({host}) => host.like('*.internal'), (o, {staff}) => o.allowed.implies(staff)),
    f.law('admin.internal is root only', ({host}) => host.eq('admin.internal'), (o, {user}) => o.allowed.implies(user.eq('root'))),
    // From the literal: admin.internal matches *.internal, so staff is needed there too.
    f.law('admin.internal needs staff', ({host}) => host.eq('admin.internal'), (o, {staff}) => o.allowed.implies(staff)),
    f.law('an empty user is refused', ({user}) => user.isEmpty, o => o.allowed.not()),
  ]
  for (const d of laws(access())) expect([d.name, proveDecision(d).proven]).toEqual([d.name, true])
  expect(proveDecision(laws(access('admin open to anyone'))[1]!).proven).toBe(false)
  expect(access().run({host: 'db.internal', user: 'ann', staff: true})).toEqual({allowed: true})
  expect(access().run({host: 'admin.internal', user: 'ann', staff: true})).toEqual({allowed: false})
  expect(access().run({host: 'admin.internal', user: 'root', staff: true})).toEqual({allowed: true})
  expect(access().run({host: 'admin.internal', user: 'root', staff: false})).toEqual({allowed: false})
  // The triple check: strings drawn so each pattern matches some, and the broken variant broken by a draw.
  const findings = checkCase(decisionCase('access', 'hosts', laws(access()), [{name: 'admin open to anyone', why: 'hosts', decision: laws(access('admin open to anyone'))[1]!}], {bound: 6}))
  expect(findings.filter(f => !f.ok).map(f => `${f.item}: ${f.detail}`)).toEqual([])
  // Two strings: equal ones match the same patterns.
  const two = fun('two').inputs({a: str({like: ['*.com']}), b: str({like: ['*.com']})}).returns(({a}) => ({com: a.like('*.com')}))
  expect(proveDecision(two.law('equal strings match alike', ({a, b}) => a.eq(b), (o, {b}) => o.com.iff(b.like('*.com')))).proven).toBe(true)
  expect(proveDecision(two.law('any two strings match alike', () => [], (o, {b}) => o.com.iff(b.like('*.com')))).proven).toBe(false)
  // Refusals: an undeclared pattern, a string past its length.
  expect(() => fun('f').inputs({a: str({like: ['x*']})}).returns(({a}) => ({m: a.like('y*')})).law('l', () => [], o => o.m)).toThrow('declare the pattern on the kind')
  expect(() => access().run({host: 'h', user: 'u'.repeat(33), staff: true})).toThrow('at most 32 characters')
  // The interning table, for state that keeps names across processes.
  expect(interned().find(([t]) => t === 'admin.internal')?.[1]).toBe(intern('admin.internal'))
  expect(() => intern.load([['admin.internal', intern('admin.internal') + 1000]])).toThrow('is interned as')
})
