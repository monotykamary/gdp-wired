// The builders (dsl.ts) against the hand-written machines of models.ts: the same verdicts, and the same runs step by
// step through both runtimes; kinds encode and decode as declared; laws with forall, decisions and loops prove and
// refute as they should; and what the types let through, the kernel's scope check still refuses.
import {expect, test} from 'bun:test'
import {type Machine, type State, interpret, search} from './machine.ts'
import {admitFlagged, boundedLoss, capLaws, loss, windowCeiling, windowLimit} from './models.ts'
import {proveLaws} from '../kernel/prove.ts'
import {type DecisionEnv, type Rule, Cond, all, bool, count, forall, fun, loop, maybe, min, nat, oneOf, proveDecision, proveLoop, proveRule, proveSteps, relation, rule, upTo, when} from './dsl.ts'

let seed = Number(process.env.FUZZ_SEED ?? 777)
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const cells = (st: State) => JSON.stringify(Object.fromEntries(Object.entries(st.maps).map(([n, m]) => [n, [...m.entries()].sort((a, b) => a[0] - b[0])])))

const budget = rule('budget')
  .params({b: nat, m: nat})
  .inputs({c: nat})
  .state({s: 0})
  .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
const caps = rule('caps')
  .params({d: nat, hr: nat, dm: nat})
  .inputs({acct: nat, day: nat, hour: nat, dom: nat, ok: bool})
  .maps({Acct: 0, Day: 0, Hour: 0, Dom: 0})
  .flags(({ok, acct, day, hour, dom, d, hr, dm, Acct, Day, Hour, Dom}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d), Hour.at(hour).lt(hr), Dom.at(dom).lt(dm))}))
  .step(({acct, day, hour, dom, granted, Acct, Day, Hour, Dom}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted), Hour: Hour.bump(hour, granted), Dom: Dom.bump(dom, granted)}))
const capsLaws = [
  caps.law('once per account', ({Acct}) => forall(k => Acct.at(k).atMost(1))),
  caps.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d))),
  caps.law('hour cap', ({Hour, hr}) => forall(k => Hour.at(k).atMost(hr))),
  caps.law('domain cap', ({Dom, dm}) => forall(k => Dom.at(k).atMost(dm))),
]
const window = (ordered: boolean) => {
  const base = rule('window limit')
    .params({w: nat, c: nat, now: nat})
    .inputs({forced: bool, t: nat})
    .log('forced', 't')
    .sums({ours: (r, {now, w}) => count(r.forced.not().and(r.t.atMost(now), now.lt(r.t.plus(w))))})
    .queries({seen: (r, {t, w}) => count(t.lt(r.t.plus(w)))})
    .flags(({forced, seen, c}) => ({admitted: forced.not().and(seen.plus(1).atMost(c))}))
    .keep(({forced, admitted}) => forced.or(admitted))
    .relations(({t, now, ours, seen}) => [relation(ours.atMost(seen), t.atMost(now))])
  return ordered ? base.prune('t', ({w}) => w) : base
}
const ceiling = window(false).law('window ceiling', ({ours, c}) => ours.atMost(c))

// Same params and inputs into a builder machine and a hand-written one, every step compared, both runtimes.
function sameRuns(a: Machine, b: Machine, params: () => Record<string, number>, input: (step: number) => Record<string, number>, steps = 20, trials = 200) {
  const ra = interpret(a), rb = interpret(b)
  for (let trial = 0; trial < trials; trial++) {
    const p = params()
    let sa = ra.init(p), sb = rb.init(p)
    for (let i = 0; i < steps; i++) {
      const inp = input(i)
      sa = ra.step(p, sa, inp), sb = rb.step(p, sb, inp)
      expect(sa.scalars).toEqual(sb.scalars)
      expect(cells(sa)).toBe(cells(sb))
    }
  }
}

test('the builders give the hand-written machines: same verdicts, same runs', () => {
  expect(proveRule(budget, [budget.law('b + m', ({s, b, m}) => s.atMost(b.plus(m)))]).proven).toBe(true)
  expect(proveLaws(loss(), [boundedLoss]).proven).toBe(true)
  sameRuns(budget.machine, loss(), () => ({b: rand(30), m: rand(10)}), () => ({c: rand(15)}))

  expect(proveRule(caps, capsLaws)).toMatchObject({proven: true, checked: true})
  expect(proveLaws(admitFlagged(), capLaws).proven).toBe(true)
  sameRuns(caps.machine, admitFlagged(), () => ({d: rand(3), hr: rand(3), dm: rand(3)}), () => ({acct: rand(4), day: rand(3), hour: rand(3), dom: rand(3), ok: rand(2)}))

  expect(proveRule(window(false), [ceiling])).toMatchObject({proven: true, checked: true})
  expect(proveRule(window(true), [ceiling])).toMatchObject({proven: true, checked: true})
  let t = 0
  sameRuns(window(true).machine, windowLimit(true), () => ({w: 1 + rand(4), c: rand(4), now: rand(12)}), i => { if (i === 0) t = 0; t += rand(3); return {forced: rand(5) === 0 ? 1 : 0, t} })
  expect(proveLaws(windowLimit(), [windowCeiling]).proven).toBe(true)
})

test('variants are one call away, and broken ones are refuted', () => {
  const uncapped = budget.step(({b, c, s}) => ({s: when(s.lt(b), s.plus(c), s)}))
  expect(proveRule(uncapped, [uncapped.law('b + m', ({s, b, m}) => s.atMost(b.plus(m)))]).proven).toBe(false)
  const dayForgotten = caps.flags(({ok, acct, hour, dom, hr, dm, Acct, Hour, Dom}) => ({granted2: ok.and(Acct.at(acct).lt(1), Hour.at(hour).lt(hr), Dom.at(dom).lt(dm))}))
    .step(({acct, day, hour, dom, granted2, Acct, Day, Hour, Dom}) => ({Acct: Acct.bump(acct, granted2), Day: Day.bump(day, granted2), Hour: Hour.bump(hour, granted2), Dom: Dom.bump(dom, granted2)}))
  expect(proveRule(dayForgotten, [dayForgotten.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))]).proven).toBe(false)
  // A flag named again replaces it in place: the step stays as written.
  const dayForgotten2 = caps.flags(({ok, acct, hour, dom, hr, dm, Acct, Hour, Dom}) => ({granted: ok.and(Acct.at(acct).lt(1), Hour.at(hour).lt(hr), Dom.at(dom).lt(dm))}))
  expect(Object.keys(dayForgotten2.machine.step.flags!)).toEqual(['granted'])
  expect(proveRule(dayForgotten2, [dayForgotten2.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))]).proven).toBe(false)
  expect(proveRule(caps, capsLaws).proven).toBe(true) // the original is untouched
  const noRelation = window(false).relations(() => [])
  expect(proveRule(noRelation, [noRelation.law('window ceiling', ({ours, c}) => ours.atMost(c))]).proven).toBe(false)
})

test('kinds: encodings, assumptions and match', () => {
  const r = rule('kinds')
    .inputs({plan: oneOf('free', 'pro', 'team'), spent: maybe(nat), allowance: maybe(upTo(1000)), admin: bool, pct: upTo(100)})
    .state({x: 0})
  expect(r.encodeInput({plan: 'team', spent: null, allowance: 40, admin: true, pct: 7})).toEqual({plan: 2, spent$some: 0, spent: 0, allowance$some: 1, allowance: 40, admin: 1, pct: 7})
  expect(() => r.encodeInput({plan: 'gold', spent: 1, allowance: 1, admin: false, pct: 1})).toThrow(RangeError)
  expect(() => r.encodeInput({plan: 'pro', spent: 1, allowance: 1001, admin: false, pct: 1})).toThrow(RangeError)
  expect(() => r.encodeInput({plan: 'pro', spent: -1, allowance: 1, admin: false, pct: 1})).toThrow(RangeError)
  const m = r.machine
  expect(m.inputs).toEqual(['plan', 'spent$some', 'spent', 'allowance$some', 'allowance', 'admin', 'pct'])
  for (let i = 0; i < 200; i++) {
    const inp = r.randomInput(rand, 5)
    expect(inp.plan!).toBeLessThan(3); expect(inp.admin!).toBeLessThan(2); expect(inp.pct!).toBeLessThanOrEqual(100)
  }
  // A decision by cases: on trial means a free plan with both facts known and spent under the allowance.
  const facts = rule('trial').inputs({plan: oneOf('free', 'pro', 'team'), spent: maybe(nat), allowance: maybe(nat)})
  const trial = facts.decide('a missing fact means not on trial',
    ({spent, allowance}) => any2(spent.isNone, allowance.isNone),
    ({plan, spent, allowance}) => plan.match({
      free: () => spent.match({none: () => trueC(), some: s => allowance.match({none: () => trueC(), some: a => s.atLeast(a)})}),
      pro: () => trueC(), team: () => trueC(),
    }))
  expect(proveDecision(trial)).toMatchObject({proven: true, checked: true})
  const wrong = facts.decide('every free plan is on trial', ({plan}) => plan.is('free'),
    ({spent, allowance}) => spent.match({none: () => falseC(), some: s => allowance.match({none: () => falseC(), some: a => s.lt(a)})}))
  expect(proveDecision(wrong).proven).toBe(false)
  expect(() => r.machine && rule('mixed').inputs({p: oneOf('a', 'b')}).decide('x', () => [], ({p}) => p.match({a: () => trueC(), b: () => 1 as never}))).toThrow()
})
const any2 = (a: Cond, b: Cond) => a.or(b)
const trueC = () => all()
const falseC = () => all().not()

test('loops: a rank that drops proves termination, one that may not is refused', () => {
  const gcd = loop('gcd by subtraction')
    .params({x0: nat, y0: nat})
    .state({x: ({x0}) => x0, y: ({y0}) => y0})
    .pre(({x0, y0}) => x0.atLeast(1).and(y0.atLeast(1)))
    .while(({x, y}) => x.ne(y))
    .body(({x, y}) => ({x: when(x.gt(y), x.minus(y), x), y: when(y.gt(x), y.minus(x), y)}))
  const positive = gcd.law('both stay positive', ({x, y}) => x.atLeast(1).and(y.atLeast(1)))
  expect(proveLoop(gcd.rank(({x, y}) => x.plus(y)), [positive])).toMatchObject({proven: true, checked: true})
  expect(proveLoop(gcd.rank(({x}) => x), [positive]).proven).toBe(false)
})

test('what the types let through, the kernel still refuses', () => {
  // A law reading a request can't be written with the types; forced past them, the kernel refuses it.
  const r: Rule = rule('r')
  const law = {name: 'reads a request', holds: {op: '<=', a: {op: 'var', name: 'c'}, b: {op: 'const', value: 1}}} as const
  expect(() => proveLaws(budget.machine, [law])).toThrow()
  void r
  expect(() => rule('dup').params({a: nat}).inputs({a: nat}).state({z: 0}).machine && interpret(rule('dup').params({a: nat}).inputs({a: nat}).state({z: 0}).machine)).toThrow()
})

test('a name is declared once: an input, a state variable, a flag, a map, a param, each its own', () => {
  const clash = (build: () => unknown) => { try { build(); return '' } catch (e) { return (e as Error).message } }
  expect(clash(() => rule('r').inputs({a: nat}).state({a: 0}).step(({a}) => ({a})).machine)).toBe('r: a is an input and a state variable; give each a name of its own')
  expect(clash(() => rule('r').params({a: nat}).maps({a: 0}).law('l', () => all()))).toContain('a is a param and a map')
  expect(clash(() => rule('r').state({a: 0}).state({a: 1}).machine)).toContain('a is a state variable and declared again')
  expect(clash(() => rule('r').inputs({a: nat}).flags(({a}) => ({a: a.eq(0)})).machine)).toBe('r: a is a flag and an input')
  expect(clash(() => rule('r').inputs({a: nat}).decide('d', () => [], ({a}) => a.atLeast(0)))).toBe('')
  // A flag named again replaces the earlier one (a variant), as before.
  const r = rule('r').inputs({a: nat}).state({s: 0}).flags(({a}) => ({big: a.gt(3)})).flags(({a}) => ({big: a.gt(5)})).step(({big, s}) => ({s: when(big, s.plus(1), s)}))
  expect(clash(() => r.machine)).toBe('')
})

test('relate: two requests under the same params, the second named b.<input>', () => {
  const gate = rule('gate').params({limit: nat}).inputs({user: nat, secret: nat, admin: bool}).assume(({secret}) => secret.atMost(9))
  const allowed = (bug: boolean) => ({limit, user, secret, admin}: DecisionEnv<typeof gate>) => (bug ? user.plus(secret) : user).atMost(limit).or(admin)
  const law = (bug: boolean) => gate.relate('the secret is irrelevant', (a, b) => [a.user.eq(b.user), a.admin.iff(b.admin)], (a, b) => allowed(bug)(a).iff(allowed(bug)(b)))
  expect(proveDecision(law(false))).toMatchObject({proven: true, checked: true})
  const broken = proveDecision(law(true))
  expect(broken.proven).toBe(false)
  // Both copies are drawn and assumed alike (secret ≤ 9 and b.secret ≤ 9).
  expect(law(true).rule.machine.inputs).toEqual(['user', 'secret', 'admin', 'b.user', 'b.secret', 'b.admin'])
  expect(JSON.stringify(law(true).given)).toContain('"name":"b.secret"},"b":{"op":"const","value":9}')
  // On a function: both results, from the same terms the function computes.
  const pick = (bug?: boolean) => fun('pick').inputs({explicit: bool, ambient: nat, user: nat}).returns(({explicit, ambient, user}) => ({target: when(explicit, bug ? ambient : user, user.plus(ambient))}))
  const ni = (bug?: boolean) => pick(bug).relate('an explicit pick ignores the ambient value', (a, b) => [a.explicit, b.explicit, a.user.eq(b.user)], (oa, ob) => oa.target.eq(ob.target))
  expect(proveDecision(ni())).toMatchObject({proven: true, checked: true})
  expect(proveDecision(ni(true)).proven).toBe(false)
})

// A choice, a yes/no or a small upTo is searched over every value it may take, past the bound; a natural only to it.
test('search tries every value of a small kind, whatever the bound', () => {
  const r = rule('fifth case').inputs({op: oneOf('a', 'b', 'c', 'd', 'e'), n: nat}).state({hit: 0}).step(({op, n}) => ({hit: when(op.is('e').and(n.atMost(2)), 1, 0)}))
  expect(search(r.machine, r.law('never the fifth case', ({hit}) => hit.eq(0)))).toEqual({params: {}, trace: [{op: 4, n: 0}]})
  const far = rule('far').inputs({n: nat}).state({hit: 0}).step(({n}) => ({hit: when(n.eq(3), 1, 0)}))
  expect(search(far.machine, far.law('never three', ({hit}) => hit.eq(0)))).toBeUndefined()
  expect(search(far.machine, far.law('never three', ({hit}) => hit.eq(0)), 3, 3)?.trace).toEqual([{n: 3}])
})

// A step law holds from every state the laws allow, reached or not: one broken only from a state no run reaches is
// refused from a random such state, with its witness and no run.
test('a step law broken only from a state no run reaches is refused at once, with the state', () => {
  const r = rule('stays').inputs({go: bool}).state({s: 0}).step(({s}) => ({s}))
  const v = proveSteps(r, [], [r.stepLaw('the count stays at 0', (_, after) => after.s.eq(0))])
  expect(v).toMatchObject({proven: false, stuck: 'sat'})
  expect(v.run).toBeUndefined()
  expect(v.witness!.s).toBeGreaterThan(0)
})

// A choice compares with a name, another choice of its kind or an index, and reads its index as a term.
test('a choice compares by name, by choice or by index', () => {
  const r = rule('phases').inputs({to: oneOf('a', 'b', 'c')}).state({p: oneOf('a', 'b', 'c').from('a')}).step(({to}) => ({p: to}))
  const law = r.stepLaw('the phase is the one asked for', ({to}, after) => all(after.p.eq(to), after.p.index.eq(to.index), after.p.eq('a').implies(after.p.eq(0)), after.p.ne('b').or(to.is('b')), after.p.eq(when(to.is('c'), 2, to.index))))
  expect(proveSteps(r, [], [law])).toMatchObject({proven: true, checked: true})
})
