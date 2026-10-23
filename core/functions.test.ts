// Functions from outside the rule (core/dsl.ts fn, divBy, modBy; the kernel's facts): the examples proven and the broken
// variant refused; a law that needs a fact fails without it; the interpreter and the compiled code compute the
// functions alike, and every law holds on random runs (the broken variant broken by one); and the refusals.
import {expect, test} from 'bun:test'
import {type Machine, interpret, loadJs} from './machine.ts'
import {divBy, everyKey, fn, forall, fun, min, modBy, nat, proveDecision, proveRule, rule, upTo} from './dsl.ts'
import {larger, largerLaws, minuteLaws, minutes} from '../examples/functions.ts'
import {checkLaws, obligations} from '../kernel/kernel.ts'
import {proveLaws} from '../kernel/prove.ts'
import {allowed, watch} from './watch.ts'

test('functions known by their facts: proven; the broken variant refused; a law that needs a fact fails without it', () => {
  expect(proveLaws(minutes().machine, minuteLaws())).toMatchObject({proven: true, checked: true})
  const raw = minutes('keeps the raw time')
  expect(proveLaws(raw.machine, minuteLaws(raw)).failed?.goal).toBe('the minute is within the time seen @step')
  const bare: Machine = {...minutes().machine, facts: []}
  expect(proveLaws(bare, minuteLaws()).proven).toBe(false)
  expect(proveLaws(larger.machine, largerLaws)).toMatchObject({proven: true, checked: true})
  expect(proveLaws({...larger.machine, facts: []}, largerLaws).proven).toBe(false)
  // The proof leans on the facts: against the machine without them, or with a weaker one, it no longer checks.
  const r = proveLaws(minutes().machine, minuteLaws())
  expect(checkLaws(minutes().machine, minuteLaws(), r.proof!)).toBe(true)
  expect(checkLaws(bare, minuteLaws(), r.proof!)).toBe(false)
  const weaker: Machine = {...minutes().machine, facts: minutes().machine.facts!.map(f => ({...f, holds: {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}}))}
  expect(checkLaws(weaker, minuteLaws(), r.proof!)).toBe(false)
})

test('the runtimes compute functions alike; every law holds on random runs, and the broken variant is broken by one', () => {
  let seed = 3
  const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
  for (const bug of [undefined, 'keeps the raw time'] as const) {
    const r = minutes(bug), m = r.machine, run = interpret(m), gen = loadJs(m), laws = minuteLaws(r)
    let broken = false
    for (let t = 0; t < 200; t++) {
      const params = {cap: rand(4)}
      let st = run.init(params), g = gen.init(params), time = 0
      const on = laws.map(l => watch(m, run, l, params, 3))
      for (let i = 0; i < 8; i++) {
        time += rand(90)
        const input = {t: time}
        if (!allowed(m, run, params, st, input)) continue
        const before = st
        st = run.step(params, st, input); g = gen.step(params, g, input)
        expect(g.scalars).toEqual(st.scalars)
        if (!on.every(w => w.step(before, input, st))) broken = true
      }
    }
    expect(broken).toBe(bug !== undefined)
  }
  // Two arguments, paired into one key and unpaired by the runtimes.
  const m = larger.machine, run = interpret(m), gen = loadJs(m)
  let st = run.init({}), g = gen.init({})
  for (const a of [3, 0, 7, 2, 1000, 5]) { st = run.step({}, st, {a}); g = gen.step({}, g, {a}) }
  expect(st.scalars).toEqual({high: 1000, seen: 5})
  expect(g.scalars).toEqual(st.scalars)
  // modBy, at the runtimes.
  const clock = rule('clock').inputs({t: nat}).state({hand: 0}).fns({sixty: modBy(60)}).step(({t, sixty}) => ({hand: sixty(t)}))
  expect(interpret(clock.machine).step({}, interpret(clock.machine).init({}), {t: 125}).scalars).toEqual({hand: 5})
})

test('functions: refusals, by name', () => {
  const base = rule('refusals').inputs({t: nat}).state({s: 0}).maps({A: 0})
  // A fact reads the params and the functions alone.
  expect(() => obligations(base.fns({q: divBy(2)}).facts(() => ({})).step(({s}) => ({s})).machine, [])).not.toThrow()
  const withState: Machine = {...base.fns({q: divBy(2)}).step(({s}) => ({s})).machine, facts: [{name: 'reads state', holds: {op: '<=', a: {op: 'var', name: 's'}, b: {op: 'const', value: 1}}}]}
  expect(() => obligations(withState, [])).toThrow(/fact reads state reads s, which it doesn't declare/)
  // A fact is over the naturals, as every law is.
  const negative: Machine = {...base.fns({q: divBy(2)}).step(({s}) => ({s})).machine, facts: [{name: 'negative', holds: {op: '<=', a: {op: 'get', map: 'q', key: {op: 'const', value: 0}}, b: {op: 'const', value: -1}}}]}
  expect(() => obligations(negative, [])).toThrow(/negative constant/)
  // A function is never written.
  const written: Machine = {...base.fns({q: divBy(2)}).step(({s}) => ({s})).machine}
  written.step = {...written.step, maps: {q: {key: {op: 'const', value: 0}, value: {op: 'const', value: 1}}}}
  expect(() => obligations(written, [])).toThrow(/writes the map q, which it doesn't declare/)
  // A condition at every key reads a function at its key nowhere (a function's values don't stop where cells do).
  expect(() => obligations(base.fns({q: divBy(2)}).flags(({A, q}) => ({f: everyKey(k => A.at(k).atMost(q(k)))})).step(({s}) => ({s})).machine, [])).toThrow(/read only in a map's key or a comparison/)
  // A function's js reads its arguments alone.
  const c = 7
  expect(() => base.fns({q: fn(1, (x: number) => x + c)}).step(({s}) => ({s})).machine).toThrow(/reads nothing else/)
})

test('decisions assume the functions\' facts where they read them; fun: a function whose laws are decisions about what it computes', () => {
  // x mod 2^32 of min(left, local) with local < 2^32 is min(left, local): it needs the fact, which the decision now gets.
  const R = 2 ** 32
  const cap = (opts: {bug?: 'narrows before capping', fact?: boolean} = {}) => {
    const f = fun('cap').inputs({left: nat, local: upTo(R - 1)}).fns({narrow: modBy(R)})
    return (opts.fact === false ? f : f.facts(({narrow}) => ({'x < 2^32 ⇒ x mod 2^32 = x': forall(x => x.lt(R).implies(narrow(x).eq(x)))})))
      .returns(({left, local, narrow}) => ({out: opts.bug ? min(narrow(left), local) : narrow(min(left, local))}))
  }
  const lossless = (c: ReturnType<typeof cap>) => c.law('narrowing loses nothing', () => [], (o, {left, local}) => o.out.eq(min(left, local)))
  expect(proveDecision(lossless(cap()))).toMatchObject({proven: true, checked: true})
  expect(proveDecision(lossless(cap({fact: false}))).proven).toBe(false)
  expect(proveDecision(lossless(cap({bug: 'narrows before capping'}))).proven).toBe(false)
  // The facts are hypotheses of the decision's goal (as its Lean export states them), at the arguments it reads.
  expect(lossless(cap()).goal.hyps.length).toBeGreaterThan(lossless(cap({fact: false})).goal.hyps.length)
  // What runs is what was proven: the compiled rule, the broken one broken past 2^32.
  expect(cap().run({left: R + 5, local: 10})).toEqual({out: 10})
  expect(cap({bug: 'narrows before capping'}).run({left: R + 5, local: 10})).toEqual({out: 5})
  // Conditions in the result come back as booleans; a field may share an argument's name.
  const reserve = fun('reserve').params({cost: nat}).inputs({left: nat}).returns(({left, cost}) => ({granted: left.atLeast(cost), left: left.minus(cost)}))
  expect(reserve.run({left: 3}, {cost: 2})).toEqual({granted: true, left: 1})
  expect(reserve.run({left: 1}, {cost: 2})).toEqual({granted: false, left: 0})
  expect(proveDecision(reserve.law('a refusal spends everything left', ({left, cost}) => left.lt(cost), o => o.granted.not().and(o.left.eq(0))))).toMatchObject({proven: true, checked: true})
  expect(proveDecision(reserve.law('a grant leaves something', () => [], o => o.granted.implies(o.left.gt(0)))).proven).toBe(false)
  expect(reserve.rule.machine.state).toEqual({'out.granted': {op: 'const', value: 0}, 'out.left': {op: 'const', value: 0}})
  expect(() => fun('f').inputs({x: nat}).run({x: 1})).toThrow('f: no result (returns)')
})

// The real-world corpus: the random runs skipped every rule that read a function the kernel knows by its facts alone
// (a window's floor(now / w) written with fn), so a false law over one came back unknown. The runs compute it by its
// JavaScript, as the rule runs, with params only where its facts hold; a run that breaks the law refutes it.
test('a false law through a function known by its facts: refuted by a run; params its facts refuse never drawn', () => {
  const win = fn(2, (x: number, d: number) => (d ? Math.floor(x / d) : 0), {facts: f => ({'q(x, d) <= x': forall((x, d) => f(x, d).atMost(x))})})
  // the count is never reset at a new window: past cap, the law breaks
  const r = rule('window').params({cap: nat, w: nat}).fns({win}).inputs({now: nat}).state({count: 0, at: 0})
    .step(({now, count, w, win}) => ({count: count.plus(1), at: win(now, w)}))
  const v = proveRule(r, [r.law('at most cap a window', ({count, cap}) => count.atMost(cap))], {search: {ms: 2000}})
  expect(v).toMatchObject({proven: false, stuck: 'sat'})
  expect(v.run?.trace.length).toBeGreaterThan(0)
  // A fact about the params (fx is f at x, as a recurrence's induction machines take it): a run from params that break
  // it is no run of the rule, so none is drawn and the true law isn't refuted.
  const sq = fn(1, (x: number) => x * x, {facts: f => ({'f(x) >= x': forall(x => f(x).atLeast(x))})})
  const s = rule('square at x').params({x: nat, fx: nat}).fns({sq}).facts(({x, fx, sq}) => ({'fx is sq(x)': fx.eq(sq(x))})).inputs({}).state({y: 0})
    .step(({fx}) => ({y: fx}))
  expect(proveRule(s, [s.law('y is 0 or at least x', ({y, x}) => y.eq(0).or(y.atLeast(x)))], {search: false})).toMatchObject({proven: true, checked: true})
})
