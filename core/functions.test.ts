// Functions from outside the rule (core/dsl.ts fn, divBy, modBy; the kernel's facts): the examples proven and the broken
// variant refused; a law that needs a fact fails without it; the interpreter and the compiled code compute the
// functions alike, and every law holds on random runs (the broken variant broken by one); and the refusals.
import {expect, test} from 'bun:test'
import {type Machine, interpret, loadJs} from './machine.ts'
import {divBy, everyKey, fn, modBy, nat, rule} from './dsl.ts'
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
