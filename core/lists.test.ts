// Lists of names (core/dsl.ts lists, ListRef) and laws about every two keys: the normalized scope of examples/lists.ts
// proven, each broken variant refused; the interpreter and the compiled code shift positions alike; every law and step
// law holds on random runs, and each broken variant is broken by one; a law about two keys reads both keys.
import {expect, test} from 'bun:test'
import {interpret, loadJs} from './machine.ts'
import {forall, rule} from './dsl.ts'
import {scope, scopeLaws, scopeSteps} from '../examples/lists.ts'
import {checkStepLaws, obligations, stepLawObligations} from '../kernel/kernel.ts'
import {proveLaws, proveStepLaws} from '../kernel/prove.ts'
import {allowed, watch} from './watch.ts'

test('the normalized scope: proven, through a law about every two positions; each broken variant refused', () => {
  const ok = scope(), r = proveStepLaws(ok.machine, scopeLaws(ok), scopeSteps(ok))
  expect(r).toMatchObject({proven: true, checked: true})
  expect(scopeLaws(ok)[1]).toMatchObject({forall: expect.any(String), forall2: expect.any(String)})
  // Each step law's own instances: without them, the proof no longer checks.
  expect(checkStepLaws(ok.machine, scopeLaws(ok), scopeSteps(ok), {...r.proof!, perStep: undefined})).toBe(false)
  for (const bug of ['skips the right neighbour', 'shifts the wrong way on removal'] as const) expect(proveLaws(scope(bug).machine, scopeLaws(scope(bug))).proven).toBe(false)
}, 300_000)

test('runs: interpreted = compiled; every law holds, and each broken variant is broken by a run', () => {
  let seed = 9
  const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
  for (const bug of [undefined, 'skips the right neighbour', 'shifts the wrong way on removal'] as const) {
    const r = scope(bug), m = r.machine, run = interpret(m), gen = loadJs(m)
    const laws = [...scopeLaws(r), ...(bug ? [] : scopeSteps(r))]
    let broken = false, steps = 0
    for (let t = 0; t < 150 && !broken; t++) {
      let st = run.init({}), g = gen.init({})
      const on = laws.map(l => watch(m, run, l, {}, 6))
      for (let i = 0; i < 10; i++) {
        // Mostly well-placed requests: the position a binary search would give, or a random one.
        const op = (['insert', 'remove'] as const)[rand(2)]!, name = 1 + rand(8), len = st.scalars.Scope_len!
        const cells = Array.from({length: len}, (_, k) => st.maps.Scope!.get(k) ?? 0)
        const at = rand(3) === 0 ? rand(len + 2) : op === 'insert' ? cells.filter(x => x < name).length : Math.max(0, cells.indexOf(name))
        const input = r.encodeInput({op, name, at})
        if (!allowed(m, run, {}, st, input)) continue
        const before = st
        st = run.step({}, st, input); g = gen.step({}, g, input)
        steps++
        expect(g.scalars).toEqual(st.scalars)
        const byKey = (a: [number, number], b: [number, number]) => a[0] - b[0]
        expect([...g.maps.Scope!.entries()].sort(byKey)).toEqual([...st.maps.Scope!.entries()].sort(byKey))
        if (!on.every(w => w.step(before, input, st))) { broken = true; break }
      }
    }
    expect(broken).toBe(bug !== undefined)
    if (!bug) expect(steps).toBeGreaterThan(500)
  }
})

test('a second key comes with a first, and differs from it (laws and step laws)', () => {
  const r = rule('keys').maps({A: 0}).state({n: 0}).step(({n}) => ({n})), m = r.machine
  const holds = {op: '<=', a: {op: 'var', name: 'i'}, b: {op: 'var', name: 'j'}} as const
  expect(() => obligations(m, [{name: 'same key twice', forall: 'i', forall2: 'i', holds}])).toThrow(/second key/)
  expect(() => obligations(m, [{name: 'no first key', forall2: 'j', holds}])).toThrow(/second key/)
  expect(() => stepLawObligations(m, [], {}, {name: 'same key twice', forall: 'i', forall2: 'i', then: holds})).toThrow(/second key/)
  expect(() => stepLawObligations(m, [], {}, {name: 'no first key', forall2: 'j', then: holds})).toThrow(/second key/)
  expect(() => stepLawObligations(m, [], {}, {name: 'two keys', forall: 'i', forall2: 'j', then: holds})).not.toThrow()
})

test('a law about two keys reads both: one about a single key at both places is weaker', () => {
  const r = rule('pairs').maps({A: 0}).state({n: 0}).step(({n}) => ({n}))
  const two = r.law('A is constant', ({A}) => forall((i, j) => A.at(i).eq(A.at(j))))
  expect(two.forall2).toBeDefined()
  expect(two.forall).not.toBe(two.forall2)
  expect(proveLaws(r.machine, [two])).toMatchObject({proven: true, checked: true})
})
