// Lists of names (core/dsl.ts lists, ListRef) and laws about every two keys: the normalized scope of examples/lists.ts
// proven, each broken variant refused; the interpreter and the compiled code shift positions alike; every law and step
// law holds on random runs, and each broken variant is broken by one; a law about two keys reads both keys.
import {expect, test} from 'bun:test'
import {interpret, loadJs} from './machine.ts'
import {forall, rule} from './dsl.ts'
import {bits, bitsLaws, scope, scopeLaws, scopeSteps} from '../examples/lists.ts'
import {checkStepLaws, obligations, stepLawObligations} from '../kernel/kernel.ts'
import {proveLaws, proveStepLaws} from '../kernel/prove.ts'
import {allowed, watch} from './watch.ts'
import {certReport, toLean} from '../lean-kernel/emit.ts'

// Its usual proof with the step law translated into one cyclic proof (core/translate.ts) by the Lean export: the
// translated leaves index the rows as kernel.ts lists them, so the kernel's check accepts them (two forms of one atom,
// their names in different orders, once made the rows past the facts differ and the step's node refused: the export
// then searched the step law's node, a file 2.4 times as large).
test('the normalized scope: its step law translated for the Lean export, checked by the kernel', () => {
  const ok = scope(), text = toLean([{id: 'scope', machine: ok.machine, laws: scopeLaws(ok), stepLaws: scopeSteps(ok)}])
  expect(certReport.cyclic).toEqual(['scope'])
  expect(certReport.translatedSteps).toEqual([ok.machine.name])
  expect(text.length).toBeLessThan(250_000)
})

test('the normalized scope: proven, through a law about every two positions; each broken variant refused', () => {
  const ok = scope(), r = proveStepLaws(ok.machine, scopeLaws(ok), scopeSteps(ok))
  expect(r).toMatchObject({proven: true, checked: true})
  expect(scopeLaws(ok)[1]).toMatchObject({forall: expect.any(String), keys: [expect.any(String)]})
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

test('further keys come with a first, each a different name (laws and step laws)', () => {
  const r = rule('keys').maps({A: 0}).state({n: 0}).step(({n}) => ({n})), m = r.machine
  const holds = {op: '<=', a: {op: 'var', name: 'i'}, b: {op: 'var', name: 'j'}} as const
  expect(() => obligations(m, [{name: 'same key twice', forall: 'i', keys: ['i'], holds}])).toThrow(/further keys/)
  expect(() => obligations(m, [{name: 'no first key', keys: ['j'], holds}])).toThrow(/further keys/)
  expect(() => stepLawObligations(m, [], {}, {name: 'same key twice', forall: 'i', keys: ['i'], then: holds})).toThrow(/further keys/)
  expect(() => stepLawObligations(m, [], {}, {name: 'no first key', keys: ['j'], then: holds})).toThrow(/further keys/)
  expect(() => stepLawObligations(m, [], {}, {name: 'two keys', forall: 'i', keys: ['j'], then: holds})).not.toThrow()
})

test('a law about two keys reads both: one about a single key at both places is weaker', () => {
  const r = rule('pairs').maps({A: 0}).state({n: 0}).step(({n}) => ({n}))
  const two = r.law('A is constant', ({A}) => forall((i, j) => A.at(i).eq(A.at(j))))
  expect(two.keys).toHaveLength(1)
  expect(two.forall).not.toBe(two.keys![0])
  expect(proveLaws(r.machine, [two])).toMatchObject({proven: true, checked: true})
})

test('three keys: any three bits repeat a value; writing the key breaks it, and a run shows it', () => {
  const laws = bitsLaws()
  expect(laws[1]!.keys).toHaveLength(2)
  expect(proveLaws(bits().machine, laws)).toMatchObject({proven: true, checked: true})
  const bad = bits('writes the key')
  expect(proveLaws(bad.machine, bitsLaws(bad)).proven).toBe(false)
  // A claim false only at the further keys is refused: those keys are every key too, not read at one.
  const r = bits(), two = r.law('two cells agree', ({A}) => forall((i, j, k) => A.at(i).atMost(1).and(A.at(j).eq(A.at(k)))))
  expect(proveLaws(r.machine, [laws[0]!, two]).proven).toBe(false)
  // The watcher reads a law about three keys at every triple: cells 1 and 2 written with 1 and 2 beside cell 0's 0 break it.
  const m = bad.machine, run = interpret(m), w = watch(m, run, bitsLaws(bad)[1]!, {}, 3)
  let st = run.init({})
  const steps: [number, number][] = [[0, 0], [1, 0], [2, 0]]
  const held = steps.map(([at, b]) => { const before = st; st = run.step({}, st, {at, b}); return w.step(before, {at, b}, st) })
  expect(held).toEqual([true, true, false])
})
