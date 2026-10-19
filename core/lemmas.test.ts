// Functions defined by a recurrence (core/dsl.ts recur) and the lemmas stated about them: each lemma proven by induction
// when the function is made, then a fact every rule that reads the function may use. A retry schedule with exponential
// backoff needs two of them (the delay is at least 1 and at most 64): with them its laws are proven, without them
// they aren't (the two equations alone say nothing about the delay at an unknown attempt); a lemma that doesn't hold
// is refused with the induction step it breaks at; the runtimes compute the function by its recurrence.
import {expect, test} from 'bun:test'
import {Unproven, min, modBy, nat, proveLeadsTo, proveSteps, recur, rule, when} from './dsl.ts'
import {area, areaLaws, backoff, escalation, escalationLaws, fillMeter, fillMeterLaws, filled, growing, ladder, ladderLaws, ledger, ledgerLaws, leftovers, pump, pumpLive, retries, retryLaws, retrySteps, tank, tankLaws} from '../examples/lemmas.ts'
import {fnValue} from './machine.ts'

test('lemmas proven by induction, then used: the backoff schedule proven with them, not without', () => {
  expect(backoff().verdict).toMatchObject({proven: true, checked: true})
  const r = retries(), laws = retryLaws(r), steps = retrySteps(r)
  expect(proveSteps(r, laws, steps)).toMatchObject({proven: true, checked: true})
  expect(r.crossCheck(laws, steps).failure).toBeUndefined()
  // The equations alone: true of the delay, but no proof without induction.
  const bare = retries('states no lemma')
  expect(proveSteps(bare, retryLaws(bare), retrySteps(bare)).proven).toBe(false)
  // The facts the rule assumes: the two equations and both lemmas.
  expect(r.machine.facts?.map(f => f.name)).toEqual(['delay: delay(0)', 'delay: delay(x + 1)', 'delay: at least 1', 'delay: at most 64'])
})

test('a lemma that is not proven is refused, with the step it breaks at; lemmas lean on each other', () => {
  const made = () => recur('delay', {zero: 1, next: (_, d) => min(d.times(2), 64)}, {'at most 32': (_, d) => d.atMost(32)})
  expect(made).toThrow(Unproven)
  try { made() } catch (e) { expect((e as Unproven).verdict.witness).toBeDefined() }
  // Two by two for five steps: "at most 10" alone isn't inductive (from 10, a step adds 2), "at most 2x" is; together
  // both are proven, as a law leans on another.
  const twos = (lemmas: Parameters<typeof recur>[2]) => () => recur('twos', {zero: 0, next: (x, y) => when(x.lt(5), y.plus(2), y)}, lemmas)
  expect(twos({'at most 10': (_, y) => y.atMost(10)})).toThrow(Unproven)
  expect(twos({'at most 10': (_, y) => y.atMost(10), 'at most 2x': (x, y) => y.atMost(x.times(2))})().verdict).toMatchObject({proven: true, checked: true})
  expect(() => recur('bad', {zero: 0, next: (_, p) => p.plus(1)}, {'reads another value': () => nat.value('y').atMost(1)})).toThrow(/reads y/)
  expect(() => recur('bad name', {zero: 0, next: (_, p) => p})).toThrow(/plain name/)
})

test('the runtimes compute it by its recurrence', () => {
  const r = retries(), gen = r.compiled(), run = r.interpreter()
  let st = gen.init({}), si = run.init({})
  const seen: number[] = []
  for (let t = 0; t < 400; t += 1) {
    const input = r.encodeInput({op: t % 7 === 6 ? 'ok' : 'fail', now: t})
    st = gen.step({}, st, input); si = run.step({}, si, input)
    expect(st.scalars).toEqual(si.scalars)
    seen.push(st.scalars.next! - t)
  }
  expect(Math.max(...seen)).toBeLessThanOrEqual(64)
  const f = (x: number) => fnValue(r.machine.fns!.delay!, x)
  expect([0, 1, 2, 3, 6, 7, 50].map(f)).toEqual([1, 2, 4, 8, 64, 64, 64])
})

test('recurrences of several arguments, reading other functions, and laws between two points', () => {
  for (const f of [filled(), leftovers(), growing()]) expect(f.verdict).toMatchObject({proven: true, checked: true})
  for (const [r, laws] of [[fillMeter(), fillMeterLaws], [ledger(), ledgerLaws], [escalation(), escalationLaws], [ladder(), ladderLaws], [tank(), tankLaws], [area(), areaLaws]] as const) {
    expect(proveSteps(r as never, laws(r as never), [])).toMatchObject({proven: true, checked: true})
    expect((r as ReturnType<typeof fillMeter>).crossCheck(laws(r as never)).failure).toBeUndefined()
  }
  // Liveness whose helpful request is allowed by a fact about two keys.
  const p = pump()
  expect(proveLeadsTo(p, [], pumpLive(p))).toMatchObject({proven: true, checked: true})
  // The runtimes: two arguments unpaired from one key, another function inlined.
  const m = fillMeter().machine, l = ledger().machine
  const key = (a: number, b: number) => (a + b) * (a + b) + b
  expect([[0, 5], [3, 5], [9, 5], [9, 20]].map(([x, c]) => fnValue(m.fns!.filled!, key(x!, c!)))).toEqual([0, 3, 5, 9])
  expect([0, 1, 7, 8, 14].map(x => fnValue(l.fns!.left!, x))).toEqual([0, 0, 21, 21, 42])
  expect(Object.keys(l.fns!)).toEqual(['left.rem', 'left'])
  // A law between two points that doesn't hold, and one that holds only with the lemma it leans on.
  expect(() => recur('shrinks', {zero: 64, next: (_, d) => d.minus(1)}, {}, {'never shrinks': (_, d, __, e) => d.atMost(e)})).toThrow(Unproven)
  expect(() => recur('filled', {args: ['cap'], zero: 0, next: (_, f, {cap}) => min(f.plus(1), cap)}, {}, {'never drains': (_, f, __, g) => f.atMost(g)})).toThrow(Unproven)
  // Without "at most 6 a day", the ledger's law isn't proven: the remainder's fact alone bounds one day, not the sum.
  const bare = rule('bare ledger').inputs({}).state({day: 0, total: 0}).fns({left: recur('leftovers', {fns: {rem: modBy(7)}, zero: 0, next: (x, t, {rem}) => t.plus(rem(x))})})
    .step(({day, left}) => ({day: day.plus(1), total: left(day.plus(1))}))
  expect(proveSteps(bare, [bare.law('at most 6 a day so far', ({total, day}) => total.atMost(day.times(6)))], []).proven).toBe(false)
  expect(() => recur('f', {args: ['x'], zero: 0, next: (_, p) => p})).toThrow(/taken/)
  expect(() => recur('f', {args: ['a', 'b', 'c', 'd', 'e'] as const, zero: 0, next: (_, p) => p})).toThrow(/at most four/)
}, 300_000)

test('a start that reads a function, four further arguments, and a runtime that keeps its place', () => {
  // f(0, a) = a mod 5, f(x + 1, a) = f(x, a) + 1: at least the start, by the remainder's facts.
  const shifted = recur('shifted', {args: ['a'], fns: {rem: modBy(5)}, zero: ({a, rem}) => rem(a), next: (_, f) => f.plus(1)}, {
    'below 5 plus the steps': (x, f) => f.lt(x.plus(5)),
  })
  expect(shifted.verdict).toMatchObject({proven: true, checked: true})
  // Four further arguments, a law between two points.
  const four = recur('four', {args: ['a', 'b', 'c', 'd'], zero: ({a}) => a, next: (_, f, {b, c, d}) => f.plus(min(b, min(c, d)))}, {
    'at least a': (_, f, {a}) => f.atLeast(a),
  }, {'never shrinks': (_, f, __, g) => f.atMost(g)})
  expect(four.verdict).toMatchObject({proven: true, checked: true})
  // The runtime: values at growing x continue from the last, at a smaller x start over, per tuple of arguments.
  const g = rule('reads').params({a: nat}).inputs({x: nat}).state({v: 0}).fns({shifted}).step(({x, a, shifted}) => ({v: shifted(x, a)}))
  const at = (x: number, a: number) => fnValue(g.machine.fns!.shifted!, (x + a) * (x + a) + a)
  expect([at(0, 7), at(3, 7), at(10, 7), at(2, 7), at(4, 9), at(10, 7)]).toEqual([2, 5, 12, 4, 8, 12])
})
