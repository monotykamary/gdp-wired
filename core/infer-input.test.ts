import {expect, test} from 'bun:test'
import {oneOf, rule, when} from './dsl.ts'
import {inferLaws} from './infer.ts'

const steps = () => rule('inference input stays unchanged')
  .inputs({go: oneOf('up', 'down', 'stay')}).state({x: 0})
  .step(({go, x}) => ({x: when(go.is('up'), x.plus(2), when(go.is('down'), x.minus(2), x))}))

test('remainder inference leaves the original facts for a second inference on the same rule', () => {
  const r = steps(), law = r.law('x is never 7', ({x}) => x.ne(7)), original = r.machine
  const first = inferLaws(r, [law], [], {ms: 15000})
  expect(first).toMatchObject({proven: true, checked: true})
  expect(first.found.map(f => f.text)).toContain('x mod 2 = 0')
  expect(r.machine).toEqual(original)
  expect(r.machine.facts).toEqual(original.facts)
  const second = inferLaws(r, [law], [], {ms: 15000, remainders: false})
  expect(second).toMatchObject({proven: true, checked: true})
  expect(second.found.map(f => f.source)).toContain("r.law('∃k. x = 2·k', ({x}) => exists(k => x.eq(k.times(2))))")
  expect(r.machine).toEqual(original)
  expect(r.machine.facts).toEqual(original.facts)
}, 60000)

test('inference retains existing divisor declarations without adding its own', () => {
  const r = steps().dividesBy(3), law = r.law('x is never 7', ({x}) => x.ne(7)), original = r.machine
  // Existing unrelated arithmetic facts may leave this search inconclusive;
  // neither successful nor inconclusive inference may change those facts.
  inferLaws(r, [law], [], {ms: 15000})
  expect(r.machine).toEqual(original)
  expect(r.machine.fns).toHaveProperty('mod$3')
  expect(r.machine.fns).not.toHaveProperty('mod$2')
}, 30000)

test('divisors mentioned by input laws are private to the inference call', () => {
  const r = steps(), donor = r.withDivisors(2)
  const law = donor.law('x is even', ({x}) => x.modBy(2).eq(0)), original = r.machine
  expect(inferLaws(r, [law], [], {ms: 15000})).toMatchObject({proven: true, checked: true})
  expect(r.machine).toEqual(original)
  expect(r.machine.fns).not.toHaveProperty('mod$2')
}, 30000)
