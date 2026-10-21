import {expect, test} from 'bun:test'
import {fold, max, min, nat, proveFold, proveSteps, recur, rule} from './dsl.ts'
import {discover} from './discover.ts'
import {compileFunction} from './machine.ts'
import {foundArea, foundInvoices, foundOrgChart, foundRetries, orgChart, orgChartLaws, retries, retryLaws, retrySteps, tooSoon} from '../examples/discover.ts'

// What `found` gives is source to paste: each entry is a property of an object literal.
const pasted = (src: string[]) => compileFunction<() => Record<string, never>>([], `return {${src.join(', ')}}`)()

test('the backoff delay: the bounds its rule needs, found, and the source pasted back proves the rule', () => {
  const o = foundRetries()
  expect(o.verdict).toMatchObject({proven: true, checked: true})
  expect(o.found).toEqual({delay: {lemmas: ["'f(x) <= 64': (_, f) => f.atMost(64)", "'f(x) >= 1': (_, f) => f.atLeast(1)"]}})
  const delay = recur('backoff', {zero: 1, next: (_, d) => min(d.times(2), 64)}, pasted(o.found.delay!.lemmas!))
  const r = retries().withParts({delay})
  expect(proveSteps(r, retryLaws(r), retrySteps(r))).toMatchObject({proven: true, checked: true})
  // As the rule stated it, refused.
  const bare = retries()
  expect(proveSteps(bare, retryLaws(bare), retrySteps(bare)).proven).toBe(false)
})

test('a closed form fitted exactly: squares is x·x', () => {
  const o = foundArea()
  expect(o.verdict).toMatchObject({proven: true, checked: true})
  expect(o.found).toEqual({sq: {lemmas: ["'f(x) = x·x': (x, f) => f.eq(x.mul(x))"]}})
})

test('a law between two points, where the rule reads the function at two of its params', () => {
  const growing = recur('growing', {zero: 1, next: (_, d) => min(d.times(2), 64)})
  const r = rule('two tiers').params({low: nat, high: nat}).pre(({low, high}) => low.atMost(high)).inputs({}).state({n: 0}).fns({delay: growing})
    .step(({n}) => ({n: n.plus(1)}))
  const laws = [r.law('the low tier waits at most as long as the high one', ({low, high, delay}) => delay(low).atMost(delay(high)))]
  expect(proveSteps(r, laws, []).proven).toBe(false)
  const o = discover(r, laws)
  expect(o.verdict).toMatchObject({proven: true, checked: true})
  expect(o.found).toEqual({delay: {lemmas: ["'f(x) <= 64': (_, f) => f.atMost(64)"], between: ["'f(y) >= f(x)': (_, f, __, g) => g.atLeast(f)"]}})
})

test('a function of two arguments: the bound in the further argument', () => {
  // A bucket filled one a step up to its capacity, read below its capacity's own level: the law needs the bound.
  const filled = recur('filled', {args: ['cap'], zero: 0, next: (_, f, {cap}) => min(f.plus(1), cap)})
  const r = rule('two meters').params({cap: nat}).inputs({}).state({n: 0, level: 0}).fns({filled})
    .step(({n, cap, filled}) => ({n: n.plus(1), level: filled(n, cap)}))
  const laws = [r.law('the level is within the capacity', ({level, cap}) => level.atMost(cap))]
  const o = discover(r, laws)
  expect(o.verdict).toMatchObject({proven: true, checked: true})
  expect(o.found.filled!.lemmas).toEqual(["'f(x) <= cap': (_, f, {cap}) => f.atMost(cap)"])
})

test("a list's folds: the taxable part within the total", () => {
  const o = foundInvoices()
  expect(o.verdict).toMatchObject({proven: true, checked: true})
  expect(o.found).toEqual({Lines: {lemmas: ["'taxed <= total': ({total, taxed}) => taxed.atMost(total)"]}})
})

test("a tree's folds: the reports' lemmas of an org chart, products of the cap among them", () => {
  const f = orgChart()
  expect(proveFold(f, orgChartLaws(f)).proven).toBe(false)
  const o = foundOrgChart()
  expect(o.verdict).toMatchObject({proven: true, checked: true})
  expect(o.found).toEqual([`"the children's cost <= heads·cap": ({cost, heads}, {cap}) => cost.atMost(heads.mul(cap))`, `"the children's depth <= heads": ({depth, heads}) => depth.atMost(heads)`])
  // Pasted into .children, the fold as stated proves its laws.
  const g = fold('org chart').params({cap: nat}).inputs({pay: nat})
    .leaf(({pay, cap}) => ({cost: min(pay, cap), heads: 1, depth: 0}))
    .children({cost: 0, heads: 0, depth: 0}, (acc, kid) => ({cost: acc.cost.plus(kid.cost), heads: acc.heads.plus(kid.heads), depth: max(acc.depth, kid.depth.plus(1))}), pasted(o.found))
    .node(({pay, cap}, kids) => ({cost: kids.cost.plus(min(pay, cap)), heads: kids.heads.plus(1), depth: kids.depth}))
  expect(proveFold(g, orgChartLaws(g as never))).toMatchObject({proven: true, checked: true})
}, 60_000)

test('a law that does not hold stays unproven', () => {
  expect(tooSoon().verdict.proven).toBe(false)
})
