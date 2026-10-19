// Lists a request carries (core/dsl.ts carriesList): items as carried maps, folds as carried maps of running values the
// encoding computes and every request is assumed to meet, lemmas about the folds proven by induction. The invoices of
// examples/invoices.ts proven, their broken variants refused, the builders cross-checked, the compiled rule run on
// real lists.
import {expect, test} from 'bun:test'
import {Unproven, nat, proveSteps, record, rule} from './dsl.ts'
import {Line, invoiceLaws, invoiceSteps, invoices, metered, meteredLaws} from '../examples/invoices.ts'

test('a list a request carries: proven, cross-checked, the broken variants refused', () => {
  const r = invoices(), laws = invoiceLaws(r), steps = invoiceSteps(r)
  expect(proveSteps(r, laws, steps)).toMatchObject({proven: true, checked: true})
  expect(r.crossCheck(laws, steps).failure).toBeUndefined()
  for (const bug of ['checks the first line only', 'states no lemma'] as const) {
    const b = invoices(bug)
    expect(proveSteps(b, invoiceLaws(b), invoiceSteps(b)).proven).toBe(false)
  }
})

test('the compiled rule on real lists: folds computed, the request refused or approved as the code would', () => {
  const r = invoices(), gen = r.compiled(), ps = r.encodeParams({budget: 100, cap: 40})
  let st = gen.init(ps)
  const line = (amount: number, taxable = false, sku = 1) => ({sku, amount, taxable})
  for (const lines of [[line(30, true), line(20)], [line(45)], [line(10, true), line(30, true)], [line(25)], []]) st = gen.step(ps, st, r.encodeInput({Lines: lines}))
  expect(r.decode(st)).toMatchObject({spent: 90, tax: 70, approved: 3})
  const enc = r.encodeInput({Lines: [line(3, true), line(4)]})
  expect(enc['Lines_len']).toBe(2)
  expect([...(enc['Lines$total'] as Map<number, number>)]).toEqual([[1, 3], [2, 7]])
  expect([...(enc['Lines$taxed'] as Map<number, number>)]).toEqual([[1, 3], [2, 3]])
  expect(() => r.encodeInput({Lines: [{sku: 1, amount: 2}] as never})).toThrow(RangeError)
  expect(() => r.encodeInput({Lines: 3 as never})).toThrow(RangeError)
})

test('a fold lemma that does not hold is refused', () => {
  const made = () => rule('x').carriesList('Lines', record({amount: nat}), {total: {from: 0, step: (acc, l) => acc.plus(l.amount)}}, {'at most 10': ({total}) => total.atMost(10)})
  expect(made).toThrow(Unproven)
  void Line
})

test('folds that read the params: proven, the broken lemma refused, computed with the params a request is encoded with', () => {
  const r = metered(), laws = meteredLaws(r)
  expect(proveSteps(r, laws, [])).toMatchObject({proven: true, checked: true})
  expect(r.crossCheck(laws, []).failure).toBeUndefined()
  expect(() => metered('charges at least the ceiling')).toThrow(Unproven)
  const params = {budget: 100, ceil: 25, fee: 5}, gen = r.compiled(), ps = r.encodeParams(params)
  const line = (amount: number) => ({sku: 1, amount, taxable: false})
  const enc = r.encodeInput({Lines: [line(30), line(10)]}, params)
  expect([...(enc['Lines$charged'] as Map<number, number>)]).toEqual([[0, 5], [1, 30], [2, 40]])
  let st = gen.init(ps)
  for (const lines of [[line(30), line(10)], [line(60), line(60)], [line(20)]]) st = gen.step(ps, st, r.encodeInput({Lines: lines}, params))
  expect(r.decode(st)).toMatchObject({spent: 95, listed: 160, fees: 10}) // 40, then 55 (each line up to 25, the fee 5), then 25 past the budget
  expect(() => r.encodeInput({Lines: [line(1)]})).toThrow(/read the params/)
})
