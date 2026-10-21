// Requests that carry lists: an invoice's lines (a sku, an amount, taxable or not), its total and its taxable part folds
// over them. For the suite (`bun examples/invoices.ts`), core/invoices.test.ts and lean-kernel/package-check.ts.
//   - an invoice is approved when every line is within the cap and the total fits the budget: nothing is spent past
//     the budget, and an approved invoice's lines are each within the cap; the broken variant checks the first line only
//   - the tax recorded is within what is spent, which needs the folds' lemma (the taxable part is within the total, at
//     every prefix), proven by induction over the lines; without the lemma the ledger's law isn't proven
//   - metered invoices: a fold that reads the params (each line charged up to a ceiling, a fee to start), its lemma
//     reading them too (the charge is within the total and the fee); a variant that charges at least the ceiling
//     breaks the lemma and is refused when the rule is built
import {type Law} from '../core/machine.ts'
import {type StepLaw, bool, max, min, nat, proveSteps, record, rule, when} from '../core/dsl.ts'

export const Line = record({sku: nat, amount: nat, taxable: bool})
export const invoices = (bug?: 'checks the first line only' | 'states no lemma') => rule('invoices')
  .params({budget: nat, cap: nat})
  .carriesList('Lines', Line, {
    total: {from: 0, step: (acc, l) => acc.plus(l.amount)},
    taxed: {from: 0, step: (acc, l) => acc.plus(when(l.taxable, l.amount, 0))},
  }, bug === 'states no lemma' ? {} : {'the taxable part is within the total': ({taxed, total}) => taxed.atMost(total)})
  .state({spent: 0, tax: 0, approved: 0})
  .flags(({Lines, cap, budget, spent}) => ({
    small: bug === 'checks the first line only' ? Lines.at(0).amount.atMost(cap) : Lines.every(l => l.amount.atMost(cap)),
    fits: spent.plus(Lines.fold.total).atMost(budget),
  }))
  .step(({Lines, spent, tax, approved, small, fits}) => {
    const ok = small.and(fits)
    return {spent: when(ok, spent.plus(Lines.fold.total), spent), tax: when(ok, tax.plus(Lines.fold.taxed), tax), approved: when(ok, approved.plus(1), approved)}
  })
export const invoiceLaws = (r = invoices()): Law[] => [
  r.law('nothing is spent past the budget', ({spent, budget}) => spent.atMost(budget)),
  r.law('the tax recorded is within what is spent', ({tax, spent}) => tax.atMost(spent)),
]
export const invoiceSteps = (r = invoices()): StepLaw[] => [
  r.stepLaw('an approved invoice has every line within the cap', ({Lines, cap, approved}, after) => after.approved.gt(approved).implies(Lines.every(l => l.amount.atMost(cap)))),
]

export const metered = (bug?: 'charges at least the ceiling') => rule('metered invoices')
  .params({budget: nat, ceil: nat, fee: nat})
  .carriesList('Lines', Line, {
    total: {from: 0, step: (acc, l) => acc.plus(l.amount)},
    charged: {from: ({fee}) => fee, step: (acc, l, {ceil}) => acc.plus(bug ? max(l.amount, ceil) : min(l.amount, ceil))},
  }, {'the charge is within the total and the fee': ({charged, total}, _, {fee}) => charged.atMost(total.plus(fee))})
  .state({spent: 0, listed: 0, fees: 0})
  .flags(({Lines, budget, spent}) => ({fits: spent.plus(Lines.fold.charged).atMost(budget)}))
  .step(({Lines, fee, spent, listed, fees, fits}) => ({
    spent: when(fits, spent.plus(Lines.fold.charged), spent), listed: when(fits, listed.plus(Lines.fold.total), listed), fees: when(fits, fees.plus(fee), fees),
  }))
export const meteredLaws = (r = metered()): Law[] => [
  r.law('nothing is spent past the budget', ({spent, budget}) => spent.atMost(budget)),
  r.law('what is spent is within what was listed and the fees', ({spent, listed, fees}) => spent.atMost(listed.plus(fees))),
]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'checks the first line only', 'states no lemma'] as const) {
    const r = invoices(bug), v = proveSteps(r, invoiceLaws(r), invoiceSteps(r), {search: false})
    results.push([`invoices${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  // With the search (the default), the lemma nobody stated is found and proven.
  { const r = invoices('states no lemma'), v = proveSteps(r, invoiceLaws(r), invoiceSteps(r)); results.push(['invoices (states no lemma), the lemma found', v.proven && v.checked && !!v.found?.lemmas?.Lines, true]) }
  { const v = proveSteps(metered(), meteredLaws(), []); results.push(['metered invoices', v.proven && v.checked, true]) }
  try { metered('charges at least the ceiling'); results.push(['metered invoices (charges at least the ceiling)', true, false]) } catch { results.push(['metered invoices (charges at least the ceiling)', false, false]) }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
