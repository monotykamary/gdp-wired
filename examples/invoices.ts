// Requests that carry lists: an invoice's lines (a sku, an amount, taxable or not), its total and its taxable part folds
// over them. For the suite (`bun examples/invoices.ts`), core/invoices.test.ts and lean-kernel/package-check.ts.
//   - an invoice is approved when every line is within the cap and the total fits the budget: nothing is spent past
//     the budget, and an approved invoice's lines are each within the cap; the broken variant checks the first line only
//   - the tax recorded is within what is spent, which needs the folds' lemma (the taxable part is within the total, at
//     every prefix), proven by induction over the lines; without the lemma the ledger's law isn't proven
import {type Law} from '../core/machine.ts'
import {type StepLaw, bool, nat, proveSteps, record, rule, when} from '../core/dsl.ts'

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

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'checks the first line only', 'states no lemma'] as const) {
    const r = invoices(bug), v = proveSteps(r, invoiceLaws(r), invoiceSteps(r))
    results.push([`invoices${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
