// Division and remainder by a constant, and signed integers: for the suite (`bun examples/arith.ts`),
// core/arith.test.ts and lean-kernel/package-check.ts. Each `x.modBy(k)` and `x.divBy(k)` is the rule's function mod$k or
// div$k read at x, which the kernel knows by x = k·(x div k) + x mod k and x mod k < k: nothing new is trusted, and the
// Lean export proves both facts of Lean's own x / k and x % k by omega.
//   - a rota: the day of the week is the day count mod 7, and the shift lead turns over every 7 days; the weekday stays
//     below 7, and the lead is the week number mod 3 (broken: the lead is the day count mod 3)
//   - billing by the started quarter hour: 15 minutes a block, a started block billed whole; the billed time covers
//     the time used and overshoots it by less than a block (broken: the blocks rounded down)
//   - a pair dispenser: tickets go out two at a time, so the count stays even, and no request ever leaves it at 7 (an
//     invariant nobody wrote: inferLaws finds "issued mod 2 = 0"); broken: an odd refill
//   - a signed ledger: a balance that moves by ±3 from 0, read as an integer; it stays a multiple of 3 below zero too
//     (Euclid's remainder of a negative balance is still in 0..2), and its quotient by 3 counts the moves net (broken:
//     a fee of 1)
import {type Law} from '../core/machine.ts'
import {type Verdict, bool, nat, oneOf, proveRule, rule, when} from '../core/dsl.ts'
import {inferLaws} from '../core/infer.ts'

export const rota = (bug?: 'lead by the day') => rule('rota').inputs({}).state({day: 0, weekday: 0, lead: 0})
  .step(({day}) => {
    const next = day.plus(1)
    return {day: next, weekday: next.modBy(7), lead: bug ? next.modBy(3) : next.divBy(7).modBy(3)}
  })
export const rotaLaws = (r = rota()): Law[] => [
  r.law('the weekday is below 7', ({weekday}) => weekday.lt(7)),
  r.law('the weekday is the day mod 7', ({weekday, day}) => weekday.eq(day.modBy(7))),
  r.law('the lead is the week mod 3', ({lead, day}) => lead.eq(day.divBy(7).modBy(3))),
]

export const billing = (bug?: 'rounds down') => rule('quarter-hour billing').inputs({minutes: nat}).state({used: 0, billed: 0})
  .step(({minutes, used}) => {
    const total = used.plus(minutes)
    return {used: total, billed: (bug ? total : total.plus(14)).divBy(15).times(15)}
  })
export const billingLaws = (r = billing()): Law[] => [
  r.law('the bill covers the time used', ({used, billed}) => used.atMost(billed)),
  r.law('the bill is less than a block over', ({used, billed}) => billed.lt(used.plus(15))),
]

export const pairs = (bug?: 'odd refill') => rule('pair dispenser').inputs({op: oneOf('issue', 'refill'), n: nat}).state({issued: 0})
  .step(({op, issued}) => ({issued: op.match({issue: () => issued.plus(2), refill: () => (bug ? issued.plus(3) : issued.plus(4))})}))
export const pairsLaw = (r = pairs()): Law => r.law('never 7 issued', ({issued}) => issued.eq(7).not())
export const evenLaw = (r = pairs()): Law => r.law('issued in pairs', ({issued}) => issued.modBy(2).eq(0))

export const ledger = (bug?: 'a fee of 1') => rule('signed ledger').inputs({up: bool}).ints({balance: 0, net: 0})
  .step(({up, balance, net}) => ({balance: when(up, balance.plus(3), balance.minus(bug ? 4 : 3)), net: when(up, net.plus(1), net.minus(1))}))
export const ledgerLaws = (r = ledger()): Law[] => [
  r.law('the balance is a multiple of 3', ({balance}) => balance.modBy(3).eq(0)),
  r.law('a third of the balance is the net count', ({balance, net}) => balance.divBy(3).eq(net)),
]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  const check = (what: string, v: Verdict, want: boolean) => results.push([what, v.proven && v.checked, want])
  for (const bug of [undefined, 'lead by the day'] as const) check(`rota${bug ? ` (${bug})` : ''}`, proveRule(rota(bug), rotaLaws(rota(bug)), {search: false}), !bug)
  for (const bug of [undefined, 'rounds down'] as const) check(`billing${bug ? ` (${bug})` : ''}`, proveRule(billing(bug), billingLaws(billing(bug)), {search: false}), !bug)
  check('pair dispenser, issued in pairs', proveRule(pairs(), [evenLaw()], {search: false}), true)
  for (const bug of [undefined, 'odd refill'] as const) {
    const r = pairs(bug), v = inferLaws(r, [pairsLaw(r)], [], {ms: 10000})
    check(`pair dispenser, never 7, by inferLaws${bug ? ` (${bug})` : ''}`, v, !bug)
    for (const f of v.found) console.log(`     found: ${f.text}`)
  }
  for (const bug of [undefined, 'a fee of 1'] as const) check(`signed ledger${bug ? ` (${bug})` : ''}`, proveRule(ledger(bug), ledgerLaws(ledger(bug)), {search: false}), !bug)
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
