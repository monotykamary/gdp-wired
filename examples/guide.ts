// The guide's code (gdpwired.dev/guide), kept here so it type-checks, proves and runs (the suite runs this file). The
// page shows each block importing from 'gdp-wired'; what each comment says a call returns is asserted below it.
//   bun examples/guide.ts
import {bool, forall, fun, min, nat, oneOf, proveDecision, proveRule, proveSteps, record, rule, when} from '../core/dsl.ts'
import {search} from '../core/machine.ts'

const failures: string[] = []
const expect = (what: string, got: unknown, want: unknown) => {
  const same = JSON.stringify(got) === JSON.stringify(want)
  if (!same) failures.push(`${what}: got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`)
}
const verdict = (v: {proven: boolean, checked: boolean}) => ({proven: v.proven, checked: v.checked})

// --- 1. The rule your code already has ----------------------------------------------------------------------------------
// What the app does today: admit a request of cost `cost` while `spent` is under `budget`, at most `maxPerRequest` each.
let spent = 0
function admit(cost: number, budget: number, maxPerRequest: number) {
  if (spent < budget) spent += Math.min(cost, maxPerRequest)
}
for (const c of [50, 40, 70, 20]) admit(c, 100, 30)
expect('the plain code', spent, 110)

// --- 2. The same rule, written for the prover ---------------------------------------------------------------------------
const budget = rule('budget')
  .params({b: nat, m: nat})   // fixed for the run: the budget, the cap per request
  .inputs({c: nat})           // what each request brings: its cost
  .state({s: 0})              // what is kept between requests: the spend, from 0
  .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))

// --- 3. What must always be true ----------------------------------------------------------------------------------------
const bounded = budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))

// --- 4. Prove it --------------------------------------------------------------------------------------------------------
expect('proven', verdict(proveRule(budget, [bounded])), {proven: true, checked: true})

// --- 5. Break it on purpose ---------------------------------------------------------------------------------------------
const uncapped = budget.step(({b, c, s}) => ({s: when(s.lt(b), s.plus(c), s)}))
const refused = proveRule(uncapped, [bounded])
expect('refused', {proven: refused.proven, goal: refused.goal, stuck: refused.stuck}, {proven: false, goal: 'spend stays within b + m @step', stuck: 'sat'})
expect('the breaking run', search(uncapped.machine, bounded), {params: {b: 1, m: 0}, trace: [{c: 2}]})

// --- 6. Use it in the app -----------------------------------------------------------------------------------------------
const shipped = budget.compiled()
const params = budget.encodeParams({b: 100, m: 30})
let st = shipped.init(params)
for (const c of [50, 40, 70, 20]) st = shipped.step(params, st, budget.encodeInput({c}))
expect('the shipped rule', budget.decode(st), {s: 110})
// Or keep your own code, and hold it to the rule.
const held = budget.compare({
  init: () => ({s: 0}),
  step: ({b, m}, state, {c}) => ({s: state.s < b ? state.s + Math.min(c, m) : state.s}),
})
expect('your code agrees', held.failure, undefined)
const wrong = budget.compare({init: () => ({s: 0}), step: ({b}, state, {c}) => ({s: state.s < b ? state.s + c : state.s})})
expect('a wrong copy is caught', typeof wrong.failure, 'string')

// --- 7. In your tests ---------------------------------------------------------------------------------------------------
expect('crossCheck', budget.crossCheck([bounded]).failure, undefined)

// --- Recipes ------------------------------------------------------------------------------------------------------------
// Limits per key: each account is granted once, and no day passes its cap.
const caps = rule('caps')
  .params({d: nat})
  .inputs({acct: nat, day: nat, ok: bool})
  .maps({Acct: 0, Day: 0})
  .flags(({ok, acct, day, d, Acct, Day}) => ({
    granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d)),
  }))
  .step(({acct, day, granted, Acct, Day}) => ({
    Acct: Acct.bump(acct, granted),
    Day: Day.bump(day, granted),
  }))
const dayCap = caps.law('no day passes its cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))
const once = caps.law('no account is granted twice', ({Acct}) => forall(k => Acct.at(k).atMost(1)))
expect('caps', verdict(proveRule(caps, [dayCap, once])), {proven: true, checked: true})

// A workflow: an order is paid, then shipped; a refund only before shipping.
const order = rule('order')
  .inputs({op: oneOf('pay', 'ship', 'refund')})
  .state({status: oneOf('new', 'paid', 'shipped', 'refunded').from('new')})
  .flags(({op, status}) => ({
    paying: op.is('pay').and(status.is('new')),
    shipping: op.is('ship').and(status.is('paid')),
    refunding: op.is('refund').and(status.is('paid')),
  }))
  .step(({paying, shipping, refunding, status}) => ({
    status: when(paying, 'paid', when(shipping, 'shipped', when(refunding, 'refunded', status))),
  }))
const neverRefunded = order.stepLaw('a shipped order is never refunded',
  (_, after) => after.status.is('refunded').not(), ({status}) => status.is('shipped'))
const paidFirst = order.stepLaw('only a paid order ships',
  ({status}, after) => after.status.is('shipped').implies(status.is('paid').or(status.is('shipped'))),
)
expect('order', verdict(proveSteps(order, [], [neverRefunded, paidFirst])), {proven: true, checked: true})

// A permission check: a pure function, and what it must never allow.
const canEdit = fun('can edit')
  .inputs({role: oneOf('owner', 'editor', 'viewer'), locked: bool})
  .returns(({role, locked}) => ({allow: role.is('owner').or(role.is('editor').and(locked.not()))}))
const viewers = canEdit.law('a viewer never edits',
  ({role}) => role.is('viewer'), out => out.allow.not())
const lockedDocs = canEdit.law('only the owner edits a locked document',
  ({role, locked}) => [locked, role.is('owner').not()], out => out.allow.not())
expect('permissions', [verdict(proveDecision(viewers)), verdict(proveDecision(lockedDocs))], [{proven: true, checked: true}, {proven: true, checked: true}])
expect('permissions run', canEdit.run({role: 'editor', locked: true}), {allow: false})

// Lists a request carries: an invoice's lines, folded into a total and a taxable part.
const Line = record({amount: nat, taxable: bool})
const invoices = rule('invoices')
  .params({budget: nat})
  .carriesList('Lines', Line, {
    total: {from: 0, step: (acc, l) => acc.plus(l.amount)},
    taxed: {from: 0, step: (acc, l) => acc.plus(when(l.taxable, l.amount, 0))},
  }, {'the taxable part is within the total': ({taxed, total}) => taxed.atMost(total)})
  .state({spent: 0, tax: 0})
  .flags(({Lines, budget, spent}) => ({fits: spent.plus(Lines.fold.total).atMost(budget)}))
  .step(({Lines, spent, tax, fits}) => ({
    spent: when(fits, spent.plus(Lines.fold.total), spent),
    tax: when(fits, tax.plus(Lines.fold.taxed), tax),
  }))
const withinBudget = invoices.law('nothing is spent past the budget',
  ({spent, budget}) => spent.atMost(budget))
const taxWithin = invoices.law('the tax recorded is within what is spent',
  ({tax, spent}) => tax.atMost(spent))
expect('invoices', verdict(proveRule(invoices, [withinBudget, taxWithin])), {proven: true, checked: true})
expect('invoice folds', invoices.foldsOf({Lines: [{amount: 30, taxable: true}, {amount: 50, taxable: false}]}), {Lines: {total: 80, taxed: 30}})

for (const f of failures) console.log(`FAIL ${f}`)
console.log(failures.length ? `${failures.length} of the guide's claims fail` : 'every claim in the guide holds')
if (failures.length) process.exit(1)
