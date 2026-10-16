// Finance: accounts, cards, withdrawals, refunds, escrow, vesting, credit decisions, amortization.
import {type Maybe, type Term, all, bool, forall, loop, maybe, min, nat, no, oneOf, relation, rule, upTo, when} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// An account with an overdraft limit: a withdrawal goes through only if total withdrawals stay within deposits plus the
// limit. Totals rather than a signed balance, since everything is a natural.
const account = rule('account with overdraft')
  .params({limit: nat})
  .inputs({kind: oneOf('deposit', 'withdraw'), amount: nat})
  .state({deposits: 0, withdrawals: 0})
  .flags(({kind, amount, deposits, withdrawals, limit}) => ({paid: kind.is('withdraw').and(withdrawals.plus(amount).atMost(deposits.plus(limit)))}))
  .step(({kind, amount, deposits, withdrawals, paid}) => ({
    deposits: when(kind.is('deposit'), deposits.plus(amount), deposits),
    withdrawals: when(paid, withdrawals.plus(amount), withdrawals),
  }))
const overdraft = account.law('withdrawals stay within deposits + limit', ({withdrawals, deposits, limit}) => withdrawals.atMost(deposits.plus(limit)))
const overdraftChecksOldTotal = account.flags(({kind, deposits, withdrawals, limit}) => ({paid2: kind.is('withdraw').and(withdrawals.atMost(deposits.plus(limit)))}))
  .step(({kind, amount, deposits, withdrawals, paid2}) => ({deposits: when(kind.is('deposit'), deposits.plus(amount), deposits), withdrawals: when(paid2, withdrawals.plus(amount), withdrawals)}))

// A card with holds: an authorization places a hold if posted + held + amount stays within the limit; a capture moves at
// most the held amount to posted; a release drops part of a hold.
const card = rule('card authorizations and captures')
  .params({limit: nat})
  .inputs({op: oneOf('authorize', 'capture', 'release'), amount: nat})
  .state({posted: 0, held: 0})
  .flags(({op, amount, posted, held, limit}) => ({
    authorized: op.is('authorize').and(posted.plus(held).plus(amount).atMost(limit)),
    captured: op.is('capture').and(amount.atMost(held)),
  }))
  .step(({op, amount, posted, held, authorized, captured}) => ({
    held: when(authorized, held.plus(amount), when(captured.or(op.is('release')), held.minus(amount), held)),
    posted: when(captured, posted.plus(amount), posted),
  }))
const withinLimit = card.law('posted + held stay within the limit', ({posted, held, limit}) => posted.plus(held).atMost(limit))
const captureUnchecked = card.flags(({op}) => ({captured2: op.is('capture')}))
  .step(({op, amount, posted, held, authorized, captured2}) => ({
    held: when(authorized, held.plus(amount), when(captured2.or(op.is('release')), held.minus(amount), held)),
    posted: when(captured2, posted.plus(amount), posted),
  }))

// A rolling daily withdrawal cap: the withdrawals logged within a day before a request (`spent`, read from the log at
// the request's time) plus the request must stay within the cap. `today` sums the withdrawals in the day ending at now.
const daily = (ordered: boolean) => {
  const base = rule('daily withdrawal cap')
    .params({day: nat, cap: nat, now: nat})
    .inputs({amount: nat, t: nat})
    .log('amount', 't')
    .sums({today: (r, {now, day}) => when(r.t.atMost(now).and(now.lt(r.t.plus(day))), r.amount, 0)})
    .queries({spent: (r, {t, day}) => when(t.lt(r.t.plus(day)), r.amount, 0)})
    .flags(({spent, amount, cap}) => ({ok: spent.plus(amount).atMost(cap)}))
    .keep(({ok}) => ok)
    .relations(({t, now, today, spent}) => [relation(today.atMost(spent), t.atMost(now))])
  return ordered ? base.prune('t', ({day}) => day) : base
}
const dailyCap = daily(false).law('withdrawn in the day ending at now <= cap', ({today, cap}) => today.atMost(cap))
const dailyForgetsAmount = daily(false).flags(({spent, cap}) => ({ok2: spent.atMost(cap)})).keep(({ok2}) => ok2)

// Refunds per order: a refund goes through only if the order's refunds stay within its charges.
const refunds = rule('refunds per order')
  .inputs({op: oneOf('charge', 'refund'), order: nat, amount: nat})
  .maps({Charged: 0, Refunded: 0})
  .flags(({op, order, amount, Charged, Refunded}) => ({refunded: op.is('refund').and(Refunded.at(order).plus(amount).atMost(Charged.at(order)))}))
  .step(({op, order, amount, refunded, Charged, Refunded}) => ({
    Charged: Charged.bump(order, op.is('charge'), amount),
    Refunded: Refunded.bump(order, refunded, amount),
  }))
const refundBound = refunds.law('every order: refunded <= charged', ({Refunded, Charged}) => forall(o => Refunded.at(o).atMost(Charged.at(o))))
const refundAgainstLast = refunds.flags(({op, order, amount, Charged}) => ({refunded2: op.is('refund').and(amount.atMost(Charged.at(order)))}))
  .step(({op, order, amount, refunded2, Charged, Refunded}) => ({Charged: Charged.bump(order, op.is('charge'), amount), Refunded: Refunded.bump(order, refunded2, amount)}))

// Escrow: funded once, then released to the seller or refunded to the buyer, never both, and never more than funded.
const escrow = rule('escrow')
  .inputs({op: oneOf('fund', 'release', 'refund'), amount: nat})
  .state({funded: 0, released: 0, refunded: 0})
  .flags(({funded, released, refunded}) => ({open: funded.gt(0).and(released.eq(0), refunded.eq(0))}))
  .step(({op, amount, funded, released, refunded, open}) => ({
    funded: when(op.is('fund').and(funded.eq(0)), amount, funded),
    released: when(op.is('release').and(open), funded, released),
    refunded: when(op.is('refund').and(open), funded, refunded),
  }))
const escrowLaws = [
  escrow.law('never both released and refunded', ({released, refunded}) => released.eq(0).or(refunded.eq(0))),
  escrow.law('paid out <= funded', ({released, refunded, funded}) => released.plus(refunded).atMost(funded)),
]
const escrowRefundAfterRelease = escrow.step(({op, amount, funded, released, refunded, open}) => ({
  funded: when(op.is('fund').and(funded.eq(0)), amount, funded),
  released: when(op.is('release').and(open), funded, released),
  refunded: when(op.is('refund').and(funded.gt(0), refunded.eq(0)), funded, refunded),
}))

// Vesting: after the cliff, each tick vests up to `rate` more, never past the grant; a claim takes at most what's vested
// and not yet claimed.
const vesting = rule('vesting with a cliff')
  .params({grant: nat, rate: nat, cliff: nat})
  .inputs({op: oneOf('tick', 'claim'), amount: nat})
  .state({ticks: 0, vested: 0, claimed: 0})
  .step(({op, amount, grant, rate, cliff, ticks, vested, claimed}) => ({
    ticks: when(op.is('tick'), ticks.plus(1), ticks),
    vested: when(op.is('tick').and(ticks.atLeast(cliff)), min(grant, vested.plus(rate)), vested),
    claimed: when(op.is('claim').and(claimed.plus(amount).atMost(vested)), claimed.plus(amount), claimed),
  }))
const vestingLaws = [
  vesting.law('claimed <= vested', ({claimed, vested}) => claimed.atMost(vested)),
  vesting.law('vested <= grant', ({vested, grant}) => vested.atMost(grant)),
]
const vestingClaimsGrant = vesting.step(({op, amount, grant, rate, cliff, ticks, vested, claimed}) => ({
  ticks: when(op.is('tick'), ticks.plus(1), ticks),
  vested: when(op.is('tick').and(ticks.atLeast(cliff)), min(grant, vested.plus(rate)), vested),
  claimed: when(op.is('claim').and(claimed.plus(amount).atMost(grant)), claimed.plus(amount), claimed),
}))

// A credit decision: approve only with a known income, debt-to-income at most 40%, and a known score of at least 600 (a
// score is 300..850, here 0..550 above 300).
const credit = rule('loan approval').inputs({income: maybe(nat), debt: nat, score: maybe(upTo(550)), cosigned: bool})
const approve = ({income, debt, score}: {income: Maybe<Term>, debt: Term, score: Maybe<Term>}) =>
  all(income.match({none: () => no, some: i => debt.times(100).atMost(i.times(40))}), score.match({none: () => no, some: s => s.atLeast(300)}))
const creditDecisions = [
  credit.decide('no income on file, no approval', ({income}) => income.isNone, env => approve(env).not()),
  credit.decide('an approval keeps debt within 40% of income', env => approve(env), ({income, debt}) => income.match({none: () => no, some: i => debt.times(5).atMost(i.times(2))})),
]
const creditWrong = credit.decide('a cosigner is always enough', ({cosigned}) => cosigned, env => approve(env))

// Amortization: each payment lowers the balance by at most the balance; with a positive payment the loan is paid off.
const amortize = loop('amortization')
  .params({principal: nat, payment: nat})
  .inputs({extra: nat})
  .state({balance: ({principal}) => principal})
  .pre(({payment}) => payment.atLeast(1))
  .while(({balance}) => balance.gt(0))
  .body(({balance, payment, extra}) => ({balance: balance.minus(min(balance, payment.plus(extra)))}))
  .rank(({balance}) => balance)
const amortizeLaws = [amortize.law('balance <= principal', ({balance, principal}) => balance.atMost(principal))]
const amortizeNoMinimum = loop('amortization, no minimum payment')
  .params({principal: nat, payment: nat})
  .inputs({extra: nat})
  .state({balance: ({principal}) => principal})
  .while(({balance}) => balance.gt(0))
  .body(({balance, payment, extra}) => ({balance: balance.minus(min(balance, payment.plus(extra)))}))
  .rank(({balance}) => balance)

export const domain: Domain = {
  domain: 'finance',
  about: 'accounts, cards, withdrawal windows, refunds, escrow, vesting, credit decisions, amortization',
  cases: [
    machineCase('account with overdraft', 'withdrawals never exceed deposits plus the overdraft limit', account, [overdraft], [
      {name: 'checks the old total', why: 'the check forgets the withdrawal itself', rule: overdraftChecksOldTotal, laws: [overdraftChecksOldTotal.law('within limit', ({withdrawals, deposits, limit}) => withdrawals.atMost(deposits.plus(limit)))]},
    ]),
    machineCase('card authorizations and captures', 'posted plus held amounts never exceed the credit limit', card, [withinLimit], [
      {name: 'captures more than held', why: 'a capture moves the full amount even past the hold', rule: captureUnchecked, laws: [captureUnchecked.law('within limit', ({posted, held, limit}) => posted.plus(held).atMost(limit))]},
    ]),
    machineCase('daily withdrawal cap', 'the withdrawals in any day ending at now stay within the cap, read from the log', daily(false), [dailyCap], [
      {name: 'forgets the request', why: 'the check reads the day so far without the withdrawal itself', rule: dailyForgetsAmount, laws: [dailyForgetsAmount.law('cap', ({today, cap}) => today.atMost(cap))]},
    ]),
    machineCase('daily withdrawal cap, pruned', 'the same, the log dropping withdrawals older than a day', daily(true), [daily(true).law('withdrawn in the day ending at now <= cap', ({today, cap}) => today.atMost(cap))]),
    machineCase('refunds per order', 'every order is refunded at most what it was charged', refunds, [refundBound], [
      {name: 'checks the amount alone', why: 'the check compares one refund with the charges, forgetting earlier refunds', rule: refundAgainstLast, laws: [refundAgainstLast.law('refunded <= charged', ({Refunded, Charged}) => forall(o => Refunded.at(o).atMost(Charged.at(o))))]},
    ]),
    machineCase('escrow', 'released or refunded, never both, never more than funded', escrow, escrowLaws, [
      {name: 'refunds after release', why: 'the refund forgets to check the release', rule: escrowRefundAfterRelease, laws: [escrowRefundAfterRelease.law('never both', ({released, refunded}) => released.eq(0).or(refunded.eq(0)))]},
    ]),
    machineCase('vesting with a cliff', 'claims never pass what has vested, and vesting never passes the grant', vesting, vestingLaws, [
      {name: 'claims against the grant', why: 'a claim is checked against the whole grant, not what has vested', rule: vestingClaimsGrant, laws: [vestingClaimsGrant.law('claimed <= vested', ({claimed, vested}) => claimed.atMost(vested))]},
    ]),
    decisionCase('loan approval', 'missing facts fail closed and approvals respect debt-to-income', creditDecisions, [
      {name: 'a cosigner is always enough', why: 'a cosigner does not supply the missing income or score', decision: creditWrong},
    ]),
    loopCase('amortization', 'a positive payment pays the loan off, and the balance never grows', amortize, amortizeLaws, [
      {name: 'no minimum payment', why: 'with payment 0 and no extra, the balance never moves', loop: amortizeNoMinimum, laws: [amortizeNoMinimum.law('balance <= principal', ({balance, principal}) => balance.atMost(principal))]},
    ]),
  ],
}
