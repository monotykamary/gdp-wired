// Ad tech and marketing: frequency caps per user read from the log, campaign spend within budget, daily pacing,
// impressions within what was bought, bids between the floor and the max bid, attribution windows, and spending a
// budget down in an auction loop. Each rule takes the bug its broken variant carries.
import {type Choice, type Maybe, type Term, count, forall, loop, max, maybe, min, nat, no, oneOf, relation, rule, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// A frequency cap: an ad is shown to a user while they saw it fewer than `cap` times in the window before. `recent`
// (a sum) counts user `who`'s impressions in the window ending at `now`.
const frequency = (bug?: 'cap off by one') => rule('frequency cap per user')
  .params({window: nat, cap: nat, now: nat, who: nat})
  .inputs({user: nat, t: nat})
  .log('user', 't')
  .sums({recent: (r, {now, window, who}) => count(r.user.eq(who).and(r.t.atMost(now), now.lt(r.t.plus(window))))})
  .queries({seen: (r, {t, window, user}) => when(r.user.eq(user), count(t.lt(r.t.plus(window))), 0)})
  .flags(({seen, cap}) => ({shows: bug ? seen.atMost(cap) : seen.plus(1).atMost(cap)}))
  .keep(({shows}) => shows)
  .relations(({t, now, user, who, recent, seen}) => [relation(recent.atMost(seen), t.atMost(now).and(user.eq(who)))])
const frequencyLaws = (r: ReturnType<typeof frequency>) => [r.law('impressions to who in the window ending at now <= cap', ({recent, cap}) => recent.atMost(cap))]

// Campaign spend: a win is checked against the bid (the most it could cost) and charged the clearing price, never above
// the bid; advertisers top campaigns up.
const spend = (bug?: 'checks the price, charges the bid') => rule('campaign spend within budget')
  .inputs({op: oneOf('fund', 'win'), campaign: nat, bid: nat, price: nat})
  .maps({Budget: 0, Spent: 0})
  .assume(({price, bid}) => price.atMost(bid))
  .flags(({op, campaign, bid, price, Budget, Spent}) => ({
    wins: op.is('win').and(Spent.at(campaign).plus(bug ? price : bid).atMost(Budget.at(campaign))),
  }))
  .step(({op, campaign, bid, price, wins, Budget, Spent}) => ({
    Budget: Budget.bump(campaign, op.is('fund'), bid),
    Spent: Spent.bump(campaign, wins, bug ? bid : price),
  }))
const spendLaws = (r: ReturnType<typeof spend>) => [r.law('every campaign: spent <= budget', ({Spent, Budget}) => forall(c => Spent.at(c).atMost(Budget.at(c))))]

// Daily pacing: a campaign spends at most `dailyCap` on any day and at most `total` overall.
const pacing = (bug?: 'pacing checks before the charge') => rule('daily pacing')
  .params({dailyCap: nat, total: nat})
  .inputs({day: nat, price: nat})
  .state({spent: 0})
  .maps({Day: 0})
  .flags(({day, price, dailyCap, total, spent, Day}) => ({
    serves: (bug ? Day.at(day).atMost(dailyCap) : Day.at(day).plus(price).atMost(dailyCap)).and(spent.plus(price).atMost(total)),
  }))
  .step(({day, price, serves, spent, Day}) => ({spent: when(serves, spent.plus(price), spent), Day: Day.bump(day, serves, price)}))
const pacingLaws = (r: ReturnType<typeof pacing>) => [
  r.law('every day: spend <= dailyCap', ({Day, dailyCap}) => forall(d => Day.at(d).atMost(dailyCap))),
  r.law('spent <= total', ({spent, total}) => spent.atMost(total)),
]
const pacingSteps = (r: ReturnType<typeof pacing>) => [
  r.stepLaw('a served impression charges its day exactly the price', ({day, price, Day}, after) => after.Day.at(day).eq(Day.at(day).plus(price)), ({serves}) => serves),
]

// Impressions within what was bought: orders add impressions, a cancellation removes only what wasn't served yet.
const delivery = (bug?: 'cancels served impressions') => rule('impressions within purchased')
  .inputs({op: oneOf('order', 'serve', 'cancel'), amount: nat})
  .state({purchased: 0, served: 0})
  .flags(({op, amount, purchased, served}) => ({
    serves: op.is('serve').and(served.lt(purchased)),
    cancels: op.is('cancel').and(bug ? amount.atMost(purchased) : served.plus(amount).atMost(purchased)),
  }))
  .step(({op, amount, serves, cancels, purchased, served}) => ({
    purchased: when(op.is('order'), purchased.plus(amount), when(cancels, purchased.minus(amount), purchased)),
    served: when(serves, served.plus(1), served),
  }))
const deliveryLaws = (r: ReturnType<typeof delivery>) => [r.law('served <= purchased', ({served, purchased}) => served.atMost(purchased))]
const deliverySteps = (r: ReturnType<typeof delivery>) => [
  r.stepLaw('a serve shows one impression', ({served}, after) => after.served.eq(served.plus(1)), ({serves}) => serves),
  r.stepsLaw('two serves show two', 2, ({served}, after) => after.served.eq(served.plus(2)), ({serves}) => serves),
]

// Bidding: the bid is the value clamped to [floor, maxBid]; in a second-price auction the winner pays the runner-up,
// never less than the floor and never more than its bid.
const bidding = rule('bid shading').params({floor: nat, maxBid: nat}).inputs({value: nat, second: nat, auction: oneOf('first', 'second')})
type BidEnv = {floor: Term, maxBid: Term, value: Term, second: Term, auction: Choice<'first' | 'second'>}
const bidOf = ({floor, maxBid, value}: BidEnv, bug?: 'boost after the cap') => (bug ? max(floor, min(maxBid, value)).plus(1) : max(floor, min(maxBid, value)))
const payOf = (env: BidEnv) => when(env.auction.is('second'), max(env.floor, min(env.second, bidOf(env))), bidOf(env))
const bidDecisions = [
  bidding.decide('the bid never passes the max bid', ({floor, maxBid}) => floor.atMost(maxBid), env => bidOf(env).atMost(env.maxBid)),
  bidding.decide('the bid is never below the floor', () => yes, env => env.floor.atMost(bidOf(env))),
  bidding.decide('the winner never pays more than it bid', () => yes, env => payOf(env).atMost(bidOf(env))),
]
const bidBroken = [
  {name: 'boost after the cap', why: 'a one-cent boost is added after the max-bid clamp', decision: bidding.decide('the bid never passes the max bid', ({floor, maxBid}) => floor.atMost(maxBid), env => bidOf(env, 'boost after the cap').atMost(env.maxBid))},
]

// Attribution: a conversion is credited to a click only if the click came first, within the window.
const attribution = rule('attribution window').params({window: nat}).inputs({clickAt: maybe(nat), conversionAt: nat})
type AttrEnv = {window: Term, clickAt: Maybe<Term>, conversionAt: Term}
const credited = ({window, clickAt, conversionAt}: AttrEnv, bug?: 'clicks after the conversion count') =>
  clickAt.match({none: () => no, some: c => (bug ? yes : c.atMost(conversionAt)).and(conversionAt.atMost(c.plus(window)))})
const attrDecisions = [
  attribution.decide('no click, no credit', ({clickAt}) => clickAt.isNone, env => credited(env).not()),
  attribution.decide('a credited conversion came after its click', env => credited(env), ({clickAt, conversionAt}) => clickAt.match({none: () => no, some: c => c.atMost(conversionAt)})),
  attribution.decide('a credited conversion is within the window', env => credited(env), ({clickAt, conversionAt, window}) => clickAt.match({none: () => no, some: c => conversionAt.atMost(c.plus(window))})),
]
const attrBroken = [
  {name: 'clicks after the conversion count', why: 'the click is matched within the window on either side of the conversion', decision: attribution.decide('a credited conversion came after its click', env => credited(env, 'clicks after the conversion count'), ({clickAt, conversionAt}) => clickAt.match({none: () => no, some: c => c.atMost(conversionAt)}))},
]

// Spending a budget down in auctions: each win costs at least one, so the remaining budget drops every turn.
const burn = (bug?: 'free wins') => loop('spending a budget down')
  .params({budget: nat})
  .inputs({price: nat})
  .state({remaining: ({budget}) => budget, spent: 0})
  .while(({remaining}) => remaining.gt(0))
  .body(({remaining, spent, price}) => {
    const cost = min(remaining, bug ? price : max(price, 1))
    return {remaining: remaining.minus(cost), spent: spent.plus(cost)}
  })
  .rank(({remaining}) => remaining)
const burnLaws = (l: ReturnType<typeof burn>) => [l.law('remaining + spent = budget', ({remaining, spent, budget}) => remaining.plus(spent).eq(budget))]

const frequencyOff = frequency('cap off by one')
const spendBid = spend('checks the price, charges the bid')
const pacingBefore = pacing('pacing checks before the charge')
const deliveryCancel = delivery('cancels served impressions')
const burnFree = burn('free wins')

export const domain: Domain = {
  domain: 'ad tech',
  about: 'frequency caps, campaign budgets, daily pacing, impressions bought, bid floors and caps, attribution windows, budget burn',
  cases: [
    machineCase('frequency cap per user', 'no user sees an ad more than cap times in any window ending at now, read from the log', frequency(), frequencyLaws(frequency()), [
      {name: 'cap off by one', why: 'the check shows the ad when the user already saw it cap times', rule: frequencyOff, laws: frequencyLaws(frequencyOff)},
    ]),
    machineCase('campaign spend within budget', 'no campaign spends more than its budget; a win is checked at the bid and charged the price', spend(), spendLaws(spend()), [
      {name: 'checks the price, charges the bid', why: 'the budget check uses the clearing price but the charge is the bid', rule: spendBid, laws: spendLaws(spendBid)},
    ]),
    machineCase('daily pacing', 'a campaign spends at most dailyCap on any day and total overall', pacing(), pacingLaws(pacing()), [
      {name: 'pacing checks before the charge', why: 'the daily check reads the day\'s spend before the price is added', rule: pacingBefore, laws: pacingLaws(pacingBefore), steps: pacingSteps(pacingBefore)},
    ], {steps: pacingSteps(pacing())}),
    machineCase('impressions within purchased', 'never more impressions served than bought, cancellations included', delivery(), deliveryLaws(delivery()), [
      {name: 'cancels served impressions', why: 'a cancellation removes impressions that were already served', rule: deliveryCancel, laws: deliveryLaws(deliveryCancel), steps: deliverySteps(deliveryCancel)},
    ], {steps: deliverySteps(delivery())}),
    decisionCase('bid shading', 'bids stay within [floor, maxBid], and a winner never pays more than it bid', bidDecisions, bidBroken),
    decisionCase('attribution window', 'a conversion is credited only to a click before it, within the window', attrDecisions, attrBroken),
    loopCase('spending a budget down', 'auctions spend a budget down and stop, every cent accounted for', burn(), burnLaws(burn()), [
      {name: 'free wins', why: 'a win at price 0 leaves the budget where it was, so the loop can run forever', loop: burnFree, laws: burnLaws(burnFree)},
    ]),
  ],
}
