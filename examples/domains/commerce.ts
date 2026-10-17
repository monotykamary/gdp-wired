// Commerce: inventory reservations, flash-sale limits, coupons, airline overbooking, hotel room-nights, auctions,
// subscription seats, gift cards, a returns window, price adjustments, cart totals.
import {type Bool, type Choice, type Cond, type MapRef, type Maybe, type Term, all, bool, forall, loop, maybe, min, nat, no, oneOf, relation, rule, when} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// Inventory: stock is received, reserved by open orders, released when an order is abandoned, and shipped out of a
// reservation. A reservation goes through only if what's reserved and sold, plus the request, stays within what was
// received, so stock on hand (received ∸ sold) always covers the open reservations.
type InventoryEnv = {qty: Term, received: Term, reserved: Term, sold: Term}
const inventory = (canReserve: (e: InventoryEnv) => Cond) => rule('inventory reservations')
  .inputs({op: oneOf('receive', 'reserve', 'release', 'ship'), qty: nat})
  .state({received: 0, reserved: 0, sold: 0})
  .flags(e => ({reserving: e.op.is('reserve').and(canReserve(e)), shipping: e.op.is('ship').and(e.qty.atMost(e.reserved))}))
  .step(({op, qty, received, reserved, sold, reserving, shipping}) => ({
    received: when(op.is('receive'), received.plus(qty), received),
    reserved: when(reserving, reserved.plus(qty), when(shipping.or(op.is('release')), reserved.minus(qty), reserved)),
    sold: when(shipping, sold.plus(qty), sold),
  }))
const stock = inventory(({qty, received, reserved, sold}) => reserved.plus(sold).plus(qty).atMost(received))
const stockLaws = [
  stock.law('reserved + sold <= received (stock on hand covers every reservation)', ({reserved, sold, received}) => reserved.plus(sold).atMost(received)),
  stock.law('sold <= received', ({sold, received}) => sold.atMost(received)),
]
const stockOversells = inventory(({qty, received, sold}) => qty.atMost(received.minus(sold)))

// A flash sale: at most `limit` units per customer and `stock` units in all. Per customer, so a map.
type SaleEnv = {customer: Term, qty: Term, limit: Term, stock: Term, sold: Term, Bought: MapRef}
const flashSale = (canBuy: (e: SaleEnv) => Cond) => rule('flash sale')
  .params({limit: nat, stock: nat})
  .inputs({customer: nat, qty: nat})
  .state({sold: 0})
  .maps({Bought: 0})
  .flags(e => ({bought: all(canBuy(e), e.sold.plus(e.qty).atMost(e.stock))}))
  .step(({customer, qty, sold, bought, Bought}) => ({Bought: Bought.bump(customer, bought, qty), sold: when(bought, sold.plus(qty), sold)}))
const sale = flashSale(({customer, qty, limit, Bought}) => Bought.at(customer).plus(qty).atMost(limit))
const saleLaws = [
  sale.law('every customer: bought <= limit', ({Bought, limit}) => forall(c => Bought.at(c).atMost(limit))),
  sale.law('sold <= stock', ({sold, stock}) => sold.atMost(stock)),
]
const salePerOrder = flashSale(({qty, limit}) => qty.atMost(limit))

// Coupons: one redemption per customer, and at most `budget` redemptions in all.
type CouponEnv = {customer: Term, budget: Term, redemptions: Term, Used: MapRef}
const coupons = (canRedeem: (e: CouponEnv) => Cond) => rule('coupons, one per customer')
  .params({budget: nat})
  .inputs({customer: nat})
  .state({redemptions: 0})
  .maps({Used: 0})
  .flags(e => ({redeemed: canRedeem(e)}))
  .step(({customer, redemptions, redeemed, Used}) => ({Used: Used.bump(customer, redeemed), redemptions: when(redeemed, redemptions.plus(1), redemptions)}))
const coupon = coupons(({customer, budget, redemptions, Used}) => all(Used.at(customer).eq(0), redemptions.lt(budget)))
const couponLaws = [
  coupon.law('every customer redeems at most once', ({Used}) => forall(c => Used.at(c).atMost(1))),
  coupon.law('redemptions <= budget', ({redemptions, budget}) => redemptions.atMost(budget)),
]
const couponBudgetOnly = coupons(({budget, redemptions}) => redemptions.lt(budget))

// Airline overbooking: tickets may be sold up to `allowance` past the seats, but only `capacity` passengers board; a
// boarded passenger's ticket can't be cancelled.
type FlightEnv = {sold: Term, boarded: Term, capacity: Term, allowance: Term}
const flight = (canBoard: (e: FlightEnv) => Cond, canCancel: (e: FlightEnv) => Cond) => rule('airline overbooking')
  .params({capacity: nat, allowance: nat})
  .inputs({op: oneOf('sell', 'cancel', 'board')})
  .state({sold: 0, boarded: 0})
  .flags(e => ({
    selling: e.op.is('sell').and(e.sold.lt(e.capacity.plus(e.allowance))),
    cancelling: e.op.is('cancel').and(canCancel(e)),
    boarding: e.op.is('board').and(canBoard(e)),
  }))
  .step(({sold, boarded, selling, cancelling, boarding}) => ({
    sold: when(selling, sold.plus(1), when(cancelling, sold.minus(1), sold)),
    boarded: when(boarding, boarded.plus(1), boarded),
  }))
const boardsWithinCapacity = ({sold, boarded, capacity}: FlightEnv) => all(boarded.lt(capacity), boarded.lt(sold))
const cancelsUnboarded = ({sold, boarded}: FlightEnv) => boarded.lt(sold)
const airline = flight(boardsWithinCapacity, cancelsUnboarded)
const airlineLaws = [
  airline.law('sold <= capacity + allowance', ({sold, capacity, allowance}) => sold.atMost(capacity.plus(allowance))),
  airline.law('boarded <= capacity', ({boarded, capacity}) => boarded.atMost(capacity)),
  airline.law('boarded <= sold', ({boarded, sold}) => boarded.atMost(sold)),
]
const airlineBoardsOverbooked = flight(({sold, boarded}) => boarded.lt(sold), cancelsUnboarded)
const airlineCancelsBoarded = flight(boardsWithinCapacity, ({sold}) => sold.gt(0))

// Hotel room-nights: a room-night (a key: room and night) is booked only while free, and cancelled only by its holder.
// Nights counts the bookings of each room-night; Holder names the guest (guests are numbered from 1, 0 is free).
type HotelEnv = {slot: Term, guest: Term, Nights: MapRef, Holder: MapRef}
const hotel = (canBook: (e: HotelEnv) => Cond, clearsHolder: boolean) => rule('hotel room-nights')
  .inputs({op: oneOf('book', 'cancel'), slot: nat, guest: nat})
  .assume(({guest}) => guest.atLeast(1))
  .maps({Nights: 0, Holder: 0})
  .flags(e => ({booking: e.op.is('book').and(canBook(e)), cancelling: e.op.is('cancel').and(e.Holder.at(e.slot).eq(e.guest))}))
  .step(({slot, guest, booking, cancelling, Nights, Holder}) => ({
    Nights: Nights.set(slot, when(booking, Nights.at(slot).plus(1), when(cancelling, Nights.at(slot).minus(1), Nights.at(slot)))),
    Holder: Holder.set(slot, when(booking, guest, when(cancelling, clearsHolder ? 0 : Holder.at(slot), Holder.at(slot)))),
  }))
const rooms = hotel(({slot, Nights}) => Nights.at(slot).eq(0), true)
const roomLaws = [
  rooms.law('every room-night is booked at most once', ({Nights}) => forall(k => Nights.at(k).atMost(1))),
  rooms.law('a room-night has a holder exactly when it is booked', ({Nights, Holder}) => forall(k => Nights.at(k).eq(0).iff(Holder.at(k).eq(0)))),
]
const roomsNoVacancyCheck = hotel(() => all(), true)
const roomsKeepHolder = hotel(({slot, Nights}) => Nights.at(slot).eq(0), false)

// An auction: a bid is taken only if it meets the reserve and beats the high bid by the increment, and the leader can't
// bid against themselves. "The high bid only rises, by at least the increment" is a law about a step.
type AuctionEnv = {amount: Term, bidder: Term, high: Term, leader: Term, bids: Term, reserve: Term, increment: Term}
const auction = (beats: (e: AuctionEnv) => Cond) => rule('auction')
  .params({reserve: nat, increment: nat})
  .inputs({bidder: nat, amount: nat})
  .state({high: 0, leader: 0, bids: 0})
  .flags(e => ({taken: all(beats(e), e.bids.eq(0).or(e.bidder.ne(e.leader)))}))
  .step(({bidder, amount, high, leader, bids, taken}) => ({
    high: when(taken, amount, high),
    leader: when(taken, bidder, leader),
    bids: when(taken, bids.plus(1), bids),
  }))
const bidding = auction(({amount, high, reserve, increment}) => all(amount.atLeast(reserve), amount.atLeast(high.plus(increment))))
const auctionLaws = [bidding.law('a taken bid meets the reserve', ({bids, high, reserve}) => bids.eq(0).or(high.atLeast(reserve)))]
const auctionSteps = (a: typeof bidding) => [
  a.stepLaw('the high bid never falls', ({high}, after) => high.atMost(after.high)),
  a.stepLaw('a taken bid beats the high bid by the increment', ({high, increment}, after) => high.plus(increment).atMost(after.high), ({taken}) => taken),
  a.stepLaw('a refused bid changes nothing', ({high, leader, bids}, after) => after.high.eq(high).and(after.leader.eq(leader)).and(after.bids.eq(bids)), ({taken}) => taken.not()),
  // About two bids in a row.
  a.stepsLaw('two taken bids raise the high bid by two increments', 2, ({high, increment}, after) => high.plus(increment).plus(increment).atMost(after.high), ({taken}) => taken),
  a.stepsLaw('two refused bids change nothing', 2, ({high, leader, bids}, after) => after.high.eq(high).and(after.leader.eq(leader)).and(after.bids.eq(bids)), ({taken}) => taken.not()),
]
const auctionBeatsByOne = auction(({amount, high, reserve}) => all(amount.atLeast(reserve), amount.gt(high)))
const auctionReserveOnly = auction(({amount, reserve, increment}) => amount.atLeast(reserve.plus(increment)))

// Subscription seats: seats are bought, assigned and unassigned one at a time; a downgrade drops seats only if the
// assigned ones still fit.
type SeatEnv = {n: Term, purchased: Term, assigned: Term}
const seats = (canDowngrade: (e: SeatEnv) => Cond) => rule('subscription seats')
  .inputs({op: oneOf('buy', 'assign', 'unassign', 'downgrade'), n: nat})
  .state({purchased: 0, assigned: 0})
  .flags(e => ({assigning: e.op.is('assign').and(e.assigned.lt(e.purchased)), downgrading: e.op.is('downgrade').and(canDowngrade(e))}))
  .step(({op, n, purchased, assigned, assigning, downgrading}) => ({
    purchased: when(op.is('buy'), purchased.plus(n), when(downgrading, purchased.minus(n), purchased)),
    assigned: when(assigning, assigned.plus(1), when(op.is('unassign'), assigned.minus(1), assigned)),
  }))
const seating = seats(({n, purchased, assigned}) => assigned.plus(n).atMost(purchased))
const seatLaws = [seating.law('assigned <= purchased', ({assigned, purchased}) => assigned.atMost(purchased))]
const seatsDowngradeBelowAssigned = seats(({n, purchased}) => n.atMost(purchased))

// A gift card: redemptions never pass what was loaded, and the balance (loaded ∸ redeemed) never passes the card's cap.
type CardEnv = {amount: Term, loaded: Term, redeemed: Term, cap: Term}
const giftCard = (canLoad: (e: CardEnv) => Cond, canRedeem: (e: CardEnv) => Cond) => rule('gift card')
  .params({cap: nat})
  .inputs({op: oneOf('load', 'redeem'), amount: nat})
  .state({loaded: 0, redeemed: 0})
  .flags(e => ({loading: e.op.is('load').and(canLoad(e)), redeeming: e.op.is('redeem').and(canRedeem(e))}))
  .step(({amount, loaded, redeemed, loading, redeeming}) => ({
    loaded: when(loading, loaded.plus(amount), loaded),
    redeemed: when(redeeming, redeemed.plus(amount), redeemed),
  }))
const loadsWithinCap = ({amount, loaded, redeemed, cap}: CardEnv) => loaded.plus(amount).atMost(redeemed.plus(cap))
const redeemsWithinBalance = ({amount, loaded, redeemed}: CardEnv) => redeemed.plus(amount).atMost(loaded)
const card = giftCard(loadsWithinCap, redeemsWithinBalance)
const cardLaws = [
  card.law('redeemed <= loaded', ({redeemed, loaded}) => redeemed.atMost(loaded)),
  card.law('balance <= cap', ({loaded, redeemed, cap}) => loaded.atMost(redeemed.plus(cap))),
]
const cardRedeemsAgainstLoaded = giftCard(loadsWithinCap, ({amount, loaded}) => amount.atMost(loaded))
const cardCapsEachLoad = giftCard(({amount, cap}) => amount.atMost(cap), redeemsWithinBalance)

// A returns window: purchases and returns are logged; a return is accepted only if the returns so far plus this one
// stay within the purchases made within `window` before it. Read from the log: `recentBought` sums the purchases in the
// window before the request and `returnedSoFar` every return, and the relations tie them to the totals record by
// record, so returns never pass purchases.
type ReturnsEnv = {op: Choice<'buy' | 'return'>, qty: Term, recentBought: Term, returnedSoFar: Term}
const returnsWindow = (canReturn: (e: ReturnsEnv) => Cond) => rule('returns window')
  .params({window: nat})
  .inputs({op: oneOf('buy', 'return'), qty: nat, t: nat})
  .log('op', 'qty', 't')
  .sums({
    bought: r => when(r.op.is('buy'), r.qty, 0),
    returned: r => when(r.op.is('return'), r.qty, 0),
  })
  .queries({
    recentBought: (r, {t, window}) => when(r.op.is('buy').and(t.lt(r.t.plus(window))), r.qty, 0),
    returnedSoFar: r => when(r.op.is('return'), r.qty, 0),
  })
  .flags(e => ({accepted: e.op.is('buy').or(canReturn(e))}))
  .keep(({accepted}) => accepted)
  .relations(({recentBought, bought, returned, returnedSoFar}) => [relation(recentBought.atMost(bought)), relation(returned.atMost(returnedSoFar))])
const returns = returnsWindow(({qty, recentBought, returnedSoFar}) => returnedSoFar.plus(qty).atMost(recentBought))
const returnsLaws = [returns.law('returned <= bought', ({returned, bought}) => returned.atMost(bought))]
const returnsForgetEarlier = returnsWindow(({qty, recentBought}) => qty.atMost(recentBought))

// Price adjustments: a markdown, and a coupon on top, against a known cost. Regular prices take no coupon and never go
// below cost; members may stack a coupon, still not below cost; clearance needs a manager and may go below cost, but
// never below half of it. A missing cost fails closed.
const pricing = rule('price adjustment').inputs({list: nat, cost: maybe(nat), markdown: nat, coupon: maybe(nat), tier: oneOf('regular', 'member', 'clearance'), manager: bool})
type PriceEnv = {list: Term, cost: Maybe<Term>, markdown: Term, coupon: Maybe<Term>, tier: Choice<'regular' | 'member' | 'clearance'>, manager: Bool}
const off = ({markdown, coupon}: PriceEnv): Term => markdown.plus(coupon.match({none: () => 0, some: c => c}))
const approve = (e: PriceEnv, memberFloor: (p: PriceEnv, cost: Term) => Cond = (p, k) => off(p).plus(k).atMost(p.list)) => e.cost.match({
  none: () => no,
  some: k => e.tier.match({
    regular: () => all(e.coupon.isNone, e.markdown.plus(k).atMost(e.list)),
    member: () => memberFloor(e, k),
    clearance: () => all(e.manager, off(e).atMost(e.list), k.atMost(e.list.minus(off(e)).times(2))),
  }),
})
const atOrAboveCost = (e: PriceEnv) => e.cost.match({none: () => no, some: k => e.list.minus(off(e)).atLeast(k)})
const pricingDecisions = [
  pricing.decide('no cost on file, no adjustment', ({cost}) => cost.isNone, e => approve(e).not()),
  pricing.decide('regular and member prices stay at or above cost', e => [approve(e), e.tier.is('clearance').not()], atOrAboveCost),
  pricing.decide('a clearance price has a manager', e => [approve(e), e.tier.is('clearance')], ({manager}) => manager),
  pricing.decide('no price falls below half the cost', e => approve(e), e => e.cost.match({none: () => no, some: k => k.atMost(e.list.minus(off(e)).times(2))})),
]
const pricingMemberForgetsCoupon = pricing.decide('member prices stay at or above cost (the coupon forgotten)', e => [approve(e, (p, k) => p.markdown.plus(k).atMost(p.list)), e.tier.is('member')], atOrAboveCost)
const pricingManagerEnough = pricing.decide('a manager-approved price is at or above cost', e => [approve(e), e.manager], atOrAboveCost)

// Cart totals: one line per turn, each at least one unit; a line's promotion is capped at its price, so the discount
// never passes the subtotal.
const cart = (minimumUnit: boolean, capsPromo: boolean) => {
  const base = loop('cart totals')
    .params({units: nat})
    .inputs({qty: nat, price: nat, promo: nat})
    .state({left: ({units}) => units, subtotal: 0, discount: 0})
    .while(({left}) => left.gt(0))
    .body(({left, subtotal, discount, qty, price, promo}) => ({
      left: left.minus(qty),
      subtotal: subtotal.plus(price),
      discount: discount.plus(capsPromo ? min(promo, price) : promo),
    }))
    .rank(({left}) => left)
  return minimumUnit ? base.assume(({qty}) => qty.atLeast(1)) : base
}
const cartTotals = cart(true, true)
const cartLaws = [
  cartTotals.law('discount <= subtotal', ({discount, subtotal}) => discount.atMost(subtotal)),
  cartTotals.law('left <= units', ({left, units}) => left.atMost(units)),
]
const cartUncappedPromo = cart(true, false)
const cartEmptyLines = cart(false, true)

export const domain: Domain = {
  domain: 'commerce',
  about: 'inventory, flash sales, coupons, overbooking, room-nights, auctions, seats, gift cards, returns, pricing, carts',
  cases: [
    machineCase('inventory reservations', 'stock on hand always covers the open reservations, and nothing ships that was not received', stock, stockLaws, [
      {name: 'reserves against stock on hand', why: 'the check compares the request with received ∸ sold, forgetting the reservations already held', rule: stockOversells, laws: stockLaws},
    ]),
    machineCase('flash sale', 'no customer buys past the per-customer limit, and the sale never passes its stock', sale, saleLaws, [
      {name: 'limits each order, not each customer', why: 'the limit is checked per order, so a customer splits a purchase into several orders', rule: salePerOrder, laws: saleLaws},
    ]),
    machineCase('coupons, one per customer', 'every customer redeems at most once, within the campaign budget', coupon, couponLaws, [
      {name: 'checks the budget only', why: 'the check forgets whether the customer already redeemed', rule: couponBudgetOnly, laws: couponLaws},
    ]),
    machineCase('airline overbooking', 'tickets stay within capacity plus the allowance, boarding within capacity and the tickets sold', airline, airlineLaws, [
      {name: 'boards every ticket holder', why: 'boarding checks for a ticket but not for a seat, so an overbooked passenger boards', rule: airlineBoardsOverbooked, laws: airlineLaws},
      {name: 'cancels a boarded ticket', why: 'a cancellation forgets the passenger may already be on board', rule: airlineCancelsBoarded, laws: airlineLaws},
    ]),
    machineCase('hotel room-nights', 'no room-night is ever booked twice, and its holder is on record exactly while it is booked', rooms, roomLaws, [
      {name: 'books without a vacancy check', why: 'a second guest books a room-night already taken', rule: roomsNoVacancyCheck, laws: roomLaws},
      {name: 'cancels but keeps the holder', why: 'a cancellation frees the night but leaves the old guest on record', rule: roomsKeepHolder, laws: roomLaws},
    ]),
    machineCase('auction', 'the high bid only rises, each time by at least the increment, and meets the reserve', bidding, auctionLaws, [
      {name: 'beats the high bid by one', why: 'a bid just above the high bid is taken, ignoring an increment above one', rule: auctionBeatsByOne, laws: auctionLaws, steps: auctionSteps(auctionBeatsByOne)},
      {name: 'checks the reserve only', why: 'a bid is compared with the reserve, not the high bid, so the high bid can fall', rule: auctionReserveOnly, laws: auctionLaws, steps: auctionSteps(auctionReserveOnly)},
    ], {steps: auctionSteps(bidding)}),
    machineCase('subscription seats', 'assigned seats never pass the purchased ones, a downgrade refused below the assigned', seating, seatLaws, [
      {name: 'downgrades below the assigned', why: 'a downgrade only checks it leaves a nonnegative seat count', rule: seatsDowngradeBelowAssigned, laws: seatLaws},
    ]),
    machineCase('gift card', 'redemptions never pass what was loaded, and the balance never passes the cap', card, cardLaws, [
      {name: 'redeems against the loaded total', why: 'a redemption is compared with everything loaded, forgetting what was already redeemed', rule: cardRedeemsAgainstLoaded, laws: cardLaws},
      {name: 'caps each load, not the balance', why: 'each load is checked against the cap alone, so loads add up past it', rule: cardCapsEachLoad, laws: cardLaws},
    ]),
    machineCase('returns window', 'returns, accepted against purchases within the window, never pass the purchases, read from the log', returns, returnsLaws, [
      {name: 'forgets earlier returns', why: 'each return is compared with the recent purchases alone, so the same purchase is returned twice', rule: returnsForgetEarlier, laws: returnsLaws},
    ]),
    decisionCase('price adjustment', 'a missing cost fails closed, prices stay above cost unless a manager clears them, never below half of it', pricingDecisions, [
      {name: 'member coupon forgotten', why: 'the member floor checks the markdown against cost but not the coupon stacked on it', decision: pricingMemberForgetsCoupon},
      {name: 'a manager is enough', why: 'a manager approves clearance prices, which may go below cost', decision: pricingManagerEnough},
    ]),
    loopCase('cart totals', 'every line has a unit, so the cart is totalled, and the discount never passes the subtotal', cartTotals, cartLaws, [
      {name: 'uncapped promotion', why: 'a promotion larger than its line is taken whole', loop: cartUncappedPromo, laws: cartLaws},
      {name: 'empty lines', why: 'a line of zero units leaves the count where it was, so the loop need not end', loop: cartEmptyLines, laws: cartLaws},
    ]),
  ],
}
