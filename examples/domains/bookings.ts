// Bookings and hospitality: no room double-booked on a night, overbooking within a margin, refunds within what was
// paid, holds that expire, quotes for members and guests, a waitlist that drains, and a table's covers per seating.
import {type Term, bool, forall, loop, nat, oneOf, rule, upTo, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// Rooms 0..3 over nights 0..6: a booking is kept at key 7 room + night, taken only if that room-night is free.
const night = (room: Term, n: Term) => room.times(7).plus(n)
const rooms = (bug?: 'checks the wrong night') => rule('no double-booked room')
  .inputs({op: oneOf('book', 'cancel'), room: upTo(3), n: upTo(6)})
  .state({booked: 0})
  .maps({Booked: 0})
  .flags(({op, room, n, Booked}) => ({
    books: op.is('book').and(Booked.at(bug === 'checks the wrong night' ? room.plus(n) : night(room, n)).eq(0)),
    cancels: op.is('cancel').and(Booked.at(night(room, n)).eq(1)),
  }))
  .step(({room, n, books, cancels, booked, Booked}) => ({
    Booked: Booked.set(night(room, n), when(books, Booked.at(night(room, n)).plus(1), when(cancels, 0, Booked.at(night(room, n))))),
    booked: when(books, booked.plus(1), when(cancels, booked.minus(1), booked)),
  }))
const roomLaws = (r: ReturnType<typeof rooms>) => [
  r.law('every room-night is booked at most once', ({Booked}) => forall(k => Booked.at(k).atMost(1))),
]

// Overbooking: a flight or hotel sells up to capacity plus a margin for expected no-shows; refunds release seats.
const overbooking = (bug?: 'margin checked before the sale') => rule('overbooking within a margin')
  .params({capacity: nat, margin: nat})
  .inputs({op: oneOf('sell', 'refund'), seats: upTo(6)})
  .state({sold: 0})
  .flags(({op, seats, sold, capacity, margin}) => ({
    sells: op.is('sell').and(bug === 'margin checked before the sale' ? sold.atMost(capacity.plus(margin)) : sold.plus(seats).atMost(capacity.plus(margin))),
    refunds: op.is('refund').and(seats.atMost(sold)),
  }))
  .step(({seats, sold, sells, refunds}) => ({sold: when(sells, sold.plus(seats), when(refunds, sold.minus(seats), sold))}))
const overbookingLaws = (r: ReturnType<typeof overbooking>) => [
  r.law('sold <= capacity + margin', ({sold, capacity, margin}) => sold.atMost(capacity.plus(margin))),
]

// Refunds: each booking's refunds never pass what was paid for it.
const refunds = (bug?: 'checks the payment, not what is left') => rule('refunds within payments')
  .inputs({op: oneOf('pay', 'refund'), booking: nat, amount: nat})
  .maps({Paid: 0, Refunded: 0})
  .flags(({op, booking, amount, Paid, Refunded}) => ({
    refunds: op.is('refund').and(bug === 'checks the payment, not what is left' ? amount.atMost(Paid.at(booking)) : Refunded.at(booking).plus(amount).atMost(Paid.at(booking))),
  }))
  .step(({op, booking, amount, refunds, Paid, Refunded}) => ({
    Paid: Paid.bump(booking, op.is('pay'), amount),
    Refunded: Refunded.bump(booking, refunds, amount),
  }))
const refundLaws = (r: ReturnType<typeof refunds>) => [
  r.law('every booking: refunded <= paid', ({Refunded, Paid}) => forall(b => Refunded.at(b).atMost(Paid.at(b)))),
]

// A seat hold: a hold lasts `ttl` ticks; it can be confirmed only within them, and an expired hold is released.
const hold = (bug?: 'confirms an expired hold' | 'holds a confirmed seat') => rule('seat holds that expire')
  .params({ttl: nat})
  .inputs({op: oneOf('hold', 'tick', 'expire', 'confirm')})
  .state({now: 0, heldAt: 0, held: 0, confirmed: 0})
  .flags(({op, now, heldAt, held, confirmed, ttl}) => ({
    holds: op.is('hold').and(held.eq(0), bug === 'holds a confirmed seat' ? yes : confirmed.eq(0)),
    expires: op.is('expire').and(held.eq(1), now.gt(heldAt.plus(ttl))),
    confirms: op.is('confirm').and(held.eq(1), bug === 'confirms an expired hold' ? yes : now.atMost(heldAt.plus(ttl))),
  }))
  .step(({op, now, heldAt, held, confirmed, holds, expires, confirms}) => ({
    now: when(op.is('tick'), now.plus(1), now),
    heldAt: when(holds, now, heldAt),
    held: when(holds, 1, when(expires.or(confirms), 0, held)),
    confirmed: when(confirms, 1, confirmed),
  }))
const holdLaws = (r: ReturnType<typeof hold>) => [
  r.law('a seat is held or confirmed, not both', ({held, confirmed}) => held.plus(confirmed).atMost(1)),
  r.law('a hold starts in the past', ({heldAt, now}) => heldAt.atMost(now)),
]
const holdSteps = (r: ReturnType<typeof hold>) => [
  r.stepLaw('a seat is confirmed only within its hold', ({confirmed, now, heldAt, ttl}, after) => confirmed.eq(0).and(after.confirmed.eq(1)).implies(now.atMost(heldAt.plus(ttl)))),
  r.stepLaw('a confirmed seat stays confirmed', ({confirmed}, after) => confirmed.eq(1).implies(after.confirmed.eq(1))),
]

// Quotes: the subtotal less a promo and a member discount of 2; a member never pays more than a guest for the same
// stay and promo.
const quote = rule('member and guest quotes').inputs({subtotal: nat, member: bool, promo: nat})
const price = ({subtotal, member, promo}: {subtotal: Term, member: {n: Term}, promo: Term}, memberFee = false) => {
  const afterPromo = subtotal.minus(promo)
  return memberFee ? afterPromo.minus(member.n.times(2)).plus(member.n.times(3)) : afterPromo.minus(member.n.times(2))
}
const quoteDecisions = [
  quote.relate('a member never pays more than a guest for the same stay', (a, b) => [a.subtotal.eq(b.subtotal), a.promo.eq(b.promo), a.member, b.member.not()], (a, b) => price(a).atMost(price(b))),
  quote.decide('a quote never exceeds the subtotal', () => [], env => price(env).atMost(env.subtotal)),
]
const quoteBroken = [
  {name: 'adds a member booking fee', why: 'the member path adds the 3 booking fee the guest path waives',
    decision: quote.relate('a member never pays more than a guest for the same stay', (a, b) => [a.subtotal.eq(b.subtotal), a.promo.eq(b.promo), a.member, b.member.not()], (a, b) => price(a, true).atMost(price(b, true)))},
]

// The waitlist drains: while guests wait and seats are free, each round offers at least one seat (no more than the
// free seats or the waiting guests), so the list ends empty or the room full.
const waitlist = (bug?: 'a round may offer nothing') => {
  const base = loop('draining the waitlist')
    .params({waiting: nat, free: nat})
    .inputs({offered: nat})
    .state({left: ({waiting}) => waiting, seats: ({free}) => free})
    .while(({left, seats}) => left.gt(0).and(seats.gt(0)))
    .body(({left, seats, offered}) => ({left: left.minus(offered), seats: seats.minus(offered)}))
    .rank(({left}) => left)
  const fits = (o: Term, left: Term, seats: Term) => o.atMost(left).and(o.atMost(seats))
  return bug === 'a round may offer nothing' ? base.assume(({offered, left, seats}) => fits(offered, left, seats)) : base.assume(({offered, left, seats}) => offered.atLeast(1).and(fits(offered, left, seats)))
}
const waitlistLaws = (l: ReturnType<typeof waitlist>) => [
  l.law('the free seats never pass what was free', ({seats, free}) => seats.atMost(free)),
  l.law('the waiting guests never pass the list', ({left, waiting}) => left.atMost(waiting)),
  l.law('as many seats taken as guests seated', ({waiting, free, left, seats}) => waiting.minus(left).eq(free.minus(seats))),
]

// A restaurant's covers per seating: tables are seated while the seating's covers stay within the kitchen's limit.
const covers = (bug?: 'counts tables, not guests') => rule('covers per seating')
  .params({limit: nat})
  .inputs({op: oneOf('seat', 'leave'), seating: upTo(3), party: upTo(8)})
  .maps({Covers: 0})
  .flags(({op, seating, party, limit, Covers}) => ({
    seats: op.is('seat').and(bug === 'counts tables, not guests' ? Covers.at(seating).plus(1).atMost(limit) : Covers.at(seating).plus(party).atMost(limit)),
    leaves: op.is('leave').and(party.atMost(Covers.at(seating))),
  }))
  .step(({seating, party, seats, leaves, Covers}) => ({
    Covers: Covers.set(seating, when(seats, Covers.at(seating).plus(party), when(leaves, Covers.at(seating).minus(party), Covers.at(seating)))),
  }))
const coverLaws = (r: ReturnType<typeof covers>) => [
  r.law('every seating: covers <= the kitchen limit', ({Covers, limit}) => forall(s => Covers.at(s).atMost(limit))),
]

const roomsWrong = rooms('checks the wrong night')
const overbookingEarly = overbooking('margin checked before the sale')
const refundsLeft = refunds('checks the payment, not what is left')
const holdExpired = hold('confirms an expired hold'), holdConfirmed = hold('holds a confirmed seat')
const waitlistStall = waitlist('a round may offer nothing')
const coversTables = covers('counts tables, not guests')

export const domain: Domain = {
  domain: 'bookings',
  about: 'room-nights, overbooking margins, refunds, expiring holds, member quotes, waitlists, covers per seating',
  cases: [
    machineCase('no double-booked room', 'no room is booked twice for the same night', rooms(), roomLaws(rooms()), [
      {name: 'checks the wrong night', why: 'the availability check reads key room + night, which collides across rooms', rule: roomsWrong, laws: roomLaws(roomsWrong)},
    ]),
    machineCase('overbooking within a margin', 'sales never pass capacity plus the no-show margin', overbooking(), overbookingLaws(overbooking()), [
      {name: 'margin checked before the sale', why: 'the check looks at the seats sold before this sale, not after it', rule: overbookingEarly, laws: overbookingLaws(overbookingEarly)},
    ]),
    machineCase('refunds within payments', 'no booking is refunded more than was paid for it', refunds(), refundLaws(refunds()), [
      {name: 'checks the payment, not what is left', why: 'each refund is compared with the payment, so two refunds can pass it', rule: refundsLeft, laws: refundLaws(refundsLeft)},
    ]),
    machineCase('seat holds that expire', 'a seat is confirmed only within its hold, and a confirmation is final', hold(), holdLaws(hold()), [
      {name: 'confirms an expired hold', why: 'confirmation forgets to check the hold\'s time', rule: holdExpired, laws: holdLaws(holdExpired), steps: holdSteps(holdExpired)},
      {name: 'holds a confirmed seat', why: 'a confirmed seat can be held again, so it is held and confirmed at once', rule: holdConfirmed, laws: holdLaws(holdConfirmed), steps: holdSteps(holdConfirmed)},
    ], {steps: holdSteps(hold())}),
    machineCase('covers per seating', 'no seating serves more guests than the kitchen\'s limit', covers(), coverLaws(covers()), [
      {name: 'counts tables, not guests', why: 'the check adds one per table instead of the party\'s size', rule: coversTables, laws: coverLaws(coversTables)},
    ]),
    decisionCase('member and guest quotes', 'a member never pays more than a guest for the same stay, and no quote passes the subtotal', quoteDecisions, quoteBroken),
    loopCase('draining the waitlist', 'every round seats someone, so the list empties or the room fills', waitlist(), waitlistLaws(waitlist()), [
      {name: 'a round may offer nothing', why: 'a round that offers no seat leaves the waitlist where it was, forever', loop: waitlistStall, laws: waitlistLaws(waitlistStall)},
    ]),
  ],
}
