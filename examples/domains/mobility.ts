// Mobility and fleets: seats in a car, a driver's hours over a rolling window, an EV's energy, a scooter fleet,
// dispatch that never leaves a rider waiting beside a free driver, one rental per rider, surge pricing, charging to a
// target.
import {type Term, all, count, forall, loop, min, nat, oneOf, relation, rule, when} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// A shared ride: riders board only into empty seats and alight only if aboard.
const ride = (bug?: 'checks one seat') => rule('ride seats')
  .params({seats: nat})
  .inputs({op: oneOf('board', 'alight'), n: nat})
  .state({riders: 0})
  .flags(({op, n, riders, seats}) => ({
    boards: op.is('board').and(bug === 'checks one seat' ? riders.lt(seats) : riders.plus(n).atMost(seats)),
    alights: op.is('alight').and(n.atMost(riders)),
  }))
  .step(({n, riders, boards, alights}) => ({riders: when(boards, riders.plus(n), when(alights, riders.minus(n), riders))}))
const rideLaws = (r: ReturnType<typeof ride>) => [r.law('riders <= seats', ({riders, seats}) => riders.atMost(seats))]
const rideOneSeat = ride('checks one seat')

// A driver's hours: each shift (start t, length hours) is accepted only if the hours already driven in the window
// before it, plus this shift, stay within the limit. `driven` (a sum) is the hours in the window ending at now; `used` (a
// query) the hours in the window before the request.
const hours = (bug?: 'forgets this shift') => rule('driver hours window')
  .params({window: nat, limit: nat, now: nat})
  .inputs({t: nat, h: nat})
  .log('t', 'h')
  .sums({driven: (r, {now, window}) => when(r.t.atMost(now).and(now.lt(r.t.plus(window))), r.h, 0)})
  .queries({used: (r, {t, window}) => when(t.lt(r.t.plus(window)), r.h, 0)})
  .flags(({used, h, limit}) => ({fits: bug === 'forgets this shift' ? used.atMost(limit) : used.plus(h).atMost(limit)}))
  .keep(({fits}) => fits)
  .relations(({t, now, driven, used}) => [relation(driven.atMost(used), t.atMost(now))])
const hoursLaws = (r: ReturnType<typeof hours>) => [r.law('hours in the window ending at now <= limit', ({driven, limit}) => driven.atMost(limit))]
const hoursForgets = hours('forgets this shift')

// An EV's energy: charging adds up to the battery's capacity, a trip runs only on the charge it has. As naturals, the
// accounting reads charge + driven = charged.
const ev = (bug?: 'trip unchecked') => rule('ev energy')
  .params({capacity: nat})
  .inputs({op: oneOf('charge', 'trip'), kwh: nat})
  .state({charge: 0, charged: 0, driven: 0})
  .flags(({op, kwh, charge}) => ({trips: op.is('trip').and(bug === 'trip unchecked' ? kwh.atLeast(0) : kwh.atMost(charge))}))
  .step(({op, kwh, charge, charged, driven, capacity, trips}) => {
    const added = when(op.is('charge'), min(kwh, capacity.minus(charge)), 0)
    return {charge: when(trips, charge.minus(kwh), charge.plus(added)), charged: charged.plus(added), driven: when(trips, driven.plus(kwh), driven)}
  })
const evLaws = (r: ReturnType<typeof ev>) => [
  r.law('charge + driven = charged', ({charge, driven, charged}) => charge.plus(driven).eq(charged)),
  r.law('charge <= capacity', ({charge, capacity}) => charge.atMost(capacity)),
]
const evUnchecked = ev('trip unchecked')

// A scooter fleet: every scooter is available, rented or in maintenance, and moves between them one at a time.
const fleet = (bug?: 'returns unrented') => rule('scooter fleet')
  .params({total: nat})
  .inputs({op: oneOf('rent', 'return', 'service', 'fix')})
  .state({available: ({total}) => total, rented: 0, repair: 0})
  .flags(({op, available, rented, repair}) => ({
    rents: op.is('rent').and(available.gt(0)),
    returns: op.is('return').and(bug === 'returns unrented' ? available.atLeast(0) : rented.gt(0)),
    services: op.is('service').and(available.gt(0)),
    fixes: op.is('fix').and(repair.gt(0)),
  }))
  .step(({available, rented, repair, rents, returns, services, fixes}) => ({
    available: available.plus(count(returns.or(fixes))).minus(count(rents.or(services))),
    rented: when(rents, rented.plus(1), when(returns, rented.minus(1), rented)),
    repair: when(services, repair.plus(1), when(fixes, repair.minus(1), repair)),
  }))
const fleetLaws = (r: ReturnType<typeof fleet>) => [r.law('available + rented + repair = total', ({available, rented, repair, total}) => available.plus(rented).plus(repair).eq(total))]
const fleetUnrented = fleet('returns unrented')

// Dispatch: a request is matched at once when a driver is free, else it waits; a driver who finishes or joins takes
// the next waiting rider first. So no rider ever waits while a driver is free.
const dispatch = (bug?: 'finish frees the driver') => rule('dispatch')
  .inputs({op: oneOf('request', 'finish', 'join')})
  .state({waiting: 0, free: 0, busy: 0})
  .flags(({op, busy}) => ({finishes: op.is('finish').and(busy.gt(0))}))
  .step(({op, waiting, free, busy, finishes}) => {
    const queue = waiting.gt(0), takesNext = bug === 'finish frees the driver' ? op.is('join').and(queue) : finishes.or(op.is('join')).and(queue)
    const freed = all(finishes, takesNext.not()), joins = all(op.is('join'), takesNext.not())
    const matched = all(op.is('request'), free.gt(0))
    return {
      waiting: when(op.is('request').and(matched.not()), waiting.plus(1), when(takesNext, waiting.minus(1), waiting)),
      free: when(matched, free.minus(1), when(freed.or(joins), free.plus(1), free)),
      busy: when(matched.or(all(op.is('join'), takesNext)), busy.plus(1), when(freed, busy.minus(1), busy)),
    }
  })
const dispatchLaws = (r: ReturnType<typeof dispatch>) => [r.law('no rider waits while a driver is free', ({waiting, free}) => waiting.eq(0).or(free.eq(0)))]
const dispatchSteps = (r: ReturnType<typeof dispatch>) => [
  r.stepLaw('a request with a free driver is matched at once', ({busy}, after) => after.busy.eq(busy.plus(1)), ({op, free}) => op.is('request').and(free.gt(0))),
]
const dispatchFrees = dispatch('finish frees the driver')

// One rental per rider: a rider starts a rental only with none active.
const rentals = (bug?: 'allows a second') => rule('one rental per rider')
  .inputs({op: oneOf('start', 'end'), rider: nat})
  .maps({Active: 0})
  .flags(({op, rider, Active}) => ({
    starts: op.is('start').and(bug === 'allows a second' ? Active.at(rider).atMost(1) : Active.at(rider).eq(0)),
    ends: op.is('end').and(Active.at(rider).gt(0)),
  }))
  .step(({rider, starts, ends, Active}) => ({Active: Active.set(rider, when(starts, Active.at(rider).plus(1), when(ends, Active.at(rider).minus(1), Active.at(rider))))}))
const rentalLaws = (r: ReturnType<typeof rentals>) => [r.law('every rider: at most one active rental', ({Active}) => forall(k => Active.at(k).atMost(1)))]
const rentalsSecond = rentals('allows a second')

// Surge pricing: the surcharge grows with the demand above supply, capped; with no excess demand the base price holds.
const surge = rule('surge pricing').params({cap: nat}).inputs({base: nat, demand: nat, supply: nat})
type SurgeEnv = Parameters<Parameters<typeof surge.decide>[1]>[0]
const price = (e: SurgeEnv, capped = true): Term => e.base.plus(capped ? min(e.demand.minus(e.supply), e.cap) : e.demand.minus(e.supply))
const surgeDecisions = [
  surge.decide('the price stays within base + cap', () => [], e => price(e).atMost(e.base.plus(e.cap))),
  surge.decide('the price never falls below base', () => [], e => e.base.atMost(price(e))),
  surge.decide('no excess demand, no surcharge', ({demand, supply}) => demand.atMost(supply), e => price(e).eq(e.base)),
]
const surgeUncapped = surge.decide('the price stays within base + cap (cap forgotten)', () => [], e => price(e, false).atMost(e.base.plus(e.cap)))

// Charging to a target: each charging slot adds at least one unit, so the car reaches its target.
const charging = (bug?: 'idle slots') => {
  const base = loop(bug ? 'charging to a target, idle slots' : 'charging to a target')
    .params({target: nat})
    .inputs({rate: nat})
    .state({level: 0})
    .while(({level, target}) => level.lt(target))
    .body(({level, target, rate}) => ({level: min(level.plus(rate), target)}))
    .rank(({level, target}) => target.minus(level))
  return bug ? base : base.assume(({rate}) => rate.atLeast(1))
}
const chargingLaws = (l: ReturnType<typeof charging>) => [l.law('level <= target', ({level, target}) => level.atMost(target))]

export const domain: Domain = {
  domain: 'mobility',
  about: 'ride seats, driver hours, EV energy, scooter fleet, dispatch, one rental per rider, surge pricing, charging to a target',
  cases: [
    machineCase('ride seats', 'a car never carries more riders than seats', ride(), rideLaws(ride()), [
      {name: 'checks one seat', why: 'a group boards whenever one seat is free', rule: rideOneSeat, laws: rideLaws(rideOneSeat)},
    ]),
    machineCase('driver hours window', 'no driver passes the limit in any window ending at now, read from the log', hours(), hoursLaws(hours()), [
      {name: 'forgets this shift', why: 'the check compares the hours already driven with the limit, leaving out the new shift', rule: hoursForgets, laws: hoursLaws(hoursForgets)},
    ]),
    machineCase('ev energy', 'every kWh charged is in the battery or was driven, and the battery never passes its capacity', ev(), evLaws(ev()), [
      {name: 'trip unchecked', why: 'a trip longer than the charge runs, and the truncated charge loses track', rule: evUnchecked, laws: evLaws(evUnchecked)},
    ]),
    machineCase('scooter fleet', 'every scooter is available, rented or in repair', fleet(), fleetLaws(fleet()), [
      {name: 'returns unrented', why: 'a return is accepted with no scooter out', rule: fleetUnrented, laws: fleetLaws(fleetUnrented)},
    ]),
    machineCase('dispatch', 'no rider waits while a driver is free, and a request with a free driver is matched at once', dispatch(), dispatchLaws(dispatch()), [
      {name: 'finish frees the driver', why: 'a finishing driver goes back to free even with riders waiting', rule: dispatchFrees, laws: dispatchLaws(dispatchFrees), steps: dispatchSteps(dispatchFrees)},
    ], {steps: dispatchSteps(dispatch())}),
    machineCase('one rental per rider', 'no rider holds two rentals at once', rentals(), rentalLaws(rentals()), [
      {name: 'allows a second', why: 'the start check allows a rider holding one rental', rule: rentalsSecond, laws: rentalLaws(rentalsSecond)},
    ]),
    decisionCase('surge pricing', 'the surcharge follows excess demand, capped, and is zero without it', surgeDecisions, [
      {name: 'cap forgotten', why: 'the surcharge is the whole excess demand', decision: surgeUncapped},
    ]),
    loopCase('charging to a target', 'every slot adds charge, so the car reaches its target and never passes it', charging(), chargingLaws(charging()), [
      {name: 'idle slots', why: 'a slot may add nothing, so charging need not end', loop: charging('idle slots'), laws: chargingLaws(charging('idle slots'))},
    ]),
  ],
}
