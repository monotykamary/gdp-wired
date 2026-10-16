// Public services and health: medication dose limits, elections, clinic slots, benefit eligibility, waitlists,
// elevators, traffic lights.
import {type Bool, type Choice, type Cond, type Maybe, type Term, bool, forall, loop, maybe, nat, no, oneOf, relation, rule, upTo, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// A daily dose limit on one patient's chart: a dose given at time t goes in only if the doses charted in the day before
// it (`given`, read from the log) plus this one stay within maxDose. `last24` sums the doses in the day ending at now.
const medication = rule('daily dose limit')
  .params({day: nat, maxDose: nat, now: nat})
  .inputs({dose: nat, t: nat})
  .log('dose', 't')
  .sums({last24: (r, {now, day}) => when(r.t.atMost(now).and(now.lt(r.t.plus(day))), r.dose, 0)})
  .queries({given: (r, {t, day}) => when(t.lt(r.t.plus(day)), r.dose, 0)})
  .flags(({given, dose, maxDose}) => ({ok: given.plus(dose).atMost(maxDose)}))
  .keep(({ok}) => ok)
  .relations(({t, now, last24, given}) => [relation(last24.atMost(given), t.atMost(now))])
const doseLawOf = (r: typeof medication) => r.law('doses in the day ending at now <= maxDose', ({last24, maxDose}) => last24.atMost(maxDose))
const medicationPruned = medication.prune('t', ({day}) => day)
const singleDoseOnly = medication.flags(({dose, maxDose}) => ({ok2: dose.atMost(maxDose)})).keep(({ok2}) => ok2)
const prunedEarly = medication.prune('t', ({day}) => day.minus(1))

// One vote per voter: a ballot counts only for a registered voter (below `voters`) who hasn't voted, and every counted
// ballot lands in exactly one tally.
const ballot = rule('one vote per voter')
  .params({voters: nat})
  .inputs({voter: nat, choice: oneOf('yes', 'no', 'blank')})
  .state({ayes: 0, nays: 0, blanks: 0, cast: 0})
  .maps({Voted: 0})
  .flags(({voter, voters, Voted}) => ({counted: voter.lt(voters).and(Voted.at(voter).eq(0))}))
  .step(({choice, voter, counted, ayes, nays, blanks, cast, Voted}) => ({
    Voted: Voted.bump(voter, counted),
    ayes: when(counted.and(choice.is('yes')), ayes.plus(1), ayes),
    nays: when(counted.and(choice.is('no')), nays.plus(1), nays),
    blanks: when(counted.and(choice.is('blank')), blanks.plus(1), blanks),
    cast: when(counted, cast.plus(1), cast),
  }))
const ballotLawsOf = (r: typeof ballot) => [
  r.law('the tallies add up to the ballots cast', ({ayes, nays, blanks, cast}) => ayes.plus(nays).plus(blanks).eq(cast)),
  r.law('every voter votes at most once', ({Voted}) => forall(v => Voted.at(v).atMost(1))),
  r.law('only registered voters vote', ({Voted, voters}) => forall(v => v.lt(voters).or(Voted.at(v).eq(0)))),
]
const ballotTwice = ballot.flags(({voter, voters}) => ({counted2: voter.lt(voters)}))
  .step(({choice, voter, counted2, ayes, nays, blanks, cast, Voted}) => ({
    Voted: Voted.bump(voter, counted2),
    ayes: when(counted2.and(choice.is('yes')), ayes.plus(1), ayes),
    nays: when(counted2.and(choice.is('no')), nays.plus(1), nays),
    blanks: when(counted2.and(choice.is('blank')), blanks.plus(1), blanks),
    cast: when(counted2, cast.plus(1), cast),
  }))
const ballotUnregistered = ballot.flags(({voter, Voted}) => ({counted3: Voted.at(voter).eq(0)}))
  .step(({choice, voter, counted3, ayes, nays, blanks, cast, Voted}) => ({
    Voted: Voted.bump(voter, counted3),
    ayes: when(counted3.and(choice.is('yes')), ayes.plus(1), ayes),
    nays: when(counted3.and(choice.is('no')), nays.plus(1), nays),
    blanks: when(counted3.and(choice.is('blank')), blanks.plus(1), blanks),
    cast: when(counted3, cast.plus(1), cast),
  }))
const ballotBlankAsYes = ballot.step(({choice, voter, counted, ayes, nays, blanks, cast, Voted}) => ({
  Voted: Voted.bump(voter, counted),
  ayes: when(counted.and(choice.is('yes').or(choice.is('blank'))), ayes.plus(1), ayes),
  nays: when(counted.and(choice.is('no')), nays.plus(1), nays),
  blanks: when(counted.and(choice.is('blank')), blanks.plus(1), blanks),
  cast: when(counted, cast.plus(1), cast),
}))

// Clinic slots: a slot opens (or is resized) to a capacity of at most `rooms`, never below what is already booked; a
// booking needs a free place in its slot; a cancellation frees one.
const clinic = rule('clinic slots')
  .params({rooms: nat})
  .inputs({op: oneOf('open', 'book', 'cancel'), slot: nat, n: nat})
  .maps({Cap: 0, Booked: 0})
  .flags(({op, slot, n, rooms, Cap, Booked}) => ({
    opens: op.is('open').and(n.atMost(rooms), Booked.at(slot).atMost(n)),
    books: op.is('book').and(Booked.at(slot).lt(Cap.at(slot))),
  }))
  .step(({op, slot, n, opens, books, Cap, Booked}) => ({
    Cap: Cap.set(slot, when(opens, n, Cap.at(slot))),
    Booked: Booked.set(slot, when(books, Booked.at(slot).plus(1), when(op.is('cancel'), Booked.at(slot).minus(1), Booked.at(slot)))),
  }))
const clinicLawsOf = (r: typeof clinic) => [
  r.law('every slot: booked <= capacity', ({Booked, Cap}) => forall(s => Booked.at(s).atMost(Cap.at(s)))),
  r.law('every slot: capacity <= rooms', ({Cap, rooms}) => forall(s => Cap.at(s).atMost(rooms))),
]
const clinicShrinks = clinic.flags(({op, n, rooms}) => ({opens2: op.is('open').and(n.atMost(rooms))}))
  .step(({op, slot, n, opens2, books, Cap, Booked}) => ({
    Cap: Cap.set(slot, when(opens2, n, Cap.at(slot))),
    Booked: Booked.set(slot, when(books, Booked.at(slot).plus(1), when(op.is('cancel'), Booked.at(slot).minus(1), Booked.at(slot)))),
  }))

// Benefit eligibility: a monthly income at most the base limit, raised by the household type, 300 per dependent and 500
// with a disability. No income on file, no benefit.
const benefit = rule('benefit eligibility')
  .params({limit: nat})
  .inputs({household: oneOf('single', 'couple', 'family'), income: maybe(nat), dependents: upTo(6), disabled: bool})
type BenefitEnv = {limit: Term, household: Choice<'single' | 'couple' | 'family'>, income: Maybe<Term>, dependents: Term, disabled: Bool}
const threshold = ({limit, household, dependents, disabled}: BenefitEnv) =>
  limit.plus(household.match({single: () => 0, couple: () => 800, family: () => 1200})).plus(dependents.times(300)).plus(when(disabled, 500, 0))
const eligible = (env: BenefitEnv) => env.income.match({none: () => no, some: i => i.atMost(threshold(env))})
const eligibleMissingAsZero = (env: BenefitEnv) => env.income.match({none: () => yes, some: i => i.atMost(threshold(env))})
const benefitDecisions = [
  benefit.decide('no income on file, no benefit', ({income}) => income.isNone, env => eligible(env).not()),
  benefit.decide('nobody qualifies above the most generous threshold', env => eligible(env), ({income, limit}) => income.match({none: () => no, some: i => i.atMost(limit.plus(1200 + 6 * 300 + 500))})),
  benefit.decide('a single adult, no dependents or disability, is held to the base limit', env => [env.household.is('single'), env.dependents.eq(0), env.disabled.not(), eligible(env)], ({income, limit}) => income.match({none: () => no, some: i => i.atMost(limit)})),
  benefit.decide('a disabled applicant within the base limit always qualifies', ({disabled, income, limit}) => [disabled, income.match({none: () => no, some: i => i.atMost(limit)})], env => eligible(env)),
]

// A class waitlist: a join takes a seat while one is free, else waits if the list has room; a leaving student's seat
// goes to the first waiter if there is one; a waiter may drop out.
const waitlist = rule('class waitlist')
  .params({capacity: nat, maxWait: nat})
  .inputs({op: oneOf('join', 'leave', 'drop')})
  .state({enrolled: 0, waiting: 0})
  .flags(({op, enrolled, waiting, capacity, maxWait}) => ({
    seat: op.is('join').and(enrolled.lt(capacity)),
    queue: op.is('join').and(enrolled.atLeast(capacity), waiting.lt(maxWait)),
    promote: op.is('leave').and(enrolled.gt(0), waiting.gt(0)),
    free: op.is('leave').and(enrolled.gt(0), waiting.eq(0)),
  }))
  .step(({op, seat, queue, promote, free, enrolled, waiting}) => ({
    enrolled: when(seat, enrolled.plus(1), when(free, enrolled.minus(1), enrolled)),
    waiting: when(queue, waiting.plus(1), when(promote.or(op.is('drop')), waiting.minus(1), waiting)),
  }))
const waitlistLawsOf = (r: typeof waitlist) => [
  r.law('enrolled <= capacity', ({enrolled, capacity}) => enrolled.atMost(capacity)),
  r.law('waiting <= maxWait', ({waiting, maxWait}) => waiting.atMost(maxWait)),
  r.law('nobody waits while a seat is free', ({waiting, enrolled, capacity}) => waiting.eq(0).or(enrolled.eq(capacity))),
]
const waitlistOverseats = waitlist.flags(({op, enrolled, capacity}) => ({seat2: op.is('join').and(enrolled.atMost(capacity))}))
  .step(({op, seat2, queue, promote, free, enrolled, waiting}) => ({
    enrolled: when(seat2, enrolled.plus(1), when(free, enrolled.minus(1), enrolled)),
    waiting: when(queue, waiting.plus(1), when(promote.or(op.is('drop')), waiting.minus(1), waiting)),
  }))
const waitlistFreesAndPromotes = waitlist.step(({op, seat, queue, promote, free, enrolled, waiting}) => ({
  enrolled: when(seat, enrolled.plus(1), when(free.or(promote), enrolled.minus(1), enrolled)),
  waiting: when(queue, waiting.plus(1), when(promote.or(op.is('drop')), waiting.minus(1), waiting)),
}))

// Elevator safety: the doors open only while stopped, the car starts only with the doors closed, and it moves between
// floor 0 and the top floor.
const elevator = rule('elevator safety')
  .params({top: nat})
  .inputs({op: oneOf('open', 'close', 'start', 'stop', 'up', 'down')})
  .state({floor: 0, moving: 0, door: 0})
  .flags(({op, moving, door, floor, top}) => ({
    opens: op.is('open').and(moving.eq(0)),
    starts: op.is('start').and(door.eq(0)),
    rises: op.is('up').and(moving.eq(1), floor.lt(top)),
    falls: op.is('down').and(moving.eq(1), floor.gt(0)),
  }))
  .step(({op, opens, starts, rises, falls, floor, moving, door}) => ({
    door: when(opens, 1, when(op.is('close'), 0, door)),
    moving: when(starts, 1, when(op.is('stop'), 0, moving)),
    floor: when(rises, floor.plus(1), when(falls, floor.minus(1), floor)),
  }))
const elevatorLawsOf = (r: typeof elevator) => [
  r.law('the doors are closed while moving', ({moving, door}) => moving.eq(0).or(door.eq(0))),
  r.law('the floor stays within 0..top', ({floor, top}) => floor.atMost(top)),
]
const elevatorOpensMoving = elevator.flags(({op}) => ({opens2: op.is('open')}))
  .step(({op, opens2, starts, rises, falls, floor, moving, door}) => ({
    door: when(opens2, 1, when(op.is('close'), 0, door)),
    moving: when(starts, 1, when(op.is('stop'), 0, moving)),
    floor: when(rises, floor.plus(1), when(falls, floor.minus(1), floor)),
  }))
const elevatorPastTop = elevator.flags(({op, moving, floor, top}) => ({rises2: op.is('up').and(moving.eq(1), floor.atMost(top))}))
  .step(({op, opens, starts, rises2, falls, floor, moving, door}) => ({
    door: when(opens, 1, when(op.is('close'), 0, door)),
    moving: when(starts, 1, when(op.is('stop'), 0, moving)),
    floor: when(rises2, floor.plus(1), when(falls, floor.minus(1), floor)),
  }))

// A traffic light at a crossing (0 red, 1 green, 2 yellow per direction): a direction turns green only when both are
// red and no pedestrian walk is on; green turns yellow, yellow red. The walk signal comes on only with both red.
const lightOf = (greenWhen: (other: Term) => Cond) => rule('traffic light')
  .inputs({op: oneOf('ns', 'ew', 'walk', 'dontWalk')})
  .state({ns: 0, ew: 0, walk: 0})
  .flags(({op, ns, ew, walk}) => ({
    nsGo: op.is('ns').and(ns.eq(0), greenWhen(ew), walk.eq(0)),
    ewGo: op.is('ew').and(ew.eq(0), greenWhen(ns), walk.eq(0)),
    walks: op.is('walk').and(ns.eq(0), ew.eq(0)),
  }))
  .step(({op, ns, ew, walk, nsGo, ewGo, walks}) => ({
    ns: when(op.is('ns'), when(ns.eq(0), when(nsGo, 1, 0), when(ns.eq(1), 2, 0)), ns),
    ew: when(op.is('ew'), when(ew.eq(0), when(ewGo, 1, 0), when(ew.eq(1), 2, 0)), ew),
    walk: when(walks, 1, when(op.is('dontWalk'), 0, walk)),
  }))
const light = lightOf(other => other.eq(0))
const lightLawsOf = (r: typeof light) => [
  r.law('one direction is always red', ({ns, ew}) => ns.eq(0).or(ew.eq(0))),
  r.law('the walk signal only with both red', ({walk, ns, ew}) => walk.eq(0).or(ns.eq(0).and(ew.eq(0)))),
]
const lightIgnoresYellow = lightOf(other => other.ne(1))

// Elevator dispatch: at a request's floor the car serves it and heads to the next one (at most `top` floors away),
// moving one floor per turn. The rank is the pair (requests pending, floors to go).
const dispatch = (serves: boolean) => loop(serves ? 'elevator dispatch' : 'elevator dispatch, never serves')
  .params({top: nat, requests: nat})
  .inputs({next: nat})
  .state({pending: ({requests}) => requests, dist: 0})
  .assume(({next, top}) => next.atMost(top))
  .while(({pending, dist}) => pending.gt(0).or(dist.gt(0)))
  .body(({pending, dist, next}) => ({
    dist: when(dist.gt(0), dist.minus(1), when(pending.gt(1), next, 0)),
    pending: when(dist.eq(0), serves ? pending.minus(1) : pending, pending),
  }))
  .rank(({pending, dist}) => [pending, dist])
const dispatchLawsOf = (l: ReturnType<typeof dispatch>) => [
  l.law('floors to go <= top', ({dist, top}) => dist.atMost(top)),
  l.law('pending <= requests', ({pending, requests}) => pending.atMost(requests)),
]

export const domain: Domain = {
  domain: 'public',
  about: 'medication dose limits, elections, clinic slots, benefit eligibility, waitlists, elevators, traffic lights',
  cases: [
    machineCase('daily dose limit', 'the doses charted in any day ending at now stay within the daily maximum, read from the log', medication, [doseLawOf(medication)], [
      {name: 'checks the single dose', why: 'each dose is checked against the daily maximum alone, not the day\'s total', rule: singleDoseOnly, laws: [doseLawOf(singleDoseOnly)]},
    ]),
    machineCase('daily dose limit, pruned', 'the same, the chart dropping doses older than a day', medicationPruned, [doseLawOf(medicationPruned)], [
      {name: 'prunes a minute early', why: 'doses are dropped one minute before they leave the day, so the check undercounts', rule: prunedEarly, laws: [doseLawOf(prunedEarly)]},
    ]),
    machineCase('one vote per voter', 'registered voters vote once, and the tallies add up to the ballots cast', ballot, ballotLawsOf(ballot), [
      {name: 'votes twice', why: 'the ballot forgets to check whether the voter already voted', rule: ballotTwice, laws: ballotLawsOf(ballotTwice)},
      {name: 'unregistered voters', why: 'the ballot forgets to check the voter roll', rule: ballotUnregistered, laws: ballotLawsOf(ballotUnregistered)},
      {name: 'blank counted as yes', why: 'a blank ballot also lands in the yes tally', rule: ballotBlankAsYes, laws: ballotLawsOf(ballotBlankAsYes)},
    ]),
    machineCase('clinic slots', 'no slot is booked past its capacity, and no capacity passes the rooms', clinic, clinicLawsOf(clinic), [
      {name: 'shrinks below bookings', why: 'resizing a slot forgets the bookings it already has', rule: clinicShrinks, laws: clinicLawsOf(clinicShrinks)},
    ]),
    decisionCase('benefit eligibility', 'a missing income fails closed, and nobody qualifies above the threshold their household earns', benefitDecisions, [
      {name: 'missing income read as zero', why: 'an empty income field is treated as no income', decision: benefit.decide('no income on file, no benefit', ({income}) => income.isNone, env => eligibleMissingAsZero(env).not())},
    ]),
    machineCase('class waitlist', 'enrollment within capacity, the waitlist within its room, and nobody waits while a seat is free', waitlist, waitlistLawsOf(waitlist), [
      {name: 'seats one too many', why: 'a join takes a seat while enrolled <= capacity (off by one)', rule: waitlistOverseats, laws: waitlistLawsOf(waitlistOverseats)},
      {name: 'frees the seat and promotes', why: 'a leave with waiters both frees the seat and promotes, losing a seat', rule: waitlistFreesAndPromotes, laws: waitlistLawsOf(waitlistFreesAndPromotes)},
    ]),
    machineCase('elevator safety', 'the doors stay closed while moving, and the car stays between floor 0 and the top', elevator, elevatorLawsOf(elevator), [
      {name: 'opens while moving', why: 'the door command forgets to check the car is stopped', rule: elevatorOpensMoving, laws: elevatorLawsOf(elevatorOpensMoving)},
      {name: 'rises past the top', why: 'the up command checks floor <= top (off by one)', rule: elevatorPastTop, laws: elevatorLawsOf(elevatorPastTop)},
    ]),
    machineCase('traffic light', 'one direction is always red, and pedestrians walk only with both red', light, lightLawsOf(light), [
      {name: 'ignores yellow', why: 'a direction turns green when the other is not green, though it may still be yellow', rule: lightIgnoresYellow, laws: lightLawsOf(lightIgnoresYellow)},
    ]),
    loopCase('elevator dispatch', 'every request is served, rank (requests pending, floors to go) dropping every turn', dispatch(true), dispatchLawsOf(dispatch(true)), [
      {name: 'never serves', why: 'arriving at a request\'s floor forgets to mark it served', loop: dispatch(false), laws: dispatchLawsOf(dispatch(false))},
    ]),
  ],
}
