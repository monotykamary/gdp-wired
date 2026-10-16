// Supply chain and manufacturing: warehouse picking, quality holds, batch production against a bill of materials,
// cold-chain excursions, shipping caps, purchase-order receiving, recall decisions, maintenance intervals, a pick wave.
import {type Bool, type Choice, type Cond, type MapRef, type Maybe, type Term, all, bool, count, forall, loop, maybe, min, nat, no, oneOf, relation, rule, upTo, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// Warehouse picking: per SKU, stock on hand and the units picked for open orders. A pick goes through only if the
// picks stay within what's on hand; shipping takes the units out of both; a write-off (damage, a miscount) only takes
// what isn't promised to a pick.
type PickEnv = {sku: Term, qty: Term, OnHand: MapRef, Picked: MapRef}
const picking = (canPick: (e: PickEnv) => Cond, canWriteOff: (e: PickEnv) => Cond) => rule('warehouse picking')
  .inputs({op: oneOf('receive', 'pick', 'ship', 'writeoff'), sku: nat, qty: nat})
  .maps({OnHand: 0, Picked: 0})
  .flags(e => ({
    picking: e.op.is('pick').and(canPick(e)),
    shipping: e.op.is('ship').and(e.qty.atMost(e.Picked.at(e.sku))),
    writingOff: e.op.is('writeoff').and(canWriteOff(e)),
  }))
  .step(({op, sku, qty, picking, shipping, writingOff, OnHand, Picked}) => ({
    OnHand: OnHand.set(sku, when(op.is('receive'), OnHand.at(sku).plus(qty), when(shipping.or(writingOff), OnHand.at(sku).minus(qty), OnHand.at(sku)))),
    Picked: Picked.set(sku, when(picking, Picked.at(sku).plus(qty), when(shipping, Picked.at(sku).minus(qty), Picked.at(sku)))),
  }))
const unpromised = ({sku, qty, OnHand, Picked}: PickEnv) => Picked.at(sku).plus(qty).atMost(OnHand.at(sku))
const warehouse = picking(unpromised, unpromised)
const pickLaws = [warehouse.law('every SKU: picked <= on hand', ({Picked, OnHand}) => forall(s => Picked.at(s).atMost(OnHand.at(s))))]
const warehousePicksOnHand = picking(({sku, qty, OnHand}) => qty.atMost(OnHand.at(sku)), unpromised)
const warehouseWritesOffPicked = picking(unpromised, () => yes)

// Quality holds: a lot on hold never ships. A hold is refused on a lot that has already shipped (that's a recall, not a
// hold), and a shipment is refused on a held lot.
type HoldEnv = {lot: Term, Held: MapRef, Shipped: MapRef}
const holds = (canShip: (e: HoldEnv) => Cond) => rule('quality holds')
  .inputs({op: oneOf('hold', 'release', 'ship'), lot: nat, qty: nat})
  .maps({Held: 0, Shipped: 0})
  .flags(e => ({holding: e.op.is('hold').and(e.Shipped.at(e.lot).eq(0)), shipping: e.op.is('ship').and(canShip(e))}))
  .step(({op, lot, qty, holding, shipping, Held, Shipped}) => ({
    Held: Held.set(lot, when(holding, 1, when(op.is('release'), 0, Held.at(lot)))),
    Shipped: Shipped.bump(lot, shipping, qty),
  }))
const quality = holds(({lot, Held}) => Held.at(lot).eq(0))
const holdLaws = [
  quality.law('no lot is both held and shipped', ({Held, Shipped}) => forall(l => Held.at(l).eq(0).or(Shipped.at(l).eq(0)))),
  quality.law('a hold is a flag', ({Held}) => forall(l => Held.at(l).atMost(1))),
]
const qualityShipsHeld = holds(() => yes)

// Batch production: a unit takes 4 bolts and 2 panels (the bill of materials as constant multiples). A build consumes
// the components only if they were received.
type BomEnv = {qty: Term, boltsIn: Term, boltsUsed: Term, panelsIn: Term, panelsUsed: Term}
const production = (boltsPerUnit: number, enough: (e: BomEnv, bolts: number) => Cond) => rule('batch production')
  .inputs({op: oneOf('bolts', 'panels', 'build'), qty: nat})
  .state({boltsIn: 0, boltsUsed: 0, panelsIn: 0, panelsUsed: 0, produced: 0})
  .flags(e => ({building: e.op.is('build').and(enough(e, boltsPerUnit))}))
  .step(({op, qty, boltsIn, boltsUsed, panelsIn, panelsUsed, produced, building}) => ({
    boltsIn: when(op.is('bolts'), boltsIn.plus(qty), boltsIn),
    panelsIn: when(op.is('panels'), panelsIn.plus(qty), panelsIn),
    boltsUsed: when(building, boltsUsed.plus(qty.times(boltsPerUnit)), boltsUsed),
    panelsUsed: when(building, panelsUsed.plus(qty.times(2)), panelsUsed),
    produced: when(building, produced.plus(qty), produced),
  }))
const bothComponents = ({qty, boltsIn, boltsUsed, panelsIn, panelsUsed}: BomEnv, bolts: number) => all(boltsUsed.plus(qty.times(bolts)).atMost(boltsIn), panelsUsed.plus(qty.times(2)).atMost(panelsIn))
const factory = production(4, bothComponents)
const bomLaws = [
  factory.law('produced × 4 <= bolts consumed', ({produced, boltsUsed}) => produced.times(4).atMost(boltsUsed)),
  factory.law('produced × 2 <= panels consumed', ({produced, panelsUsed}) => produced.times(2).atMost(panelsUsed)),
  factory.law('bolts consumed <= received', ({boltsUsed, boltsIn}) => boltsUsed.atMost(boltsIn)),
  factory.law('panels consumed <= received', ({panelsUsed, panelsIn}) => panelsUsed.atMost(panelsIn)),
]
const factoryBomTypo = production(3, bothComponents)
const factoryChecksBoltsOnly = production(4, ({qty, boltsIn, boltsUsed}, bolts) => boltsUsed.plus(qty.times(bolts)).atMost(boltsIn))

// Cold-chain excursions: a reefer's door may open for `minutes` at time t only if the excursion minutes logged within
// `span` before t, plus these, stay within the allowance, and the openings within `span` stay below `events`. The sums
// read the window ending at now; the relations say the window before a request at or before now covers it.
const coldChain = (opts: {edge: 0 | 1, prune?: (p: {span: Term}) => Term}) => {
  const inWindow = (t: Term, rt: Term, span: Term) => t.plus(opts.edge).lt(rt.plus(span))
  const base = rule('cold-chain excursions')
    .params({span: nat, allowance: nat, events: nat, now: nat})
    .inputs({minutes: nat, t: nat})
    .log('minutes', 't')
    .sums({
      recentMinutes: (r, {now, span}) => when(r.t.atMost(now).and(now.lt(r.t.plus(span))), r.minutes, 0),
      recentEvents: (r, {now, span}) => count(r.t.atMost(now).and(now.lt(r.t.plus(span)))),
    })
    .queries({
      minutesBefore: (r, {t, span}) => when(inWindow(t, r.t, span), r.minutes, 0),
      eventsBefore: (r, {t, span}) => count(inWindow(t, r.t, span)),
    })
    .flags(({minutes, minutesBefore, eventsBefore, allowance, events}) => ({allowed: all(minutesBefore.plus(minutes).atMost(allowance), eventsBefore.lt(events))}))
    .keep(({allowed}) => allowed)
    .relations(({t, now, recentMinutes, minutesBefore, recentEvents, eventsBefore}) => [
      relation(recentMinutes.atMost(minutesBefore), t.atMost(now)),
      relation(recentEvents.atMost(eventsBefore), t.atMost(now)),
    ])
  return opts.prune ? base.prune('t', opts.prune) : base
}
const coldLawsOf = (r: ReturnType<typeof coldChain>) => [
  r.law('excursion minutes in the window ending at now <= allowance', ({recentMinutes, allowance}) => recentMinutes.atMost(allowance)),
  r.law('openings in the window ending at now <= events', ({recentEvents, events}) => recentEvents.atMost(events)),
]
const cold = coldChain({edge: 0}), coldLaws = coldLawsOf(cold)
const coldEdge = coldChain({edge: 1})
const coldPruned = coldChain({edge: 0, prune: ({span}) => span})
const coldPrunedEarly = coldChain({edge: 0, prune: ({span}) => span.minus(1)})

// Shipping caps: a container takes a pallet only if weight, volume and pallet positions all stay within its limits.
type LoadEnv = {weight: Term, volume: Term, kg: Term, m3: Term, pallets: Term, maxKg: Term, maxM3: Term, positions: Term}
const container = (fits: (e: LoadEnv) => Cond) => rule('shipping weight and volume caps')
  .params({maxKg: nat, maxM3: nat, positions: nat})
  .inputs({op: oneOf('load', 'unload'), weight: nat, volume: nat})
  .state({kg: 0, m3: 0, pallets: 0})
  .flags(e => ({loading: e.op.is('load').and(fits(e)), unloading: e.op.is('unload').and(e.pallets.gt(0))}))
  .step(({weight, volume, kg, m3, pallets, loading, unloading}) => ({
    kg: when(loading, kg.plus(weight), when(unloading, kg.minus(weight), kg)),
    m3: when(loading, m3.plus(volume), when(unloading, m3.minus(volume), m3)),
    pallets: when(loading, pallets.plus(1), when(unloading, pallets.minus(1), pallets)),
  }))
const fitsAll = ({weight, volume, kg, m3, pallets, maxKg, maxM3, positions}: LoadEnv) => all(kg.plus(weight).atMost(maxKg), m3.plus(volume).atMost(maxM3), pallets.lt(positions))
const shipping = container(fitsAll)
const shippingLaws = [
  shipping.law('weight <= max weight', ({kg, maxKg}) => kg.atMost(maxKg)),
  shipping.law('volume <= max volume', ({m3, maxM3}) => m3.atMost(maxM3)),
  shipping.law('pallets <= positions', ({pallets, positions}) => pallets.atMost(positions)),
]
const shippingWeightOnly = container(({weight, kg, pallets, maxKg, positions}) => all(kg.plus(weight).atMost(maxKg), pallets.lt(positions)))
const shippingOneTooMany = container(({weight, volume, kg, m3, pallets, maxKg, maxM3, positions}) => all(kg.plus(weight).atMost(maxKg), m3.plus(volume).atMost(maxM3), pallets.atMost(positions)))

// Purchase-order receiving: per PO line, receipts stay within the quantity ordered plus a receiving tolerance; a
// cancellation can't take the order below what was received (beyond the tolerance).
type PoEnv = {line: Term, qty: Term, slack: Term, Ordered: MapRef, Received: MapRef}
const purchasing = (canReceive: (e: PoEnv) => Cond, canCancel: (e: PoEnv) => Cond) => rule('purchase-order receiving')
  .params({slack: nat})
  .inputs({op: oneOf('order', 'receive', 'cancel'), line: nat, qty: nat})
  .maps({Ordered: 0, Received: 0})
  .flags(e => ({receiving: e.op.is('receive').and(canReceive(e)), cancelling: e.op.is('cancel').and(canCancel(e))}))
  .step(({op, line, qty, receiving, cancelling, Ordered, Received}) => ({
    Ordered: Ordered.set(line, when(op.is('order'), Ordered.at(line).plus(qty), when(cancelling, Ordered.at(line).minus(qty), Ordered.at(line)))),
    Received: Received.bump(line, receiving, qty),
  }))
const withinTolerance = ({line, qty, slack, Ordered, Received}: PoEnv) => Received.at(line).plus(qty).atMost(Ordered.at(line).plus(slack))
const po = purchasing(withinTolerance, withinTolerance)
const poLaws = [po.law('every line: received <= ordered + tolerance', ({Received, Ordered, slack}) => forall(l => Received.at(l).atMost(Ordered.at(l).plus(slack))))]
const poPerDelivery = purchasing(({line, qty, slack, Ordered}) => qty.atMost(Ordered.at(line).plus(slack)), withinTolerance)
const poCancelsReceived = purchasing(withinTolerance, () => yes)

// Recall decisions: a recall covers lots made between `from` and `to` by contract or imported sources. A unit whose lot
// date or source is unknown is treated as covered (fail closed); a passed retest clears a covered unit only when the
// recall's severity (0..3) is below 2.
const recall = rule('recall').params({from: nat, to: nat}).inputs({made: maybe(nat), source: maybe(oneOf('in_house', 'contract', 'imported')), retested: bool, severity: upTo(3)})
type RecallEnv = {from: Term, to: Term, made: Maybe<Term>, source: Maybe<Choice<'in_house' | 'contract' | 'imported'>>, retested: Bool, severity: Term}
const covered = (e: RecallEnv, unknownLot: Cond) => all(
  e.made.match({none: () => unknownLot, some: d => all(d.atLeast(e.from), d.atMost(e.to))}),
  e.source.match({none: () => yes, some: s => s.match({in_house: () => no, contract: () => yes, imported: () => yes})}),
)
const pull = (e: RecallEnv, unknownLot: Cond = yes) => all(covered(e, unknownLot), e.retested.not().or(e.severity.atLeast(2)))
const recallDecisions = [
  recall.decide('an unknown unit is pulled in a severe recall', e => [e.made.isNone, e.source.isNone, e.severity.atLeast(2)], e => pull(e)),
  recall.decide('a known lot made before the window stays', e => e.made.match({none: () => no, some: d => d.lt(e.from)}), e => pull(e).not()),
  recall.decide('in-house lots stay', e => e.source.match({none: () => no, some: s => s.is('in_house')}), e => pull(e).not()),
  recall.decide('severity 3 overrides a passed retest', e => [covered(e, yes), e.severity.atLeast(3)], e => pull(e)),
]
const recallFailsOpen = recall.decide('an unknown unit is pulled in a severe recall (lookup fails open)', e => [e.made.isNone, e.source.isNone, e.severity.atLeast(2)], e => pull(e, no))
const recallRetestClears = recall.decide('a passed retest always clears', e => e.retested, e => pull(e).not())

// Machine maintenance: hours are metered as the machine runs (at most a shift per report); a run that takes it past the
// service interval locks it, a locked machine doesn't start, and a service resets both.
const maintenance = (respectsLock: boolean, locksOnNewHours: boolean) => rule('machine maintenance interval')
  .params({limit: nat, shift: nat})
  .inputs({op: oneOf('run', 'service'), hours: nat})
  .assume(({hours, shift}) => hours.atMost(shift))
  .state({since: 0, locked: 0})
  .flags(({op, locked}) => ({running: respectsLock ? op.is('run').and(locked.eq(0)) : op.is('run')}))
  .step(({op, hours, limit, since, locked, running}) => ({
    since: when(running, since.plus(hours), when(op.is('service'), 0, since)),
    locked: when(running.and((locksOnNewHours ? since.plus(hours) : since).gt(limit)), 1, when(op.is('service'), 0, locked)),
  }))
const machine = maintenance(true, true)
const maintenanceLaws = [
  machine.law('hours since service <= limit, or the machine is locked', ({since, limit, locked}) => since.atMost(limit).or(locked.eq(1))),
  machine.law('hours since service <= limit + one shift', ({since, limit, shift}) => since.atMost(limit.plus(shift))),
  machine.law('locked is a flag', ({locked}) => locked.atMost(1)),
]
const machineIgnoresLock = maintenance(false, true)
const machineLocksLate = maintenance(true, false)

// A pick wave drains the order backlog: each turn picks at least one item of the open order, or, when it's done,
// closes it and opens the next (of any size). The rank is the tuple (orders, items): opening an order drops the first
// part however large the next order is, and picking drops the second.
const wave = (minimumPick: boolean, tupleRank: boolean) => {
  const base = loop('pick wave')
    .params({backlog: nat})
    .inputs({pick: nat, size: nat})
    .state({orders: ({backlog}) => backlog, items: 0, shipped: 0, opened: 0})
    .while(({orders, items}) => orders.gt(0).or(items.gt(0)))
    .body(({orders, items, shipped, opened, pick, size}) => ({
      items: when(items.gt(0), items.minus(pick), size),
      orders: when(items.gt(0), orders, orders.minus(1)),
      shipped: when(items.gt(0), shipped.plus(min(items, pick)), shipped),
      opened: when(items.gt(0), opened, opened.plus(size)),
    }))
    .rank(({orders, items}) => (tupleRank ? [orders, items] : orders))
  return minimumPick ? base.assume(({pick}) => pick.atLeast(1)) : base
}
const pickWave = wave(true, true)
const waveLaws = [
  pickWave.law('shipped + open items <= items opened', ({shipped, items, opened}) => shipped.plus(items).atMost(opened)),
  pickWave.law('orders <= backlog', ({orders, backlog}) => orders.atMost(backlog)),
]
const waveNoMinimum = wave(false, true)
const waveOrdersOnly = wave(true, false)

export const domain: Domain = {
  domain: 'supply',
  about: 'picking, quality holds, bills of materials, cold chain, shipping caps, PO receiving, recalls, maintenance, pick waves',
  cases: [
    machineCase('warehouse picking', 'every SKU: the units picked for orders never pass the stock on hand', warehouse, pickLaws, [
      {name: 'picks against on hand', why: 'a pick is compared with the stock on hand, forgetting units already picked', rule: warehousePicksOnHand, laws: pickLaws},
      {name: 'writes off picked stock', why: 'a write-off takes stock already promised to a pick', rule: warehouseWritesOffPicked, laws: pickLaws},
    ]),
    machineCase('quality holds', 'no lot is ever both on hold and shipped', quality, holdLaws, [
      {name: 'ships a held lot', why: 'the shipment forgets to check the hold', rule: qualityShipsHeld, laws: holdLaws},
    ]),
    machineCase('batch production', 'every unit produced consumed its bill of materials, and nothing consumed was not received', factory, bomLaws, [
      {name: 'bill of materials typo', why: 'the build consumes 3 bolts per unit where the bill says 4', rule: factoryBomTypo, laws: bomLaws},
      {name: 'checks bolts only', why: 'a build checks the bolts on hand but not the panels', rule: factoryChecksBoltsOnly, laws: bomLaws},
    ]),
    machineCase('cold-chain excursions', 'the excursion minutes and door openings in any window ending at now stay within the allowance, read from the log', cold, coldLaws, [
      {name: 'off by one at the window edge', why: 'the window before a request drops the opening exactly span minutes back, which the window ending at now still counts', rule: coldEdge, laws: coldLawsOf(coldEdge)},
    ]),
    machineCase('cold-chain excursions, pruned', 'the same, the log dropping openings once they leave the window', coldPruned, coldLawsOf(coldPruned), [
      {name: 'pruned a minute early', why: 'openings are dropped one minute before they leave the window, so the next request undercounts', rule: coldPrunedEarly, laws: coldLawsOf(coldPrunedEarly)},
    ]),
    machineCase('shipping weight and volume caps', 'a container never passes its weight, volume or pallet positions', shipping, shippingLaws, [
      {name: 'checks weight only', why: 'light, bulky pallets are loaded past the volume', rule: shippingWeightOnly, laws: shippingLaws},
      {name: 'one pallet too many', why: 'the position check uses <= where it means <', rule: shippingOneTooMany, laws: shippingLaws},
    ]),
    machineCase('purchase-order receiving', 'every PO line: received never passes ordered plus the tolerance', po, poLaws, [
      {name: 'checks each delivery alone', why: 'a delivery is compared with the line, forgetting earlier deliveries', rule: poPerDelivery, laws: poLaws},
      {name: 'cancels received units', why: 'a cancellation takes the line below what already arrived', rule: poCancelsReceived, laws: poLaws},
    ]),
    decisionCase('recall', 'unknown lots fail closed, lots outside the recall stay, a severe recall overrides a retest', recallDecisions, [
      {name: 'lookup fails open', why: 'a unit with no lot date is treated as outside the window', decision: recallFailsOpen},
      {name: 'a retest always clears', why: 'a passed retest does not clear a recall of severity 2 or more', decision: recallRetestClears},
    ]),
    machineCase('machine maintenance interval', 'hours since service stay within the interval or the machine is locked, and never pass it by more than a shift', machine, maintenanceLaws, [
      {name: 'runs while locked', why: 'the start forgets the lock, so hours keep accruing past the interval', rule: machineIgnoresLock, laws: maintenanceLaws},
      {name: 'locks a run late', why: 'the lock looks at the hours before the run, so the run that crosses the limit leaves it unlocked', rule: machineLocksLate, laws: maintenanceLaws},
    ]),
    loopCase('pick wave', 'every turn picks or opens an order, so the wave ends (ranked by orders, then items), and nothing ships that was not opened', pickWave, waveLaws, [
      {name: 'no minimum pick', why: 'a turn that picks nothing leaves the rank where it was', loop: waveNoMinimum, laws: waveLaws},
      {name: 'ranked by orders alone', why: 'a pick leaves the order count where it was; only the tuple drops on every turn', loop: waveOrdersOnly, laws: waveLaws},
    ]),
  ],
}
