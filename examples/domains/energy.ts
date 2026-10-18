// Energy and grids: a home battery, the inverter's rating per step, export caps over a window, demand response, feeder
// metering, EV charging sessions, interconnection approvals, a battery drawn down to its reserve.
import {type Bool, type Maybe, type Term, all, bool, forall, loop, max, maybe, min, nat, no, oneOf, relation, rule, when} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// A home battery: charging adds at most the inverter rating and never past the capacity; discharging takes at most the
// rating and never below the reserve. Energy in and out balance: soc + out = in (as naturals, no signed balance).
const battery = (bug?: 'unrated charge' | 'checks before charging') => rule('home battery')
  .params({capacity: nat, reserve: nat, rating: nat})
  .inputs({op: oneOf('charge', 'discharge'), kwh: nat})
  .state({soc: 0, charged: 0, discharged: 0})
  .flags(({op, kwh, soc, capacity, reserve, rating}) => {
    const amount = bug === 'unrated charge' ? kwh : min(kwh, rating)
    return {
      charges: op.is('charge').and(bug === 'checks before charging' ? soc.atMost(capacity) : soc.plus(amount).atMost(capacity)),
      discharges: op.is('discharge').and(reserve.plus(min(kwh, rating)).atMost(soc)),
    }
  })
  .step(({kwh, rating, soc, charged, discharged, charges, discharges}) => {
    const amount = bug === 'unrated charge' ? kwh : min(kwh, rating), out = min(kwh, rating)
    return {
      soc: when(charges, soc.plus(amount), when(discharges, soc.minus(out), soc)),
      charged: when(charges, charged.plus(amount), charged),
      discharged: when(discharges, discharged.plus(out), discharged),
    }
  })
const batteryLaws = (r: ReturnType<typeof battery>) => [
  r.law('soc <= capacity', ({soc, capacity}) => soc.atMost(capacity)),
  r.law('soc + discharged = charged', ({soc, discharged, charged}) => soc.plus(discharged).eq(charged)),
]
const batterySteps = (r: ReturnType<typeof battery>) => [
  r.stepLaw('a step moves the charge by at most the rating', ({soc, rating}, after) => after.soc.atMost(soc.plus(rating)).and(soc.atMost(after.soc.plus(rating)))),
  r.stepsLaw('two steps move it by at most twice the rating', 2, ({soc, rating}, after) => after.soc.atMost(soc.plus(rating).plus(rating)).and(soc.atMost(after.soc.plus(rating).plus(rating)))),
]
const batteryUnrated = battery('unrated charge'), batteryEarly = battery('checks before charging')

// Export caps over a window: the kWh exported within `window` before a request, plus the request, stay within the cap
// the grid operator allows; `exported` sums the exports in the window ending at now.
const exports = (opts: {pruned?: boolean, bug?: 'forgets the request'} = {}) => {
  const base = rule(opts.pruned ? 'grid export cap, pruned' : 'grid export cap')
    .params({window: nat, cap: nat, now: nat})
    .inputs({kwh: nat, t: nat})
    .log('kwh', 't')
    .sums({exported: (r, {now, window}) => when(r.t.atMost(now).and(now.lt(r.t.plus(window))), r.kwh, 0)})
    .queries({sent: (r, {t, window}) => when(t.lt(r.t.plus(window)), r.kwh, 0)})
    .flags(({sent, kwh, cap}) => ({ok: opts.bug ? sent.atMost(cap) : sent.plus(kwh).atMost(cap)}))
    .keep(({ok}) => ok)
    .relations(({t, now, exported, sent}) => [relation(exported.atMost(sent), t.atMost(now))])
  return opts.pruned ? base.prune('t', ({window}) => window) : base
}
const exportLaw = (r: ReturnType<typeof exports>) => r.law('exported in the window ending at now <= cap', ({exported, cap}) => exported.atMost(cap))
const exportsForget = exports({bug: 'forgets the request'})

// Demand response: the operator sheds load in blocks, never cutting below the critical load (hospitals, pumps);
// restoring brings blocks back. `load` is the connected load.
const demand = (bug?: 'forgets the block') => rule('demand response')
  .params({load: nat, critical: nat})
  .inputs({op: oneOf('shed', 'restore'), kw: nat})
  .pre(({load, critical}) => critical.atMost(load))
  .state({shed: 0})
  .flags(({op, kw, shed, load, critical}) => ({sheds: op.is('shed').and(bug ? critical.plus(shed).atMost(load) : critical.plus(shed).plus(kw).atMost(load))}))
  .step(({op, kw, shed, sheds}) => ({shed: when(sheds, shed.plus(kw), when(op.is('restore'), shed.minus(kw), shed))}))
const demandLaw = (r: ReturnType<typeof demand>) => r.law('the critical load is never shed', ({shed, critical, load}) => critical.plus(shed).atMost(load))
const demandForget = demand('forgets the block')

// Feeder metering: each reading adds to its meter and to the feeder's total, which the feeder's own meter records; no
// meter can read more than the feeder.
const feeder = (bug?: 'feeder clips the reading') => rule('feeder metering')
  .params({max: nat})
  .inputs({meter: nat, kwh: nat})
  .state({total: 0})
  .maps({Meter: 0})
  .step(({meter, kwh, max: top, total, Meter}) => ({Meter: Meter.bump(meter, all(), kwh), total: total.plus(bug ? min(kwh, top) : kwh)}))
const feederLaw = (r: ReturnType<typeof feeder>) => r.law('every meter <= the feeder total', ({Meter, total}) => forall(k => Meter.at(k).atMost(total)))
const feederClips = feeder('feeder clips the reading')

// EV charging sessions: a driver buys kWh, then the charger delivers in bursts, never past what was bought; a session
// that ends refunds what was not delivered.
const ev = (bug?: 'overshoots the last burst') => rule('EV charging session')
  .inputs({op: oneOf('buy', 'charge', 'end'), kwh: nat})
  .state({bought: 0, delivered: 0, refunded: 0})
  .flags(({op, kwh, bought, delivered}) => ({charges: op.is('charge').and(bug ? delivered.lt(bought) : delivered.plus(kwh).atMost(bought))}))
  .step(({op, kwh, bought, delivered, refunded, charges}) => ({
    bought: when(op.is('buy'), bought.plus(kwh), bought),
    delivered: when(charges, delivered.plus(kwh), delivered),
    refunded: when(op.is('end'), bought.minus(delivered), refunded),
  }))
const evLaws = (r: ReturnType<typeof ev>) => [r.law('delivered <= bought', ({delivered, bought}) => delivered.atMost(bought))]
const evOvershoot = ev('overshoots the last burst')

// Interconnection: a new solar array connects only with known feeder headroom covering it, and an export permit when it
// exports; storage-only sites need no permit. A missing headroom figure fails closed.
const intercon = rule('interconnection approval').inputs({kw: nat, headroom: maybe(nat), exports: bool, permit: maybe(bool)})
type InterEnv = {kw: Term, headroom: Maybe<Term>, exports: Bool, permit: Maybe<Bool>}
const fits = ({kw, headroom}: Pick<InterEnv, 'kw' | 'headroom'>) => headroom.match({none: () => no, some: h => kw.atMost(h)})
const permitted = ({permit}: Pick<InterEnv, 'permit'>) => permit.match({none: () => no, some: p => p})
const approve = (env: InterEnv) => fits(env).and(env.exports.not().or(permitted(env)))
const approveUnknownHeadroom = (env: InterEnv) => env.headroom.match({none: () => env.exports.not().or(permitted(env)), some: h => env.kw.atMost(h).and(env.exports.not().or(permitted(env)))})
const interDecisions = [
  intercon.decide('no headroom on file, no connection', ({headroom}) => headroom.isNone, env => approve(env).not()),
  intercon.decide('a connection fits the headroom', env => approve(env), env => fits(env)),
  intercon.decide('an exporting site has a permit', env => [approve(env), env.exports], env => permitted(env)),
]
const interUnknown = intercon.decide('no headroom on file, no connection', ({headroom}) => headroom.isNone, env => approveUnknownHeadroom(env).not())

// A battery drawn down to its reserve for a peak: each turn draws at least 1 kWh, never below the reserve.
const drawdown = (floor: number) => loop(floor ? 'peak drawdown' : 'peak drawdown, no minimum draw')
  .params({start: nat, reserve: nat})
  .inputs({draw: nat})
  .state({soc: ({start}) => start})
  .while(({soc, reserve}) => reserve.lt(soc))
  .body(({soc, reserve, draw}) => ({soc: soc.minus(min(soc.minus(reserve), max(draw, floor)))}))
  .rank(({soc}) => soc)
const drawdownLaws = (r: ReturnType<typeof drawdown>) => [r.law('soc <= start', ({soc, start}) => soc.atMost(start))]

export const domain: Domain = {
  domain: 'energy',
  about: 'home batteries, inverter ratings, export caps over a window, demand response, feeder metering, EV sessions, interconnection, peak drawdown',
  cases: [
    machineCase('home battery', 'the charge stays within capacity, energy in and out balance, and no step moves more than the rating', battery(), batteryLaws(battery()), [
      {name: 'unrated charge', why: 'a charge request is taken whole, past the inverter rating', rule: batteryUnrated, laws: batteryLaws(batteryUnrated), steps: batterySteps(batteryUnrated)},
      {name: 'checks before charging', why: 'the capacity check reads the charge before this charge is added', rule: batteryEarly, laws: batteryLaws(batteryEarly), steps: batterySteps(batteryEarly)},
    ], {steps: batterySteps(battery())}),
    machineCase('grid export cap', 'exports in any window stay within the operator\'s cap, read from the log', exports(), [exportLaw(exports())], [
      {name: 'forgets the request', why: 'the check reads the window so far without the export itself', rule: exportsForget, laws: [exportLaw(exportsForget)]},
    ]),
    machineCase('grid export cap, pruned', 'the same, the log dropping exports older than the window', exports({pruned: true}), [exportLaw(exports({pruned: true}))]),
    machineCase('demand response', 'load shedding never reaches the critical load', demand(), [demandLaw(demand())], [
      {name: 'forgets the block', why: 'the check reads the load already shed, not the block being shed', rule: demandForget, laws: [demandLaw(demandForget)]},
    ]),
    machineCase('feeder metering', 'no meter on a feeder reads more than the feeder', feeder(), [feederLaw(feeder())], [
      {name: 'feeder clips the reading', why: 'the feeder total caps each reading while the meter takes it whole', rule: feederClips, laws: [feederLaw(feederClips)]},
    ]),
    machineCase('EV charging session', 'a session never delivers more than was bought', ev(), evLaws(ev()), [
      {name: 'overshoots the last burst', why: 'a burst is allowed while anything is left, then delivered whole', rule: evOvershoot, laws: evLaws(evOvershoot)},
    ]),
    decisionCase('interconnection approval', 'missing headroom fails closed, connections fit, exporters hold a permit', interDecisions, [
      {name: 'unknown headroom read as room', why: 'a site with no headroom on file is approved on its permit alone', decision: interUnknown},
    ]),
    loopCase('peak drawdown', 'a draw of at least 1 kWh a turn reaches the reserve, the charge never rising', drawdown(1), drawdownLaws(drawdown(1)), [
      {name: 'no minimum draw', why: 'a turn may draw nothing, so the drawdown can stall above the reserve', loop: drawdown(0), laws: drawdownLaws(drawdown(0))},
    ]),
  ],
}
