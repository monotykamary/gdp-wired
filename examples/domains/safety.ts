// Safety controls and IoT: elevator doors and motion, an intersection's lights, a heater's clamped output, an emergency
// stop, a two-hand press, three-sensor fusion, a heartbeat watchdog and a motor's ramp-down.
import {type Term, all, bool, loop, max, min, nat, oneOf, rule, when} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// An elevator: the door opens only when the car is stopped, and the car moves only with the door shut. As naturals,
// "never open while moving" reads open + moving <= 1.
const elevator = (bug?: 'opens while moving' | 'moves with the door open') => rule('elevator door and motion')
  .inputs({op: oneOf('open', 'close', 'go', 'arrive')})
  .state({open: 0, moving: 0})
  .flags(({op, open, moving}) => ({
    opens: op.is('open').and(bug === 'opens while moving' ? open.eq(0) : moving.eq(0)),
    goes: op.is('go').and(bug === 'moves with the door open' ? moving.eq(0) : open.eq(0)),
  }))
  .step(({op, open, moving, opens, goes}) => ({
    open: when(opens, 1, when(op.is('close'), 0, open)),
    moving: when(goes, 1, when(op.is('arrive'), 0, moving)),
  }))
const elevatorLaws = (r: ReturnType<typeof elevator>) => [r.law('never open while moving', ({open, moving}) => open.plus(moving).atMost(1))]
const elevatorOpens = elevator('opens while moving'), elevatorMoves = elevator('moves with the door open')

// An intersection: a direction turns green only when the other is red and the all-red clearance has run `clearance`
// ticks; turning red restarts the clearance count.
const lights = (bug?: 'forgets the cross street') => rule('intersection lights')
  .params({clearance: nat})
  .inputs({op: oneOf('tick', 'nsGo', 'ewGo', 'stop')})
  .state({ns: 0, ew: 0, clear: 0})
  .flags(({op, ns, ew, clear, clearance}) => ({
    nsGoes: op.is('nsGo').and(bug === 'forgets the cross street' ? clear.atLeast(clearance) : all(ew.eq(0), clear.atLeast(clearance))),
    ewGoes: op.is('ewGo').and(ns.eq(0), clear.atLeast(clearance)),
  }))
  .step(({op, ns, ew, clear, nsGoes, ewGoes}) => ({
    ns: when(nsGoes, 1, when(op.is('stop'), 0, ns)),
    ew: when(ewGoes, 1, when(op.is('stop'), 0, ew)),
    clear: when(op.is('stop'), 0, when(op.is('tick'), clear.plus(1), clear)),
  }))
const lightsLaws = (r: ReturnType<typeof lights>) => [
  r.law('never green both ways', ({ns, ew}) => ns.plus(ew).atMost(1)),
  r.law('each light is red or green', ({ns, ew}) => ns.atMost(1).and(ew.atMost(1))),
]
const lightsCross = lights('forgets the cross street')

// A heater: the requested output is clamped into [lo, hi], so the element never runs outside its rating.
const heater = (bug?: 'no lower clamp') => rule('heater output clamp')
  .params({lo: nat, hi: nat})
  .pre(({lo, hi}) => lo.atMost(hi))
  .inputs({request: nat})
  .state({out: ({lo}) => lo})
  .step(({request, lo, hi}) => ({out: bug === 'no lower clamp' ? min(request, hi) : min(max(request, lo), hi)}))
const heaterLaws = (r: ReturnType<typeof heater>) => [r.law('lo <= output <= hi', ({out, lo, hi}) => lo.atMost(out).and(out.atMost(hi)))]
const heaterNoLow = heater('no lower clamp')

// An emergency stop: pressing it stops the machine and latches; only a reset with the key, on a stopped machine, clears
// it, and the machine starts only when it is clear.
const estop = (bug?: 'stop clears the latch') => rule('emergency stop')
  .inputs({op: oneOf('press', 'reset', 'start', 'stop'), key: bool})
  .state({engaged: 0, running: 0})
  .flags(({op, key, engaged, running}) => ({
    clears: op.is('reset').and(key, running.eq(0)).or(bug === 'stop clears the latch' ? op.is('stop') : op.is('stop').and(engaged.eq(0))),
    starts: op.is('start').and(engaged.eq(0)),
  }))
  .step(({op, engaged, running, clears, starts}) => ({
    engaged: when(op.is('press'), 1, when(clears, 0, engaged)),
    running: when(op.is('press').or(op.is('stop')), 0, when(starts, 1, running)),
  }))
const estopLaws = (r: ReturnType<typeof estop>) => [r.law('an engaged stop means not running', ({engaged, running}) => engaged.plus(running).atMost(1))]
const estopSteps = (r: ReturnType<typeof estop>) => [
  r.stepLaw('an engaged stop stays engaged without a keyed reset', ({engaged}, after) => engaged.atMost(after.engaged), ({op, key}) => op.is('reset').and(key).not()),
  r.stepsLaw('a press then a start leaves it stopped', 2, (_first, last) => last.running.eq(0), ({op}, j) => (j === 0 ? op.is('press') : op.is('start'))),
]
const estopStopClears = estop('stop clears the latch')

// A two-hand press: a run cycle needs both hands and the guard closed; setup mode jogs slowly with both hands.
const press = rule('two-hand press').params({maxJog: nat}).inputs({mode: oneOf('run', 'setup'), left: bool, right: bool, guard: bool, jog: nat})
type PressEnv = Parameters<Parameters<typeof press.decide>[1]>[0]
const cycles = (e: PressEnv, bug?: 'either hand') => e.mode.match({
  run: () => all(bug === 'either hand' ? e.left.or(e.right) : e.left.and(e.right), e.guard),
  setup: () => all(e.left, e.right, e.jog.atMost(e.maxJog)),
})
const pressDecisions = [
  press.decide('a run cycle needs both hands', e => [cycles(e) as never, e.mode.is('run')], e => e.left.and(e.right)),
  press.decide('a run cycle needs the guard closed', e => [cycles(e) as never, e.mode.is('run')], e => e.guard),
  press.decide('setup never jogs past the limit', e => [cycles(e) as never, e.mode.is('setup')], e => e.jog.atMost(e.maxJog)),
]
const pressEither = press.decide('a run cycle needs both hands (either hand accepted)', e => [cycles(e, 'either hand') as never, e.mode.is('run')], e => e.left.and(e.right))

// Three-sensor fusion: the reading used is the median, so one faulty sensor can't move it outside the other two.
const sensors = rule('three-sensor fusion').inputs({a: nat, b: nat, c: nat})
const median = (a: Term, b: Term, c: Term) => max(min(a, b), min(max(a, b), c))
const wrongMedian = (a: Term, b: Term, c: Term) => max(min(a, b), c)
const fusionDecisions = [
  sensors.decide('the fused reading is within the sensors', () => [], ({a, b, c}) => min(min(a, b), c).atMost(median(a, b, c)).and(median(a, b, c).atMost(max(max(a, b), c)))),
  sensors.decide('two sensors that agree win', ({a, b}) => a.eq(b), ({a, b, c}) => median(a, b, c).eq(a)),
  sensors.decide('one high outlier is ignored', ({a, b, c}) => [a.atMost(b), b.atMost(c)], ({a, b, c}) => median(a, b, c).eq(b)),
]
const fusionWrong = sensors.decide('two sensors that agree win (the third read last)', ({a, b}) => a.eq(b), ({a, b, c}) => wrongMedian(a, b, c).eq(a))

// A watchdog: each missed heartbeat counts; the miss that reaches `limit` puts the device in its safe state, a heartbeat
// clears the count, and the safe state is left only by a recovery with no misses pending.
const watchdog = (bug?: 'trips one miss late') => rule('heartbeat watchdog')
  .params({limit: nat})
  .pre(({limit}) => limit.atLeast(1))
  .inputs({op: oneOf('beat', 'miss', 'recover')})
  .state({missed: 0, safe: 0})
  .flags(({op, missed, limit}) => ({trips: op.is('miss').and(bug === 'trips one miss late' ? missed.plus(1).gt(limit) : missed.plus(1).atLeast(limit))}))
  .step(({op, missed, safe, trips}) => ({
    missed: when(op.is('miss'), missed.plus(1), when(op.is('beat'), 0, missed)),
    safe: when(trips, 1, when(op.is('recover').and(missed.eq(0)), 0, safe)),
  }))
const watchdogLaws = (r: ReturnType<typeof watchdog>) => [r.law('not safe means fewer misses than the limit', ({safe, missed, limit}) => safe.eq(0).implies(missed.lt(limit)))]
const watchdogSteps = (r: ReturnType<typeof watchdog>) => [
  r.stepLaw('the miss that reaches the limit makes it safe', (_before, after) => after.safe.eq(1), ({op, missed, limit}) => op.is('miss').and(missed.plus(1).atLeast(limit))),
]
const watchdogLate = watchdog('trips one miss late')

// A motor's ramp-down: the speed drops by at least one step each control tick until it stops.
const ramp = (bug?: 'zero steps') => {
  const base = loop(bug ? 'motor ramp-down, steps may be zero' : 'motor ramp-down')
    .params({speed0: nat})
    .inputs({dec: nat})
    .state({speed: ({speed0}) => speed0})
    .while(({speed}) => speed.gt(0))
    .body(({speed, dec}) => ({speed: speed.minus(min(speed, dec))}))
    .rank(({speed}) => speed)
  return bug ? base : base.assume(({dec}) => dec.atLeast(1))
}
const rampLaws = (l: ReturnType<typeof ramp>) => [l.law('speed <= the start speed', ({speed, speed0}) => speed.atMost(speed0))]

export const domain: Domain = {
  domain: 'safety and iot',
  about: 'elevator doors, intersection lights, heater clamp, emergency stop, two-hand press, sensor fusion, watchdog, motor ramp-down',
  cases: [
    machineCase('elevator door and motion', 'the door never opens while the car moves', elevator(), elevatorLaws(elevator()), [
      {name: 'opens while moving', why: 'the open command checks the door, not the motion', rule: elevatorOpens, laws: elevatorLaws(elevatorOpens)},
      {name: 'moves with the door open', why: 'the go command checks the motion, not the door', rule: elevatorMoves, laws: elevatorLaws(elevatorMoves)},
    ]),
    machineCase('intersection lights', 'never green both ways, and every green waits out the all-red clearance', lights(), lightsLaws(lights()), [
      {name: 'forgets the cross street', why: 'north-south turns green after the clearance without checking east-west is red', rule: lightsCross, laws: lightsLaws(lightsCross)},
    ]),
    machineCase('heater output clamp', 'the output stays within the element\'s rating', heater(), heaterLaws(heater()), [
      {name: 'no lower clamp', why: 'the clamp caps the request but lets it fall below the minimum', rule: heaterNoLow, laws: heaterLaws(heaterNoLow)},
    ]),
    machineCase('emergency stop', 'an engaged stop keeps the machine stopped and holds until a keyed reset', estop(), estopLaws(estop()), [
      {name: 'stop clears the latch', why: 'the ordinary stop button also clears an engaged emergency stop', rule: estopStopClears, laws: estopLaws(estopStopClears), steps: estopSteps(estopStopClears)},
    ], {steps: estopSteps(estop())}),
    decisionCase('two-hand press', 'a run cycle needs both hands and the guard, setup jogs within its limit', pressDecisions, [
      {name: 'either hand starts a cycle', why: 'the run check accepts one hand on the buttons', decision: pressEither},
    ]),
    decisionCase('three-sensor fusion', 'the median keeps one faulty sensor from moving the reading', fusionDecisions, [
      {name: 'third sensor read last', why: 'the fusion takes the larger of the first pair\'s low and the third, not the median', decision: fusionWrong},
    ]),
    machineCase('heartbeat watchdog', 'the miss that reaches the limit makes the device safe, and it stays safe until recovered', watchdog(), watchdogLaws(watchdog()), [
      {name: 'trips one miss late', why: 'the trip compares with > instead of >=, so the limit-th miss leaves it running', rule: watchdogLate, laws: watchdogLaws(watchdogLate), steps: watchdogSteps(watchdogLate)},
    ], {steps: watchdogSteps(watchdog())}),
    loopCase('motor ramp-down', 'the speed falls by at least a step each tick, so the motor stops', ramp(), rampLaws(ramp()), [
      {name: 'zero steps', why: 'a tick may decrease the speed by nothing, so the ramp need not end', loop: ramp('zero steps'), laws: rampLaws(ramp('zero steps'))},
    ]),
  ],
}
