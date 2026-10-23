// Bottleneck v2.19.5, its LocalDatastore: the reservoir, maxConcurrent and minTime bookkeeping every job goes through
// (Bottleneck.coffee:158-180 _drainOne calls __register__, :137 __free__). MIT, (c) Simon Grondin.
// https://github.com/SGrondin/bottleneck/tree/8a8bde9cde151c278397703c48f2bba4ded2bae7/src
//
// Mapping:
// - Requests are the datastore's calls: `register` a job of `weight` (__register__, LocalDatastore.coffee:107-116),
//   `free` it when done (__free__, :133-138), `heartbeat` (the setInterval body, :22-38), `incrementReservoir` (:88-92).
//   A free is for a job that registered (Job.coffee's done path): `.assume` weight <= running.
// - `now: nat` (ms from the datastore's construction, when `_nextRequest`, `_lastReservoirRefresh` and
//   `_lastReservoirIncrease` are Date.now(), :8) is sent in with each call (:104, :109, :23); Date.now() never goes back.
// - A setting that may be null is a flag beside its value (`hasMax`, `hasRefresh` for reservoirRefreshInterval and
//   reservoirRefreshAmount both set, `hasIncrease`, `hasMaximum`); the reservoir is state (`hasRes`, `res`): the
//   heartbeat sets it from null. CoffeeScript's `maximum - reservoir` and `reservoir += incr` read a null reservoir as 0,
//   which `res = 0` is.
// - Ghosts: `lastStart` (when the last registered job may start: now + wait, the `wait` :113 returns) and `started`.
import {bool, max, min, nat, oneOf, rule, when, yes} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'SGrondin/bottleneck', commit: '8a8bde9cde151c278397703c48f2bba4ded2bae7', licence: 'MIT', author: 'Simon Grondin', language: 'CoffeeScript'}

export const localDatastore = () => rule('bottleneck LocalDatastore')
  // Bottleneck.coffee:28-39 storeDefaults: maxConcurrent, minTime, reservoir, reservoirRefreshInterval/Amount,
  // reservoirIncreaseInterval/Amount/Maximum.
  .params({hasMax: bool, maxConcurrent: nat, minTime: nat, hasRes0: bool, res0: nat,
    hasRefresh: bool, refreshInterval: nat, refreshAmount: nat, hasIncrease: bool, increaseInterval: nat, increaseAmount: nat,
    hasMaximum: bool, increaseMaximum: nat})
  .inputs({op: oneOf('register', 'free', 'heartbeat', 'incrementReservoir'), weight: nat, now: nat})
  .state({running: 0, done: 0, hasRes: bool.from(({hasRes0}) => hasRes0), res: ({res0}) => res0, nextRequest: 0, lastRefresh: 0, lastIncrease: 0,
    clock: 0, lastStart: 0, started: bool.from(false)})
  .assume(({now, clock}) => now.atLeast(clock))
  .assume(({op, weight, running}) => op.is('free').implies(weight.atMost(running)))
  .flags(({op, weight, now, hasMax, maxConcurrent, running, hasRes, res, hasRefresh, refreshInterval, lastRefresh}) => ({
    // computeCapacity / conditionsCheck (:77-86): weight <= min(maxConcurrent - running, reservoir), either may be null.
    registers: op.is('register').and(hasMax.not().or(weight.atMost(maxConcurrent.minus(running))), hasRes.not().or(weight.atMost(res))),
    // :25-28 the refresh, when its interval has passed.
    refreshes: op.is('heartbeat').and(hasRefresh, now.atLeast(lastRefresh.plus(refreshInterval))),
  }))
  .flags(({op, now, hasIncrease, increaseInterval, lastIncrease}) => ({
    // :30-36 the increase, when its interval has passed.
    increases: op.is('heartbeat').and(hasIncrease, now.atLeast(lastIncrease.plus(increaseInterval))),
  }))
  .step(env => {
    const {op, weight, now, minTime, running, done, hasRes, res, nextRequest, lastRefresh, lastIncrease, lastStart, started,
      refreshAmount, increaseAmount, hasMaximum, increaseMaximum, registers, refreshes, increases} = env
    const free = op.is('free'), incRes = op.is('incrementReservoir')
    // After the refresh (:27 reservoir = reservoirRefreshAmount), the increase (:33 incr = min(amount, maximum -
    // reservoir) when a maximum is set; :34-35 applied only when positive).
    const r1 = when(refreshes, refreshAmount, res), incr = when(hasMaximum, min(increaseAmount, increaseMaximum.minus(r1)), increaseAmount)
    const bumps = increases.and(incr.gt(0))
    // :113-114 wait = max(nextRequest - now, 0); nextRequest = now + wait + minTime.
    const start = max(nextRequest, now)
    return {
      running: when(registers, running.plus(weight), when(free, running.minus(weight), running)),
      done: when(free, done.plus(weight), done),
      // :112 reservoir -= weight (when not null); :88-92 incrementReservoir adds (a null reservoir read as 0).
      res: when(registers.and(hasRes), res.minus(weight), when(incRes, res.plus(weight), when(bumps, r1.plus(incr), r1))),
      hasRes: when(refreshes.or(bumps, incRes), yes, hasRes),
      nextRequest: when(registers, start.plus(minTime), nextRequest),
      lastRefresh: when(refreshes, now, lastRefresh),
      lastIncrease: when(increases, now, lastIncrease),
      clock: now,
      lastStart: when(registers, start, lastStart),
      started: when(registers, yes, started),
    }
  })

// `weight` of an incrementReservoir call is its `incr` (:88).
const r = localDatastore()
const cite = (path: string, lines: string, exp: string) => ({...src, path, lines, export: exp})

export const items: RealItem[] = [{
  id: 'rate limit/bottleneck/LocalDatastore',
  domain: 'rate limit',
  source: cite('src/LocalDatastore.coffee', '16-138', 'LocalDatastore'),
  also: [cite('src/Bottleneck.coffee', '28-47, 130-180', 'Bottleneck (storeDefaults, _free, _drainOne)'), {...src, path: 'README.md', lines: '200-210', export: 'options', language: 'Markdown'}],
  summary: 'The job limiter\'s bookkeeping: a job registers only when its weight fits under maxConcurrent and the reservoir, which it spends; starts are spaced by minTime; a heartbeat refreshes the reservoir to an amount and increases it up to a maximum.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'the heartbeat is a setInterval (LocalDatastore.coffee:22-38) and the queue drains on promises (Bottleneck.coffee:158-205): the heartbeat is a request sent at any time, the queue (priorities, highWater, the BLOCK strategy of __submit__, :120-131) is not modelled'},
    {gap: 'scope', blocks: 'part', detail: 'updateSettings (:54-59) and a negative incrementReservoir (any number, :88) are left out; weights and settings are naturals'},
  ],
  laws: [
    invariant(r, r.law('no more weight runs at once than maxConcurrent', ({hasMax, running, maxConcurrent}) => hasMax.implies(running.atMost(maxConcurrent))),
      'safety', 'docs', 'README:200 maxConcurrent "How many jobs can be executing at the same time"'),
    stepLaw(r, r.stepLaw('a job registers only when the reservoir holds its weight',
      ({res, weight}, after) => after.res.plus(weight).eq(res),
      ({registers, hasRes}) => registers.and(hasRes)),
    'step', 'docs', 'README:205 reservoir "How many jobs can be executed before the limiter stops executing jobs. If reservoir reaches 0, no jobs will be executed"'),
    stepLaw(r, r.stepLaw('the heartbeat\'s increase never lifts the reservoir past reservoirIncreaseMaximum',
      ({res, refreshAmount, increaseMaximum, refreshes}, after) => after.res.atMost(max(increaseMaximum, when(refreshes, refreshAmount, res))),
      ({op, hasMaximum}) => op.is('heartbeat').and(hasMaximum)),
    'step', 'docs', 'README:210 reservoirIncreaseMaximum "The maximum value that reservoir can reach when reservoirIncreaseInterval is in use"'),
    stepLaw(r, r.stepLaw('two jobs start at least minTime apart',
      ({lastStart, minTime}, after) => after.lastStart.atLeast(lastStart.plus(minTime)),
      ({registers, started}) => registers.and(started)),
    'step', 'docs', 'README:201 minTime "How long to wait after launching a job before launching another one"'),
    leadsTo(r, r.leadsTo('a reservoir below its refresh amount is refreshed', {
      from: ({hasRefresh, res, refreshAmount}) => hasRefresh.and(res.lt(refreshAmount)),
      to: ({hasRes, res, refreshAmount}) => hasRes.and(res.atLeast(refreshAmount)),
      helpful: ({clock, lastRefresh, refreshInterval}) => ({op: 2, now: clock.plus(lastRefresh).plus(refreshInterval)}),
    }), 'docs', 'README:206 "Every reservoirRefreshInterval milliseconds, the reservoir value will be automatically updated to the value of reservoirRefreshAmount"'),
  ],
}]
