import {expect, test} from 'bun:test'
import {proveRule, rule} from './dsl.ts'
import {inferLaws} from './infer.ts'
import {withBudget, checkWorkEndpoint} from '../kernel/prove.ts'
import {checkWatchdog, WatchdogExpired, withSearchWatchdog} from './search-watchdog.ts'

const pause = () => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 25)

test('explicit watchdog duration validation, immediate stop and scope restoration', () => {
  for (const ms of [-1, Infinity, -Infinity, NaN]) expect(() => withSearchWatchdog(ms, () => 1)).toThrow('finite and nonnegative')
  expect(() => withSearchWatchdog(0, () => { throw Error('must not enter') })).toThrow(WatchdogExpired)
  expect(() => checkWatchdog('restored after immediate stop')).not.toThrow()
  expect(() => withSearchWatchdog(1000, () => { throw Error('caller error') })).toThrow('caller error')
  expect(() => checkWatchdog('restored after caller error')).not.toThrow()
})

test('nested watchdogs shorten but cannot renew inherited real deadlines', () => {
  expect(() => withSearchWatchdog(1, () => withSearchWatchdog(60000, () => { pause(); checkWatchdog('inherited short deadline') }))).toThrow(WatchdogExpired)
  withSearchWatchdog(1000, () => {
    expect(() => withSearchWatchdog(0, () => 1)).toThrow(WatchdogExpired)
    expect(() => checkWatchdog('outer deadline restored')).not.toThrow()
  })
  expect(() => checkWatchdog('no deadline left')).not.toThrow()
})

test('work-only pauses do not create watchdogs; explicit work plus watchdog stays distinct', () => {
  withBudget(1000000, () => { pause(); expect(() => checkWorkEndpoint('work-only pause')).not.toThrow() })
  expect(() => withBudget(1000000, () => withSearchWatchdog(1, () => { pause(); checkWorkEndpoint('work with real watchdog') }))).toThrow(WatchdogExpired)
  const r = rule('watchdog control').state({value: 0}).step(({value}) => ({value: value.plus(1)}))
  const law = r.law('nonnegative', ({value}) => value.atLeast(0))
  const v = proveRule(r, [law], {search: {work: 1000000}, watchdogMs: 0})
  expect(v).toMatchObject({proven: false, checked: false, stopped: true, termination: {kind: 'wall-deadline', phase: 'search preflight'}})
  const standalone = inferLaws(r, [law], [], {watchdogMs: 0})
  expect(standalone).toMatchObject({proven: false, checked: false, stopped: true, termination: {kind: 'wall-deadline'}})
  for (const watchdogMs of [-1, NaN, Infinity]) {
    expect(() => proveRule(r, [law], {watchdogMs})).toThrow('finite and nonnegative')
    expect(() => inferLaws(r, [law], [], {watchdogMs})).toThrow('finite and nonnegative')
  }
  expect(() => checkWatchdog('restored public scopes')).not.toThrow()
})
