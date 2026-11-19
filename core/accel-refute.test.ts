import {describe, expect, test} from 'bun:test'
import {int, oneOf, proveRule, rule, when, checkAcceleratedRun} from './dsl.ts'
import {buildRepeatGoals} from './accel-refute.ts'
import {arithmetic, type Machine, less, n, x} from './machine.ts'
import {check} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'
import {partialAggregationInvariants, partialAggregationRule} from '../research/langs/jvm/rules/PartialAggregation.ts'

describe('checked accelerated refutation', () => {
  test('PartialAggregation #5 is REFUTED (accelerated) at k = 2^31, never concrete run', () => {
    const law = partialAggregationRule.law(
      'slow failed calls never outnumber slow calls',
      s => s.numberOfSlowFailedCalls.atMost(s.numberOfSlowCalls),
    )
    const v = proveRule(partialAggregationRule, [...partialAggregationInvariants, law], {search: {ms: 15_000}})
    expect(v.proven).toBe(false)
    expect(v.checked).toBe(false)
    expect(v.run).toBeUndefined()
    expect(v.acceleratedRun).toBeDefined()
    expect(v.acceleratedRun!.checked).toBe(true)
    expect(v.acceleratedRun!.totalSteps).toBe(2 ** 31)
    expect(v.acceleratedRun!.law).toBe(law.name)
    expect(checkAcceleratedRun(partialAggregationRule.machine, [...partialAggregationInvariants, law], v.acceleratedRun!)).toBe(true)
  })

  test('mutant where int32 saturates instead of wrapping is NOT refuted', () => {
    const satRule = rule('PartialAggregationSaturating')
      .params({epochSecond0: int})
      .inputs({method: oneOf('record', 'reset'), record_outcome: oneOf('SUCCESS', 'ERROR', 'SLOW_SUCCESS', 'SLOW_ERROR'), reset_epochSecond: int})
      .state({numberOfSlowCalls: int.from(0), numberOfSlowFailedCalls: int.from(0), epochSecond: int.from(({epochSecond0}) => epochSecond0)})
      .step(({method, record_outcome, numberOfSlowCalls, numberOfSlowFailedCalls, epochSecond, reset_epochSecond}) => {
        const t1 = method.is('record')
        const t3 = record_outcome.is('SLOW_SUCCESS')
        const t4 = numberOfSlowCalls.plus(1)
        const t5 = when(t4.atLeast(2147483648), 2147483647, t4) // saturates! cannot wrap
        const t6 = record_outcome.is('SLOW_ERROR')
        const t7 = numberOfSlowFailedCalls.plus(1)
        return {
          numberOfSlowCalls: when(t1, when(t3, t5, when(t6, t5, numberOfSlowCalls)), 0),
          numberOfSlowFailedCalls: when(t1, when(t3, numberOfSlowFailedCalls, when(t6, when(t7.atLeast(2147483648), 2147483647, t7), numberOfSlowFailedCalls)), 0),
          epochSecond: when(t1, epochSecond, reset_epochSecond),
        }
      })
    const law = satRule.law('slow failed calls never outnumber slow calls', s => s.numberOfSlowFailedCalls.atMost(s.numberOfSlowCalls))
    const v = proveRule(satRule, [law], {search: {ms: 10_000}})
    expect(v.acceleratedRun).toBeUndefined()
    expect(v.run).toBeUndefined()
  }, 90_000)

  test('mutant where assume prevents wraparound is NOT refuted', () => {
    const bounded = rule('PartialAggregationBounded')
      .inputs({method: oneOf('record', 'reset'), record_outcome: oneOf('SUCCESS', 'ERROR', 'SLOW_SUCCESS', 'SLOW_ERROR')})
      .state({numberOfSlowCalls: int.from(0), numberOfSlowFailedCalls: int.from(0)})
      .assume(({method, numberOfSlowCalls}) => method.is('reset').or(numberOfSlowCalls.lt(2147483647)))
      .step(({method, record_outcome, numberOfSlowCalls, numberOfSlowFailedCalls}) => {
        const t1 = method.is('record'), t3 = record_outcome.is('SLOW_SUCCESS'), t6 = record_outcome.is('SLOW_ERROR')
        const t4 = numberOfSlowCalls.plus(1), t5 = when(t4.atLeast(2147483648), t4.minus(4294967296), t4)
        const t7 = numberOfSlowFailedCalls.plus(1), t8 = when(t7.atLeast(2147483648), t7.minus(4294967296), t7)
        return {
          numberOfSlowCalls: when(t1, when(t3, t5, when(t6, t5, numberOfSlowCalls)), 0),
          numberOfSlowFailedCalls: when(t1, when(t3, numberOfSlowFailedCalls, when(t6, t8, numberOfSlowFailedCalls)), 0),
        }
      })
    const law = bounded.law('slow failed calls never outnumber slow calls', s => s.numberOfSlowFailedCalls.atMost(s.numberOfSlowCalls))
    const v = proveRule(bounded, [law], {search: {ms: 10_000}})
    expect(v.acceleratedRun).toBeUndefined()
    expect(v.run).toBeUndefined()
    expect(v.proven && v.checked).toBe(true)
  })

  test('tampered accelerated certificates are rejected by checkAcceleratedRun', () => {
    const law = partialAggregationRule.law(
      'slow failed calls never outnumber slow calls',
      s => s.numberOfSlowFailedCalls.atMost(s.numberOfSlowCalls),
    )
    const laws = [...partialAggregationInvariants, law]
    const v = proveRule(partialAggregationRule, laws, {search: {ms: 15_000}})
    const acc = v.acceleratedRun!
    expect(checkAcceleratedRun(partialAggregationRule.machine, laws, acc)).toBe(true)
    const rep = acc.segments[0]!
    if (rep.kind !== 'repeat') throw new Error('expected repeat segment')
    // Tamper count across wraparound boundary
    expect(checkAcceleratedRun(partialAggregationRule.machine, laws, {
      ...acc, totalSteps: acc.totalSteps + 1,
      segments: [{...rep, count: rep.count + 1}, ...acc.segments.slice(1)],
    })).toBe(false)
    // Tamper closedForm delta
    expect(checkAcceleratedRun(partialAggregationRule.machine, laws, {
      ...acc,
      segments: [{...rep, closedForm: {...rep.closedForm, numberOfSlowCalls: {base: 0, delta: 2}}}, ...acc.segments.slice(1)],
    })).toBe(false)
    // Tamper endState
    expect(checkAcceleratedRun(partialAggregationRule.machine, laws, {
      ...acc,
      segments: [{...rep, endState: {...rep.endState, numberOfSlowCalls: 0}}, ...acc.segments.slice(1)],
    })).toBe(false)
    // Tamper the tree, supplied goal, or displayed start-state / witness.
    for (const changed of [
      {...rep, stepTree: {leaf: []}},
      {...rep, allowGoal: {...rep.allowGoal, hyps: []}},
      {...rep, startState: {}},
    ]) {
      expect(checkAcceleratedRun(partialAggregationRule.machine, laws, {
        ...acc, segments: [changed, ...acc.segments.slice(1)],
      })).toBe(false)
    }
    expect(checkAcceleratedRun(partialAggregationRule.machine, laws, {...acc, witness: {}})).toBe(false)
    // The inferred premises must come from the actual built-ins, not arbitrary
    // functions or facts that use one of their reserved-looking names.
    const machine = partialAggregationRule.machine
    const f = Object.keys(machine.fns!)[0]!
    expect(checkAcceleratedRun({...machine, fns: {...machine.fns, [f]: {...machine.fns![f]!, js: 'x => 0'}}}, laws, acc)).toBe(false)
    const [fact, ...facts] = machine.facts!
    expect(checkAcceleratedRun({...machine, facts: [{...fact!, holds: {op: '<', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}}, ...facts]}, laws, acc)).toBe(false)
  })

  test('repeat admission rejects impossible arithmetic facts and serialization hooks', () => {
    const ticks = x('ticks'), count = 2, jVar = 'j', closedForm = {ticks: {base: 0, delta: 1}}
    const m: Machine = {name: 'two ticks', params: [], inputs: [], state: {ticks: n(0)},
      step: {state: {ticks: {op: 'add', a: ticks, b: n(1)}}}}
    const law = {name: 'stays below two', holds: less(ticks, n(count))}, goals = buildRepeatGoals(m, {}, {}, count, closedForm, jVar)
    const allow = grow(goals.allowGoal), step = grow(goals.stepGoal)
    if (!('tree' in allow) || !('tree' in step)) throw new Error('expected the ordinary repeat trees')
    const endState = {ticks: count}
    const packet = {checked: true, params: {}, totalSteps: count, law: law.name, finalState: endState, witness: {ticks: count - 1},
      segments: [{kind: 'repeat' as const, checked: true, request: {}, count, jVar, closedForm, startState: {ticks: 0}, endState,
        ...goals, allowTree: allow.tree, stepTree: step.tree}]}
    expect(checkAcceleratedRun(m, [law], packet)).toBe(true)
    expect(checkAcceleratedRun({...m, ...arithmetic([0])}, [law], packet)).toBe(false)
    const facts = Object.assign([{name: 'no start', holds: less(n(0), n(0))}], {toJSON: () => []})
    expect(checkAcceleratedRun({...m, facts}, [law], packet)).toBe(false)
  })

  test('a mathematical repeat is refused if a skipped step overflows the interpreter', () => {
    const pad = Number.MAX_SAFE_INTEGER - 20, ticks = x('ticks')
    const m: Machine = {
      name: 'exact-range', params: [], inputs: [], state: {ticks: n(0)},
      step: {state: {ticks: {op: 'sub', a: {op: 'add', a: ticks, b: n(pad)}, b: n(pad - 1)}}},
    }
    const count = 100, jVar = 'j', closedForm = {ticks: {base: 0, delta: 1}}
    const law = {name: 'stays below 100', holds: less(ticks, n(count))}
    const goals = buildRepeatGoals(m, {}, {}, count, closedForm, jVar)
    const allow = grow(goals.allowGoal, new Map(), {nodes: 0, until: clock() + 1000})
    const step = grow(goals.stepGoal, new Map(), {nodes: 0, until: clock() + 1000})
    if (!('tree' in allow) || !('tree' in step)) throw new Error('expected both goals to hold over the naturals')
    expect(check(goals.allowGoal, allow.tree)).toBe(true)
    expect(check(goals.stepGoal, step.tree)).toBe(true)
    const endState = {ticks: count}
    expect(checkAcceleratedRun(m, [law], {
      checked: true, params: {}, totalSteps: count, law: law.name, finalState: endState, witness: {ticks: count - 1},
      segments: [{kind: 'repeat', checked: true, request: {}, count, jVar, closedForm, startState: {ticks: 0}, endState,
        ...goals, allowTree: allow.tree, stepTree: step.tree}],
    })).toBe(false)
  })

  test('general uint16 wraparound counter (k = 65536) is REFUTED (accelerated)', () => {
    const u16 = rule('Uint16Counter')
      .inputs({op: oneOf('inc', 'reset')})
      .state({c: 0, seenHigh: 0})
      .step(({op, c, seenHigh}) => {
        const inc = op.is('inc')
        const next = when(c.plus(1).atLeast(65536), 0, c.plus(1))
        return {
          c: when(inc, next, 0),
          seenHigh: when(inc, when(c.atLeast(60000), 1, seenHigh), 0),
        }
      })
    const law = u16.law('once high, stays high until reset', ({c, seenHigh}) => seenHigh.eq(0).or(c.atLeast(60000)))
    const v = proveRule(u16, [law], {search: {ms: 10_000}})
    expect(v.run).toBeUndefined()
    expect(v.acceleratedRun?.checked).toBe(true)
    expect(v.acceleratedRun!.totalSteps).toBe(65536)
    expect(checkAcceleratedRun(u16.machine, [law], v.acceleratedRun!)).toBe(true)
  })

  test('general countdown with flags and concrete prefix is REFUTED (accelerated)', () => {
    const cd = rule('FlaggedCountdown')
      .inputs({op: oneOf('arm', 'tick')})
      .state({armed: 0, ticks: 2_000_000, fired: 0})
      .flags(({op, armed}) => ({canTick: op.is('tick').and(armed.eq(1))}))
      .step(({op, armed, ticks, fired, canTick}) => ({
        armed: when(op.is('arm'), 1, armed),
        ticks: when(canTick, when(ticks.gt(0), ticks.minus(1), 0), ticks),
        fired: when(canTick.and(ticks.eq(0)), 1, fired),
      }))
    const law = cd.law('never fires', ({fired}) => fired.eq(0))
    const v = proveRule(cd, [law], {search: {ms: 10_000}})
    expect(v.run).toBeUndefined()
    expect(v.acceleratedRun?.checked).toBe(true)
    expect(v.acceleratedRun!.totalSteps).toBe(2_000_002) // 1 arm + 2,000,000 ticks + 1 fire
    expect(checkAcceleratedRun(cd.machine, [law], v.acceleratedRun!)).toBe(true)
  })
})
