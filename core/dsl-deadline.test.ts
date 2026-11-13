import {expect, test} from 'bun:test'
import {withStageAllowance, withStageDeadline, withStageWall} from './dsl-deadline.ts'
import {completeWorkProfile} from './work-profile.ts'
import {workLedger, BudgetExpired} from './work-admission.ts'
import {workAmount} from './work-amount.ts'
import {clock, withDeadline, withWall, withinDeadline} from '../kernel/prove.ts'
import {checkGoalLemmas, type LemmaCut} from '../kernel/kernel.ts'
import {proveRule, rule, nat} from './dsl.ts'

if (completeWorkProfile.enabled) {
  test('full-profile helper consumes its own deadline but no root budget or reservation', () => {
    workLedger.withBudget(workAmount(1000n), () => {
      const before = workLedger.snapshot()
      expect(withStageDeadline(clock() + 1, () => workLedger.start('ticks', 251), () => 'local')).toBe('local')
      const after = workLedger.snapshot()
      expect(after.actual).toEqual(before.actual); expect(after.reserved).toEqual(before.reserved)
      expect(after.rootEpoch).toBe(before.rootEpoch); expect(after.rootBaseline).toEqual(before.rootBaseline)
      expect(after.activeEndpoints).toEqual(before.activeEndpoints)
    })
  })
  test('counted wall mirror uses the same owned deadline contract', () => {
    workLedger.withBudget(workAmount(1000n), () => {
      expect(withStageWall(clock() + 1, () => workLedger.start('ticks', 251), () => false)).toBe(false)
    })
  })
  test('the unchanged kernel cannot smuggle success out of an exhausted stage', () => {
    const goal = {name: 'native false', hyps: []}, lemmas: LemmaCut[] = [{when: [], cut: {x: 1}, tree: {leaf: []}}]
    workLedger.withBudget(workAmount(1000n), () => {
      const result = withStageDeadline(clock(), () => {
        checkGoalLemmas(goal, {leaf: []}, lemmas)
        return {proven: true, checked: true}
      }, () => ({proven: false, checked: false}))
      expect(result).toEqual({proven: false, checked: false})
    })
  })
  test('ordinary true and false rules retain native proof checking', () => {
    const r = rule('deadline fixture').inputs({n: nat}).state({x: 0}).step(({n}) => ({x: n}))
    const good = proveRule(r, [r.law('nonnegative', ({x}) => x.atLeast(0))], {search: {work: 1_000_000}})
    expect(good.proven).toBe(true); expect(good.checked).toBe(true)
    const bad = proveRule(r, [r.law('always zero', ({x}) => x.eq(0))], {search: {work: 1_000_000}})
    expect(bad.proven).toBe(false); expect(bad.checked).toBe(false)
  })
} else {
  test('legacy helper preserves identical callback result and ignores its refusal fallback', () => {
    const value = {proven: true, checked: true}; let fallback = false
    expect(withStageDeadline(clock(), () => value, () => { fallback = true })).toBe(withDeadline(clock(), () => value))
    expect(withStageWall(Infinity, () => value, () => { fallback = true })).toBe(withWall(Infinity, () => value))
    expect(fallback).toBe(false)
  })
  test('legacy implicit allowances add no deadline that was not there before', () => {
    const before = withinDeadline(Infinity)
    expect(withStageAllowance(1, () => withinDeadline(Infinity), () => -1)).toBe(before)
  })
  test('legacy helper does not newly catch BudgetExpired', () => {
    const error = new BudgetExpired('legacy external')
    let caught: unknown
    try { withStageDeadline(Infinity, () => { throw error }, () => 'bad') } catch (e) { caught = e }
    expect(caught).toBe(error)
  })
}
