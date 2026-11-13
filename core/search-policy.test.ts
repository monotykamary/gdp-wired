import {expect, spyOn, test} from 'bun:test'
import {inProxySearch, projectedSearchWork, proxySearchState, withPlainSearchPolicy} from './search-policy.ts'
import {completeWorkProfile} from './work-profile.ts'
import {admittedWork, BudgetExpired, workLedger} from './work-admission.ts'
import {workAdd, workAmount} from './work-amount.ts'
import {work} from './solver.ts'
import {withStageAllowance, withStageDeadline, withStageWall} from './dsl-deadline.ts'
import {budgetEnd, clock, counted, fullWork, late, searchNow, searchWork, wallAt, withBudget, withDeadline, withSearchWork, withWall, withWork, withinDeadline} from '../kernel/prove.ts'

const rooted = <T>(run: () => T, units = 1_000_000n): T => workLedger.withBudget(workAmount(units), run)
if (completeWorkProfile.enabled) {
  test('proxy is only the declared twelve-counter projection; W still charges excluded work', () => rooted(() => {
    const before = workLedger.snapshot(), q = projectedSearchWork(), w = fullWork()
    withPlainSearchPolicy(false, () => {
      expect(inProxySearch()).toBe(true)
      expect(budgetEnd()).toBe(Infinity)
      workLedger.start('ticks', 100)
      expect(projectedSearchWork()).toBe(q)
      expect(searchWork()).toBe(q)
      expect(fullWork() - w).toBe(100)
      workLedger.start('plainRows', 2)
      expect(projectedSearchWork() - q).toBeCloseTo(15.86, 10)
      expect(clock()).toBeCloseTo(projectedSearchWork() / 250, 12)
    })
    expect(inProxySearch()).toBe(false)
    const after = workLedger.snapshot()
    expect(after.activeEndpoints).toEqual(before.activeEndpoints)
    expect(after.rootEpoch).toBe(before.rootEpoch)
    expect(after.reserved).toEqual(before.reserved)
  }))
  test('row/model rates and nested inheritance use separate proxy state', () => rooted(() => withPlainSearchPolicy(false, () => {
    const initial = work.n
    try {
      counted(40, () => {
        const t = clock()
        work.n += 80
        expect(clock() - t).toBe(2)
        counted(250, () => {
          expect(proxySearchState()?.rate).toBe(40)
          expect(proxySearchState()?.model).toBe(false)
        }, true)
      })
      expect(proxySearchState()?.rate).toBe(0)
      counted(250, () => {
        const t = clock()
        counted(40, () => {
          work.n += 80
          expect(clock()).toBe(t)
          expect(proxySearchState()?.model).toBe(true)
        })
        workLedger.start('plainRows', 10)
        expect(clock() - t).toBeCloseTo(79.3 / 250, 10)
      }, true)
    } finally { work.n = initial }
  })))
  test('all soft helpers poll without a ledger endpoint, refusal or fallback', () => rooted(() => {
    const before = workLedger.snapshot(), events: string[] = []
    workLedger.withTrace(e => { events.push(e.kind) }, () => withPlainSearchPolicy(false, () => {
      let fallback = false
      const stop = clock()
      const out = withStageDeadline(stop, () => {
        workLedger.start('fm', 1)
        expect(late(Infinity)).toBe(true)
        return 'unknown'
      }, () => { fallback = true; return 'fallback' })
      expect(out).toBe('unknown'); expect(fallback).toBe(false)
      expect(withStageAllowance(0, () => 'polled', () => 'fallback')).toBe('polled')
      withStageWall(clock(), () => { workLedger.start('fm', 1); expect(late(Infinity)).toBe(true) }, () => undefined)
      expect(workLedger.snapshot().activeEndpoints).toEqual(before.activeEndpoints)
    }))
    expect(events.includes('refuse')).toBe(false)
    expect(events.includes('scope-enter')).toBe(false)
  }))
  test('a soft cost cap polls the projection, never stops or discounts admission', () => rooted(() => withPlainSearchPolicy(false, () => {
    const end = searchWork() + 1, w = fullWork()
    withSearchWork(end, () => {
      workLedger.start('fm', 1)
      expect(late(Infinity)).toBe(true)
      expect(fullWork() - w).toBeCloseTo(2.33, 10)
    })
    expect(late(Infinity)).toBe(false)
  })))
  test('native explicit work caps still refuse inside a proxy scope', () => rooted(() => withPlainSearchPolicy(false, () => {
    const before = admittedWork()
    expect(() => withWork(workAdd(before, workAmount(1n)), () => workLedger.start('ticks', 2))).toThrow(BudgetExpired)
    expect(admittedWork()).toEqual(before)
  })))
  test('root refusal escapes a soft wrapper and cannot become its fallback', () => {
    let fallback = false
    expect(() => rooted(() => withPlainSearchPolicy(false, () =>
      withStageDeadline(Infinity, () => workLedger.start('ticks', 6), () => { fallback = true })), 5n)).toThrow(BudgetExpired)
    expect(fallback).toBe(false); expect(inProxySearch()).toBe(false)
  })
  test('a nested native quota changes no heuristic rate and remains a real quota', () => rooted(() => withPlainSearchPolicy(false, () => {
    expect(proxySearchState()?.rate).toBe(0)
    withBudget(workAmount(10n), () => {
      expect(proxySearchState()?.rate).toBe(0)
      expect(budgetEnd()).toBe(Infinity)
      workLedger.start('ticks', 2)
    })
    expect(() => withBudget(workAmount(1n), () => workLedger.start('ticks', 2))).toThrow(BudgetExpired)
  })))
  test('native parent locks nested plain entries, without projection or soft semantics', () => rooted(() => withPlainSearchPolicy(true, () => {
    expect(inProxySearch()).toBe(false)
    expect(Number.isFinite(budgetEnd())).toBe(true)
    withPlainSearchPolicy(false, () => {
      expect(inProxySearch()).toBe(false)
      expect(searchWork()).toBe(fullWork())
      expect(clock()).toBeCloseTo(fullWork() / 250, 10)
    })
  })))
  test('native child suspends a proxy, restores it on throw and leaks no state', () => rooted(() => {
    const boom = new Error('fixture')
    withPlainSearchPolicy(false, () => {
      const outer = proxySearchState()
      expect(() => withPlainSearchPolicy(true, () => {
        expect(inProxySearch()).toBe(false)
        withPlainSearchPolicy(false, () => expect(inProxySearch()).toBe(false))
        throw boom
      })).toThrow(boom)
      expect(proxySearchState()).toBe(outer)
      expect(() => counted(40, () => withDeadline(clock() + 2, () => { throw boom }))).toThrow(boom)
      expect(proxySearchState()?.rate).toBe(0)
      expect(withinDeadline(Infinity)).toBe(Infinity)
    })
    expect(inProxySearch()).toBe(false)
  }))
  test('proxy primitives do not read wall time for control', () => rooted(() => withPlainSearchPolicy(false, () => {
    const p = spyOn(performance, 'now').mockImplementation(() => { throw new Error('wall clock read') })
    const d = spyOn(Date, 'now').mockImplementation(() => { throw new Error('epoch clock read') })
    try {
      const t = clock()
      expect(searchNow()).toBe(t)
      withWall(t + 1, () => {
        expect(wallAt()).toBe(t + 1)
        withDeadline(t + 2, () => expect(late(t + 3)).toBe(false))
      })
    } finally { p.mockRestore(); d.mockRestore() }
  })))
  test('full accounting outside scope retains owned soft endpoints and exact admission', () => rooted(() => {
    expect(inProxySearch()).toBe(false)
    let fallback = false
    withStageDeadline(clock(), () => workLedger.start('ticks', 1), () => { fallback = true })
    expect(fallback).toBe(true)
    expect(searchWork()).toBe(fullWork())
  }))
} else {
  test('legacy mode never enters or changes proxy policy', () => {
    const before = clock(), value = {}
    expect(withPlainSearchPolicy(false, () => {
      expect(inProxySearch()).toBe(false); expect(proxySearchState()).toBeUndefined()
      return value
    })).toBe(value)
    expect(clock()).toBeGreaterThanOrEqual(before)
  })
}
