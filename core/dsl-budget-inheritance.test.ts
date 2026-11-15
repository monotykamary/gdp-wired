import {expect, spyOn, test} from 'bun:test'
import {nat, proveRule, proveSteps, rule, type ProveOptions} from './dsl.ts'
import {BudgetExpired, workLedger, type WorkAdmissionSnapshot} from './work-admission.ts'
import {compareWork, workAmount, workFromExact, workSub} from './work-amount.ts'
import {completeWorkProfile} from './work-profile.ts'
import {clock, wallAt, withBudget} from '../kernel/prove.ts'

// The hook only observes the first native public-body entry and optionally
// admits a work quantum. The original method, proof and checker still run.
function probe(enter: () => void) {
  const r = rule('public budget fixture').inputs({n: nat}).state({x: 0}).step(({n}) => ({x: n}))
  const law = r.law('nonnegative', ({x}) => x.atLeast(0))
  const original = r.withSumsOf.bind(r)
  let entered = false
  const hook = spyOn(r, 'withSumsOf').mockImplementation((...xs) => {
    if (!entered) { entered = true; enter() }
    return original(...xs)
  })
  return {
    run: (opts: ProveOptions, steps = false) => {
      const out = steps ? proveSteps(r, [law], [], opts) : proveRule(r, [law], opts)
      expect(entered).toBe(true)
      return out
    },
    close: () => hook.mockRestore(),
  }
}
const available = (s: WorkAdmissionSnapshot) => workSub(workSub(workFromExact(s.effectiveEnd!), workFromExact(s.actual)), workFromExact(s.reserved))

if (completeWorkProfile.enabled) {
  for (const steps of [false, true]) test(`implicit ${steps ? 'proveSteps' : 'proveRule'} search:false inherits the root and can exceed 15M`, () => {
    let enclosing!: WorkAdmissionSnapshot
    const f = probe(() => {
      const entry = workLedger.snapshot()
      expect(entry.activeEndpoints).toEqual(enclosing.activeEndpoints)
      expect(available(entry)).toEqual(available(enclosing))
      expect(entry.rootEpoch).toBe(enclosing.rootEpoch)
      workLedger.start('ticks', 15_000_001)
    })
    try {
      withBudget(30_000_000, () => {
        enclosing = workLedger.snapshot()
        const out = f.run({search: false, from: 'any'}, steps)
        expect(out.proven).toBe(true); expect(out.checked).toBe(true)
        const after = workLedger.snapshot()
        expect(compareWork(workSub(workFromExact(after.actual), workFromExact(enclosing.actual)), workAmount(15_000_001n))).toBeGreaterThanOrEqual(0)
        expect(after.activeEndpoints).toEqual(enclosing.activeEndpoints)
        expect(after.reserved).toEqual(enclosing.reserved)
        expect(after.rootBaseline).toEqual(enclosing.rootBaseline)
      })
    } finally { f.close() }
  })

  test('implicit child propagates the enclosing refusal to its owner', () => {
    let enclosing!: WorkAdmissionSnapshot, childError: unknown, ownerError: unknown
    const f = probe(() => workLedger.start('ticks', 15_000_001))
    try {
      try {
        withBudget(10_000_000, () => {
          enclosing = workLedger.snapshot()
          try { f.run({search: false}) } catch (error) { childError = error; throw error }
        })
      } catch (error) { ownerError = error }
      expect(childError).toBeInstanceOf(BudgetExpired)
      expect(ownerError).toBe(childError)
      const refusal = workLedger.capacityRefusal(ownerError)
      expect(refusal?.limiting).toEqual(enclosing.activeEndpoints)
      expect(refusal?.reason).toBe('quantum')
      expect(workLedger.snapshot().activeEndpoints).toEqual([])
      expect(workLedger.snapshot().reserved).toEqual({numerator: '0', denominator: '1'})
    } finally { f.close() }
  })

  for (const [search, amount] of [[{work: 1000}, 1000], [{ms: 4}, 1000], [{work: 0}, 0], [{ms: 0}, 0]] as const) {
    test(`explicit ${JSON.stringify(search)} retains its own bounded scope and handler`, () => {
      let enclosing!: WorkAdmissionSnapshot
      const f = probe(() => {
        const entry = workLedger.snapshot()
        expect(entry.activeEndpoints.length).toBe(enclosing.activeEndpoints.length + 1)
        expect(entry.activeEndpoints.at(-1)?.kind).toBe('scope')
        expect(available(entry)).toEqual(workAmount(BigInt(amount)))
        workLedger.start('ticks', amount + 1)
      })
      try {
        withBudget(30_000_000, () => {
          enclosing = workLedger.snapshot()
          const out = f.run({search})
          expect(out.proven).toBe(false); expect(out.checked).toBe(false)
          expect(out.why).toContain('[limits=scope]')
          const after = workLedger.snapshot()
          expect(after.activeEndpoints).toEqual(enclosing.activeEndpoints)
          expect(after.actual).toEqual(enclosing.actual)
          expect(after.reserved).toEqual(enclosing.reserved)
          workLedger.start('ticks', 1)
        })
      } finally { f.close() }
    })
  }

  // Default auto-search may use 10s, beyond Bun's 5s test default.
  test('implicit search-enabled child preserves the normalized scheduling hint without a new ledger endpoint', () => {
    let enclosing!: WorkAdmissionSnapshot
    const f = probe(() => {
      expect(workLedger.snapshot().activeEndpoints).toEqual(enclosing.activeEndpoints)
      expect(wallAt() - clock()).toBeCloseTo(completeWorkProfile.defaultUnits / 250, 6)
    })
    try {
      withBudget(30_000_000, () => {
        enclosing = workLedger.snapshot()
        const out = f.run({search: true})
        expect(out.proven).toBe(true); expect(out.checked).toBe(true)
      })
    } finally { f.close() }
  }, 30_000)

  test('outermost implicit call still opens the original default budget', () => {
    expect(workLedger.inBudget()).toBe(false)
    const f = probe(() => {
      const entry = workLedger.snapshot()
      expect(entry.activeEndpoints.length).toBe(1)
      expect(entry.activeEndpoints[0]?.kind).toBe('root')
      expect(available(entry)).toEqual(workAmount(BigInt(completeWorkProfile.defaultUnits)))
    })
    try {
      const out = f.run({search: false})
      expect(out.proven).toBe(true); expect(out.checked).toBe(true)
      expect(workLedger.inBudget()).toBe(false)
    } finally { f.close() }
  })

  test('conflicting explicit zero budgets still fail validation before a child scope', () => {
    const f = probe(() => { throw new Error('validation must precede native body') })
    try {
      withBudget(30_000_000, () => {
        const before = workLedger.snapshot()
        expect(() => f.run({search: {work: 0, ms: 0}})).toThrow('choose a work budget or a legacy ms budget, not both')
        expect(workLedger.snapshot()).toEqual(before)
      })
    } finally { f.close() }
  })
} else {
  test('legacy outer default and explicit plain-path migration behavior are unchanged', () => {
    const f = probe(() => expect(workLedger.inBudget()).toBe(false))
    try {
      const out = f.run({search: false})
      expect(out.proven).toBe(true); expect(out.checked).toBe(true)
    } finally { f.close() }
    const r = rule('legacy explicit fixture').state({x: 0}).step(({x}) => ({x}))
    const out = proveRule(r, [r.law('zero', ({x}) => x.eq(0))], {search: {work: 1000}})
    expect(out.proven).toBe(false); expect(out.checked).toBe(false)
    expect(out.why).toBe('work mode: plain-path migration pending')
  })
}
