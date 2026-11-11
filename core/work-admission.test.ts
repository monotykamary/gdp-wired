import {expect, test} from 'bun:test'
import {type WorkAdmissionEvent, BudgetExpired, WorkLedger} from './work-admission.ts'
import {type WorkKey, workKeys} from './work-kinds.ts'
import {compareWork, workAdd, workAmount, workFromExact, workFromNumber, workShare} from './work-amount.ts'
const weights = (patch: Partial<Record<WorkKey, number>> = {}) => Object.fromEntries(workKeys.map(key => [key, patch[key] ?? 1])) as Record<WorkKey, number>
function assertPrefix(e: WorkAdmissionEvent): void {
  const f = workFromExact(e.actual), r = workFromExact(e.reserved)
  expect(f.num >= 0n && r.num >= 0n).toBe(true)
  for (const end of e.activeEndpoints) expect(compareWork(workAdd(f, r), workFromExact(end.end))).toBeLessThanOrEqual(0)
  let total = workAmount(0n)
  for (const key of workKeys) total = workAdd(total, workShare(workFromExact(e.weights[key]), BigInt(e.counters[key]), 1n))
  expect(compareWork(total, f)).toBe(0)
  if (e.activeEndpoints.length) expect(e.effectiveEnd).not.toBeNull()
}
test('all26 sinks obey small equal and smaller-child endpoints at every prefix', () => {
  for (const sink of workKeys) for (const cap of [workAmount(0n), workAmount(1n, 8n), workAmount(1n, 2n), workAmount(1n), workAmount(7n, 3n), workAmount(10n)]) for (const parent of [cap, workAdd(cap, workAmount(1000n))]) {
    const ledger = new WorkLedger(weights({[sink]: 0.125}))
    ledger.withTrace(assertPrefix, () => ledger.withBudget(parent, () => ledger.withBudget(cap, () => {
      try { ledger.withChunk(sink, 1000, lease => { for (let n = 0; n < lease.granted; n++) lease.start() }) }
      catch (error) { expect(error).toBeInstanceOf(BudgetExpired) }
    })))
    expect(compareWork(ledger.actual(), cap)).toBeLessThanOrEqual(0)
  }
})
test('an indivisible quantum that does not fit starts no work', () => {
  const ledger = new WorkLedger(weights({fm: 2.33})); let started = false
  ledger.withTrace(assertPrefix, () => ledger.withBudget(workAmount(1n), () => {
    expect(() => ledger.withChunk('fm', 1, lease => { lease.start(); started = true })).toThrow(BudgetExpired)
  }))
  expect(started).toBe(false); expect(ledger.counter('fm')).toBe(0n)
})
test('unused reservations release but started work survives success and failure', () => {
  const ledger = new WorkLedger(weights())
  ledger.withTrace(assertPrefix, () => ledger.withBudget(workAmount(10n), () => {
    ledger.withChunk('ticks', 10, lease => { lease.start(3) })
    expect(ledger.counter('ticks')).toBe(3n); expect(ledger.reserved().num).toBe(0n)
    expect(() => ledger.withChunk('tableCells', 7, lease => { lease.start(2); throw new Error('body failure') })).toThrow('body failure')
    expect(ledger.counter('tableCells')).toBe(2n); expect(ledger.reserved().num).toBe(0n)
  }))
  expect(compareWork(ledger.actual(), workAmount(5n))).toBe(0)
})
test('nested counter work invalidates foreign credit; old tokens never revive', () => {
  const ledger = new WorkLedger(weights())
  ledger.withTrace(assertPrefix, () => ledger.withBudget(workAmount(10n), () => {
    ledger.withChunk('ticks', 5, outer => {
      ledger.withChunk('fm', 1, inner => inner.start())
      expect(() => outer.start()).toThrow(BudgetExpired)
    })
    ledger.withChunk('ticks', 4, outer => {
      ledger.withBudget(workAmount(1n), () => ledger.withChunk('values', 1, inner => inner.start()))
      expect(() => outer.start()).toThrow(BudgetExpired)
    })
  }))
})
test('rational shares use exact current capacity without clock conversion', () => {
  const ledger = new WorkLedger(weights({ticks: 0.02}))
  ledger.withTrace(assertPrefix, () => ledger.withBudget(workAmount(1n), () => ledger.withShare(1n, 3n, () => {
    ledger.withChunk('ticks', 100, lease => { expect(lease.granted).toBe(16); lease.start(lease.granted) })
  })))
  expect(compareWork(ledger.actual(), workAmount(1n, 3n))).toBeLessThanOrEqual(0)
})
test('escaped, async and doubly consumed leases cannot spend', () => {
  const ledger = new WorkLedger(weights()); let escaped: (() => void) | undefined
  ledger.withBudget(workAmount(3n), () => {
    ledger.withChunk('ticks', 1, lease => { escaped = () => lease.start(); lease.start(); expect(() => lease.start()).toThrow(RangeError) })
    expect(() => escaped!()).toThrow(BudgetExpired)
    expect(() => ledger.withChunk('ticks', 1, () => Promise.resolve())).toThrow(TypeError)
  })
  expect(compareWork(ledger.actual(), workFromNumber(1))).toBe(0)
})

test('epoch exhaustion fails closed and cannot leak a root baseline or scope', () => {
  for (const field of ['rootEpoch','scopeEpoch','endpointSequence'] as const) {
    const ledger = new WorkLedger(weights())
    const internal = ledger as unknown as Record<typeof field, number>
    internal[field] = Number.MAX_SAFE_INTEGER
    let entered = false
    expect(() => ledger.withBudget(workAmount(10n), () => { entered = true })).toThrow(RangeError)
    expect(entered).toBe(false)
    expect(ledger.snapshot().rootBaseline).toBeNull()
    expect(ledger.snapshot().activeEndpoints).toHaveLength(0)
    expect(ledger.reserved().num).toBe(0n)
  }
  const ledger = new WorkLedger(weights())
  expect(() => ledger.withBudget(workAmount(10n), () => {
    (ledger as unknown as {scopeEpoch: number}).scopeEpoch = Number.MAX_SAFE_INTEGER
  })).toThrow(RangeError)
  expect(ledger.snapshot().rootBaseline).toBeNull()
  expect(ledger.snapshot().activeEndpoints).toHaveLength(0)
  expect(ledger.reserved().num).toBe(0n)
})

test('observer failures cannot retain dead leases or bounded scopes', () => {
  for (const kind of ['reserve', 'release', 'scope-enter', 'scope-exit'] as const) {
    const ledger = new WorkLedger(weights())
    expect(() => ledger.withTrace(event => { if (event.kind === kind) throw new Error('observer failure') },
      () => ledger.withBudget(workAmount(10n), () => ledger.withChunk('ticks', 4, lease => lease.start())))).toThrow('observer failure')
    expect(ledger.reserved().num).toBe(0n)
    expect(ledger.bounded()).toBe(false)
    expect(() => ledger.setUnscopedCounter('ticks', Number(ledger.counter('ticks')))).not.toThrow()
  }
})
