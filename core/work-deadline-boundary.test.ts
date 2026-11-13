import {expect, test} from 'bun:test'
import {BudgetExpired, WorkLedger} from './work-admission.ts'
import {workAmount, workAdd} from './work-amount.ts'
import {workKeys, type WorkKey} from './work-kinds.ts'

const fresh = () => new WorkLedger(Object.fromEntries(workKeys.map(key => [key, 1])) as Record<WorkKey, number>)
const stage = <T, F>(l: WorkLedger, room: number, run: () => T, no: () => F) =>
  l.withDeadlineRefusalBoundary(workAdd(l.actual(), workAmount(BigInt(room))), run, no)
const caught = (run: () => unknown): unknown => { try { run() } catch (e) { return e }; throw Error('expected refusal') }
const charge = (l: WorkLedger, n: number) => l.start('ticks', n, 'deadline test')

test('successful stage preserves its result, root, baseline and available work', () => {
  const l = fresh(), value = {proven: true, checked: true}
  l.withBudget(workAmount(100n), () => {
    const before = l.snapshot()
    expect(stage(l, 10, () => value, () => undefined)).toBe(value)
    const after = l.snapshot()
    expect(after.actual).toEqual(before.actual); expect(after.reserved).toEqual(before.reserved)
    expect(after.activeEndpoints).toEqual(before.activeEndpoints)
    expect(after.rootEpoch).toBe(before.rootEpoch); expect(after.rootBaseline).toEqual(before.rootBaseline)
    expect(l.available()).toEqual(workAmount(100n))
  })
})
test('owned deadline refuses just its stage and the next stage can use only remaining root work', () => {
  const l = fresh(); let fallback = 0
  l.withBudget(workAmount(12n), () => {
    expect(stage(l, 10, () => { charge(l, 8); charge(l, 3); return 'bad' }, () => { fallback++; return 'refused' })).toBe('refused')
    expect(l.actual()).toEqual(workAmount(8n)); expect(l.reserved()).toEqual(workAmount(0n))
    expect(stage(l, 3, () => { charge(l, 3); return 'next' }, () => 'bad')).toBe('next')
    expect(l.actual()).toEqual(workAmount(11n)); expect(l.available()).toEqual(workAmount(1n))
    expect(l.capacityRefusal(caught(() => charge(l, 2)))!.limiting.map(e => e.kind)).toEqual(['root'])
  })
  expect(fallback).toBe(1)
})
test('internally swallowed refusal cannot return success or poison an enclosing sticky guard', () => {
  const l = fresh()
  l.withBudget(workAmount(100n), () => {
    const result = l.withCapacityRefusalBoundary(() => {
      expect(stage(l, 5, () => l.withCapacityRefusalBoundary(() => {
        try { charge(l, 6) } catch {}
        return {proven: true, checked: true}
      }), () => undefined)).toBeUndefined()
      charge(l, 2)
      return 'continued'
    })
    expect(result).toBe('continued'); expect(l.actual()).toEqual(workAmount(2n))
  })
})
test('preexisting parent sticky error is not cleared by a later locally handled deadline', () => {
  const l = fresh(); let first: unknown
  const error = caught(() => l.withBudget(workAmount(100n), () => l.withCapacityRefusalBoundary(() => {
    first = caught(() => charge(l, 101))
    expect(stage(l, 5, () => charge(l, 6), () => 'local')).toBe('local')
    return 'must not escape'
  })))
  expect(error).toBe(first); expect(l.capacityRefusal(error)!.limiting[0]!.kind).toBe('root')
})
for (const kind of ['root', 'scope', 'work-cap', 'deadline'] as const) {
  test(`a tied ancestor ${kind} is propagated, never consumed by the inner stage`, () => {
    const l = fresh(); let fallback = false
    const error = caught(() => l.withEndpoint(kind, workAmount(5n), () => stage(l, 5, () => charge(l, 6), () => { fallback = true })))
    expect(error).toBeInstanceOf(BudgetExpired); expect(fallback).toBe(false)
    expect(l.capacityRefusal(error)!.limiting.map(e => e.kind)).toEqual([kind, 'deadline'])
  })
}
for (const kind of ['root', 'scope', 'work-cap'] as const) {
  test(`a tighter ${kind} is not a local deadline`, () => {
    const l = fresh(); let fallback = false
    const error = caught(() => l.withEndpoint(kind, workAmount(3n), () => stage(l, 5, () => charge(l, 4), () => { fallback = true })))
    expect(l.capacityRefusal(error)!.limiting.map(e => e.kind)).toEqual([kind]); expect(fallback).toBe(false)
  })
}
test('equal-end descendant deadline mirrors are consumed by their authenticated owner after unwind', () => {
  const l = fresh(); let seen: unknown
  l.withBudget(workAmount(100n), () => l.withCapacityRefusalBoundary(() => {
    expect(stage(l, 5, () => l.withEndpoint('deadline', workAmount(5n), () => {
      seen = caught(() => charge(l, 6)); throw seen
    }), () => 'local')).toBe('local')
    expect(l.capacityRefusal(seen)!.limiting.map(e => e.kind)).toEqual(['deadline', 'deadline'])
    charge(l, 1)
  }))
})
test('nested owned mirrors propagate to the outer owner, not the inner fallback', () => {
  const l = fresh(); let inner = 0, outer = 0
  l.withBudget(workAmount(100n), () => l.withCapacityRefusalBoundary(() => {
    stage(l, 5, () => stage(l, 5, () => charge(l, 6), () => { inner++ }), () => { outer++ })
    charge(l, 1)
  }))
  expect(inner).toBe(0); expect(outer).toBe(1)
})
test('nested shorter owned stages are independent and do not poison their parent', () => {
  const l = fresh(); let outer = 0
  l.withBudget(workAmount(100n), () => {
    expect(stage(l, 10, () => {
      expect(stage(l, 5, () => charge(l, 6), () => 'inner')).toBe('inner')
      charge(l, 7); return 'outer success'
    }, () => { outer++; return 'bad' })).toBe('outer success')
  })
  expect(outer).toBe(0)
})
for (const kind of ['scope', 'work-cap', 'deadline'] as const) {
  test(`a stricter unowned descendant ${kind} remains fatal`, () => {
    const l = fresh(); let fallback = false
    const error = caught(() => l.withBudget(workAmount(100n), () => stage(l, 10,
      () => l.withEndpoint(kind, workAmount(3n), () => charge(l, 4)), () => { fallback = true })))
    expect(l.capacityRefusal(error)!.limiting.map(e => e.kind)).toEqual([kind]); expect(fallback).toBe(false)
  })
}
for (const kind of ['scope', 'work-cap'] as const) {
  test(`a tied descendant ${kind} is fatal even beside the owned deadline`, () => {
    const l = fresh()
    const error = caught(() => l.withBudget(workAmount(100n), () => stage(l, 5,
      () => l.withEndpoint(kind, workAmount(5n), () => charge(l, 6)), () => 'bad')))
    expect(l.capacityRefusal(error)!.limiting.map(e => e.kind)).toEqual(['deadline', kind])
  })
}
test('entry refusal before the body is local, spends nothing, and never reuses its endpoint identity', () => {
  const l = fresh(); let body = false, beforeId = 0, nextId = 0
  l.withBudget(workAmount(100n), () => {
    charge(l, 8); beforeId = l.currentScope()!.id
    expect(l.withCapacityRefusalBoundary(() => l.withDeadlineRefusalBoundary(workAmount(5n), () => { body = true }, () => 'entry refused'))).toBe('entry refused')
    stage(l, 10, () => { nextId = l.currentScope()!.id }, () => undefined)
    expect(l.actual()).toEqual(workAmount(8n)); expect(l.reserved()).toEqual(workAmount(0n))
  })
  expect(body).toBe(false); expect(nextId).toBeGreaterThan(beforeId + 1)
})
test('first local stop cannot mask a later swallowed ROOT refusal, even with an inner first-error guard', () => {
  const l = fresh(); let rootError: unknown, fallback = false
  const error = caught(() => stage(l, 10, () => l.withCapacityRefusalBoundary(() => {
    try { charge(l, 11) } catch {}
    l.withBudget(workAmount(5n), () => { rootError = caught(() => charge(l, 6)) })
    return {proven: true, checked: true}
  }), () => { fallback = true }))
  expect(error).toBe(rootError); expect(l.capacityRefusal(error)!.limiting.map(e => e.kind)).toEqual(['root'])
  expect(fallback).toBe(false)
})
test('first local stop cannot mask a later swallowed ancestor-budget scope refusal', () => {
  const l = fresh(); let hard: unknown
  const error = caught(() => l.withBudget(workAmount(100n), () => stage(l, 10, () => {
    try { charge(l, 11) } catch {}
    l.withBudget(workAmount(5n), () => { hard = caught(() => charge(l, 6)) })
    return 'bad'
  }, () => 'also bad')))
  expect(error).toBe(hard); expect(l.capacityRefusal(error)!.limiting[0]!.kind).toBe('scope')
})
test('foreign, forged and ordinary errors are not local deadline refusals', () => {
  const l = fresh(), other = fresh(), foreign = caught(() => other.withBudget(workAmount(0n), () => charge(other, 1)))
  for (const error of [foreign, new BudgetExpired('forged'), new TypeError('native failure'), {phase: 'fake', limiting: [{kind: 'deadline'}]}]) {
    let fallback = false
    expect(caught(() => stage(l, 5, () => { throw error }, () => { fallback = true }))).toBe(error)
    expect(fallback).toBe(false)
  }
})
test('an authentic old local refusal cannot impersonate a new stage', () => {
  const l = fresh(); let old: unknown
  stage(l, 5, () => { old = caught(() => charge(l, 6)); throw old }, () => undefined)
  expect(caught(() => stage(l, 5, () => { throw old }, () => 'bad'))).toBe(old)
})
test('an ordinary error after a local refusal is not masked by its fallback', () => {
  const l = fresh(), fault = new TypeError('later fault')
  expect(caught(() => stage(l, 5, () => { try { charge(l, 6) } catch {}; throw fault }, () => 'bad'))).toBe(fault)
})
test('fallback executes after endpoint cleanup and cannot hide a new root refusal', () => {
  const l = fresh(); let active: string[] = []
  const error = caught(() => l.withBudget(workAmount(100n), () => stage(l, 5, () => charge(l, 6), () => {
    active = l.snapshot().activeEndpoints.map(e => e.kind); charge(l, 101)
  })))
  expect(active).toEqual(['root']); expect(l.capacityRefusal(error)!.limiting[0]!.kind).toBe('root')
})
test('asynchronous stage and fallback reject and leave no active endpoint or boundary', () => {
  const l = fresh()
  expect(() => stage(l, 5, () => Promise.resolve('bad'), () => undefined)).toThrow('must be synchronous')
  expect(() => stage(l, 5, () => charge(l, 6), () => Promise.resolve('bad'))).toThrow('must be synchronous')
  expect(l.snapshot().activeEndpoints).toEqual([]); expect(l.diagnosticCheckpoint().capacityBoundaries).toEqual([])
})
test('diagnostic copies cannot mutate a live deadline owner identity', () => {
  const l = fresh()
  expect(stage(l, 5, () => {
    const copy = l.diagnosticCheckpoint().capacityBoundaries[0]!
    ;(copy.deadline as {id: number}).id = -1
    charge(l, 6)
  }, () => 'still local')).toBe('still local')
})
