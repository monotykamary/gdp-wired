import {expect, test} from 'bun:test'
import {countStageTrace, traceCountStage} from './count-stage-trace.ts'
test('stage observations distinguish assembly from native checks without accepting a proof', () => {
  const events: Record<string, unknown>[] = [], trace = countStageTrace(e => events.push(e), 'composition-total')
  trace.mark('merge', 'untrusted-assembly')
  trace.mark('native-step-check', 'trusted-check')
  trace.pause(); trace.finish(); trace.finish()
  expect(events.map(e => e.part)).toEqual(['merge', 'native-step-check', 'composition-total'])
  expect(events.map(e => e.role)).toEqual(['untrusted-assembly', 'trusted-check', undefined])
  expect(events.at(-1)!.aggregate).toBe(true)
  for (const event of events) for (const key of ['wallMs', 'units']) {
    expect(Number.isFinite(event[key])).toBe(true)
    expect(event[key] as number).toBeGreaterThanOrEqual(0)
  }
})
test('a measured stage returns or throws exactly its underlying computation', () => {
  const events: Record<string, unknown>[] = [], error = new Error('not a certificate')
  expect(traceCountStage(e => events.push(e), 'value', 'untrusted-search', () => 17)).toBe(17)
  expect(() => traceCountStage(e => events.push(e), 'failure', 'untrusted-assembly', () => {throw error})).toThrow(error)
  expect(events.map(e => e.part)).toEqual(['value', 'failure'])
  const trace = countStageTrace()
  trace.mark('unused', 'trusted-check'); trace.pause(); trace.finish()
  expect(traceCountStage(undefined, 'unused', 'trusted-check', () => false)).toBe(false)
})
