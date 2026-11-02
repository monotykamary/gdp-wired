import {expect, test} from 'bun:test'
import {type RecallSide, scoreRecall} from './score.ts'
const side = (version: string, verdict: string): RecallSide => ({version, status: 'checked', result: {rules: [{ok: true, entry: 'Handler', laws: [{name: 'policy', expr: 'result implies admin', verdict, run: ['run'], replayed: 'original code agrees'}]}]}})
test('recall requires the same stated policy, original replay and fixed counterpart', () => {
  const a = side('vulnerable', 'broken'), b = side('fixed', 'proven')
  expect(scoreRecall([a,b]).found).toBe(true)
  expect(scoreRecall([a,side('fixed','unknown')]).found).toBe(true)
  expect(scoreRecall([a,side('fixed','broken')]).found).toBe(false)
  expect(scoreRecall([a]).found).toBe(false)
  b.result!.rules[0]!.laws[0]!.expr = 'another policy'
  expect(scoreRecall([a,b]).found).toBe(false)
})
test('deliberate training flaws require reproduction but no fictional fixed revision', () => {
  const a = side('vulnerable', 'broken')
  expect(scoreRecall([a], true).found).toBe(true)
  expect(scoreRecall([a]).found).toBe(false)
  a.result!.rules[0]!.ok = false
  expect(scoreRecall([a], true).found).toBe(false)
})

test('refusals, absent laws and un-replayed environment schedules never count', () => {
  const a = side('vulnerable', 'broken'), b = side('fixed', 'proven')
  a.result!.rules[0]!.ok = false
  expect(scoreRecall([a,b]).found).toBe(false)
  a.result!.rules[0]!.ok = true
  delete a.result!.rules[0]!.laws[0]!.replayed
  expect(scoreRecall([a,b]).found).toBe(false)
  a.result!.rules[0]!.laws = []
  expect(scoreRecall([a,b]).found).toBe(false)
})
