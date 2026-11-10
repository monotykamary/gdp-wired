import {expect, test} from 'bun:test'
import {extract} from './extract.ts'
import {LawError, buildLaw} from './laws.ts'
import {proveRule, proveSteps} from './dsl.ts'
import {nativeCounterexample, sourceControls} from '../research/verify-all/source-crosscheck-cases.ts'

for (const c of sourceControls) test(`source cross-check historical regression: ${c.id} is refused by default`, () => {
  const witness = nativeCounterexample(c)
  expect(c.holds(witness.result, witness.args)).toBe(false)
  const x = extract(c.source, {file: `${c.id}.ts`, entry: c.entry, ...(c.standalone ? {mode: 'standalone' as const} : {})})
  if (!x.ok) { expect(x.refusals.length).toBeGreaterThan(0); return }
  let b: ReturnType<typeof buildLaw>
  try { b = buildLaw(x, {name: c.id, expr: c.expr, method: 'decide'}, {clock: 1, calendar: {}}) }
  catch (e) { expect(e).toBeInstanceOf(LawError); return }
  const v = b.kind === 'law' ? proveRule(x.rule!, [...x.invariants ?? [], b.law], {search: false}) : proveSteps(x.rule!, x.invariants ?? [], [b.law], {search: false})
  expect(v.proven && v.checked).toBe(false)
  if (v.kernelProven) expect(v.translation).toBe('error')
})
