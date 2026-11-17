// Paired existing Rust u8 Budget fixture kernel proof timings; never source admission.
// Run once per phase in a fresh Bun process after the job overlays exactly four pinned files.
import {performance} from 'node:perf_hooks'
import {extractRust} from '../../core/extract-rs.ts'
import {buildLaw} from '../../core/laws.ts'
import {proveRule, proveSteps} from '../../core/dsl.ts'
import type {Law} from '../../core/machine.ts'
import type {StepLaw} from '../../kernel/kernel.ts'

const phase = process.argv[2]
const pair = process.argv[3]
if ((phase !== 'before' && phase !== 'after') || !pair) throw new Error('usage: bun budget-perf.ts before|after pair-id')
const fixture = new URL('../../core/rs/examples/limits', import.meta.url).pathname
const extraction = extractRust(fixture, {entry: 'Budget', methods: ['spend', 'lap', 'try_spend', 'mark'], failures: 'kept', check: {runs: 0, states: 0, probes: false}})
if (!extraction.ok || !extraction.rule) throw new Error('existing fixture extraction failed: ' + JSON.stringify(extraction.notes))
const specs = [
  {name: 'existing/u8-spent-bound', expr: 'spent <= limit'},
  {name: 'existing/u8-wrapping-lap', expr: 'old(laps) == 255 implies laps == 0', method: 'lap'},
  {name: 'existing/u8-failed-spend-rollback', expr: 'failed implies spent == old(spent)', method: 'spend'},
]
for (const spec of specs) {
  const built = buildLaw(extraction, spec)
  for (let sample = -1; sample < 20; sample++) {
    const start = performance.now()
    const verdict = built.kind === 'step'
      ? proveSteps(extraction.rule, extraction.invariants ?? [], [built.law as StepLaw], {search: false, watchdogMs: 10_000})
      : proveRule(extraction.rule, [...(extraction.invariants ?? []), built.law as Law], {search: false, watchdogMs: 10_000})
    const record = {pair, phase, name: spec.name, sample, wallMs: performance.now() - start,
      kernelProven: verdict.kernelProven ?? false, proven: verdict.proven, checked: verdict.checked,
      translation: verdict.translation ?? null, stuck: verdict.stuck ?? null}
    console.log(JSON.stringify(record))
    if (record.kernelProven !== true || record.translation !== 'unchecked' || record.proven !== false || record.checked !== false || record.stuck !== null)
      throw new Error('unexpected proof verdict: ' + JSON.stringify(record))
  }
}
