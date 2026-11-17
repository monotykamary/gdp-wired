// Existing Rust u8 fixture laws: kernel timing only, not a source-admission gate.
import {performance} from 'node:perf_hooks'
import {extractRust} from '../../core/extract-rs.ts'
import {buildLaw} from '../../core/laws.ts'
import {proveRule, proveSteps} from '../../core/dsl.ts'
import type {Law} from '../../core/machine.ts'
import type {StepLaw} from '../../kernel/kernel.ts'

const phase = process.argv[2]
if (phase !== 'before' && phase !== 'after') throw new Error('expected before or after phase')
const fixture = new URL('../../core/rs/examples/limits', import.meta.url).pathname
const extraction = extractRust(fixture, {entry: 'Budget', methods: ['spend', 'lap', 'try_spend', 'mark'], failures: 'kept', check: {runs: 0, states: 0, probes: false}})
if (!extraction.ok || !extraction.rule) throw new Error(`existing fixture extraction failed: ${JSON.stringify(extraction.notes)}`)
const r = extraction.rule
const specifications = [
  {name: 'existing/u8-spent-bound', expr: 'spent <= limit'},
  {name: 'existing/u8-wrapping-lap', expr: 'old(laps) == 255 implies laps == 0', method: 'lap'},
  {name: 'existing/u8-failed-spend-rollback', expr: 'failed implies spent == old(spent)', method: 'spend'},
]
for (const specification of specifications) {
  const built = buildLaw(extraction, specification)
  for (let repeat = 0; repeat < 4; repeat++) {
    const start = performance.now()
    const verdict = built.kind === 'step'
      ? proveSteps(r, extraction.invariants ?? [], [built.law as StepLaw], {search: false, watchdogMs: 10_000})
      : proveRule(r, [...(extraction.invariants ?? []), built.law as Law], {search: false, watchdogMs: 10_000})
    console.log(JSON.stringify({phase, scope: 'existing fixture kernel proof timing; source replay disabled', name: specification.name,
      pass: repeat ? repeat : 'warmup', wallMs: performance.now() - start, proven: verdict.proven, checked: verdict.checked,
      kernelProven: verdict.kernelProven ?? false, translation: verdict.translation ?? null, stuck: verdict.stuck ?? null}))
  }
}
