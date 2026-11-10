import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
const file = process.argv[2] ?? 'pilot-input/f3-original-mldr-raw-pilot.log'
const strict = process.argv.includes('--strict-window'), timed = process.argv.includes('--require-timed-window')
const lines = readFileSync(file, 'utf8').split('\n')
const records = (tag: string): any[] => lines.filter(line => line.startsWith(tag + ' ')).map(line => JSON.parse(line.slice(tag.length + 1)))
const results = records('F3_SOLVER_RESULT'), comparison = records('F3_PILOT_COMPARISON')
assert.equal(results.length, 2); assert.equal(comparison.length, 1)
if (process.argv.includes('--canonical')) {
  assert.equal(comparison[0].patchSha256, 'f59720c766a68a2647cb150c6f3e0793363aa36804eb6bc3185430488f0eebe0')
  assert.equal(comparison[0].sourceUnchanged, true)
}
assert.equal(results[0].monitor, false); assert.equal(results[1].monitor, true)
assert.deepEqual(results[0].result, results[1].result); assert.deepEqual(results[0].raw, results[1].raw)
assert.equal(comparison[0].sameRawAndVerdict, true)
for (const result of results) for (const [key, total] of Object.entries(result.raw)) {
  const amounts = Object.values(result.phases).map((phase: any) => phase.raw[key])
  assert(amounts.every(n => Number.isSafeInteger(n) && n >= 0), key + ' nonnegative phase delta')
  assert.equal(amounts.reduce((sum, n) => sum + n, 0), total, key + ' phase reconciliation')
}
const warnings = records('F3_RAW_SILENCE')
const captured = warnings.filter(warning => warning.whileRunning && warning.stack?.some((frame: any) => frame.functionName))
const changed = records('F3_RAW_WINDOW_CHANGED')
if (timed) for (const window of [...warnings, ...changed]) {
  const timing = window.profileWindow
  assert.equal(timing?.valid, true, 'valid sample timestamps are required')
  assert.equal(timing.selection, 'timeDeltas')
  assert(Number.isInteger(timing.samplesInWindow) && timing.samplesInWindow >= 0)
  if (timing.samplesInWindow === 0) assert.equal(window.stack.length, 0)
  else {
    assert(timing.firstSampleUs >= timing.lowerBoundUs)
    assert(timing.lastSampleUs <= timing.profileEndUs && timing.lastSampleUs >= timing.firstSampleUs)
    assert(window.stack.length > 0)
  }
}
if (strict) {
  assert(warnings.every(warning => warning.stable === true && warning.whileRunning && warning.heartbeatBefore === warning.heartbeatAfter))
  assert(changed.every(window => window.stable === false && (!window.whileRunning || window.heartbeatBefore !== window.heartbeatAfter)))
  assert(warnings.length + changed.length <= 16, 'bounded diagnostic')
} else assert(captured.length > 0, 'no meaningful live-stack capture')
console.log('F3_RAW_PILOT_AUDIT ' + JSON.stringify({passed: true, source: comparison[0].source, runtime: results[0].runtime,
  sameRawAndVerdict: true, exclusivePhaseReconciliation: true, result: results[0].result, raw: results[0].raw,
  reportedWindows: warnings.length, changedWindows: changed.length, strictWindowChecks: strict, timedWindowChecks: timed, unattributedWindows: warnings.length - captured.length, liveStacks: captured.length, topFunctions: [...new Set(captured.map(warning => warning.stack[0]?.functionName))],
  warningLimit: strict ? 'bounded raw-progress pilot only; changed capture windows are not stable violations' : 'first pilot did not recheck heartbeat after profiler acknowledgement; captures are candidates, not final F3 proof',
  scope: 'Node raw-progress diagnostic only; no calibrated weights/W, no Bun F3, no full census'}))
