import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
function read(path: string, expectedPatch: string) {
  const text = readFileSync(path, 'utf8')
  const rows = (tag: string) => text.split('\n').filter(line => line.startsWith(tag + ' ')).map(line => JSON.parse(line.slice(tag.length + 1)))
  const comparisons = rows('F3_PILOT_COMPARISON'), results = rows('F3_SOLVER_RESULT')
  assert.equal(comparisons.length, 1); assert.equal(results.length, 2)
  assert.equal(comparisons[0].patchSha256, expectedPatch)
  assert.equal(comparisons[0].sourceUnchanged, true); assert.equal(comparisons[0].sameRawAndVerdict, true)
  assert.equal(results[0].monitor, false); assert.equal(results[1].monitor, true)
  return results
}
const parent = read('request-result/f3-request-mldr-pilot.log', '2c98e5dc8d92da3b1f6833c1e1a331de24b559349c30cc44f52ec5c2a6c53ac2')
const current = read(process.argv[2] ?? 'numeric-f3.log', '8df0cf2ac466465a45683a639124d5f774e1b85b72d7f36c1b42b682c4e46fbd')
for (let index = 0; index < 2; index++) {
  const before = parent[index]!, after = current[index]!
  assert.equal(before.id, after.id)
  assert.deepEqual(before.result, after.result)
  assert.deepEqual(before.raw, after.raw)
  assert.deepEqual(Object.keys(before.phases).sort(), Object.keys(after.phases).sort())
  for (const key of Object.keys(before.phases)) assert.deepEqual(before.phases[key].raw, after.phases[key].raw, key)
}
console.log('F3_NUMERIC_SOURCE_EQUIVALENCE ' + JSON.stringify({passed: true, parent: '94b65671', current: '32a59b2a', observerModes: ['off', 'on'], sameRawAndVerdict: true, sameExclusivePhaseRaw: true, scope: 'one original-model normal-finite path only; no general IEEE-754 proof, calibrated W or complete F3/F4 qualification'}))
