// Disposable-worker negative control: restore the old metadata-dropping replay,
// require the actual production-path regression to reject it, then restore source.
import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
const path = 'core/counts.ts', original = readFileSync(path, 'utf8')
const from = '({goal, decls}, j) => ({...built[j]!, goal, decls, gg: mcGoal(goal.hyps, decls, built[j]!.c)})'
const to = '({goal, decls}, j) => ({goal, decls, c: built[j]!.c, gg: mcGoal(goal.hyps, decls, built[j]!.c)})'
assert.equal(original.split(from).length, 2, 'exactly one replay reconstruction')
try {
  writeFileSync(path, original.replace(from, to))
  const result = spawnSync(process.execPath, ['test', 'core/count-ranges.test.ts', '--test-name-pattern', 'ordinary core replay'], {encoding: 'utf8', timeout: 30000})
  const text = result.stdout + result.stderr
  console.log(text)
  assert.equal(result.status, 1, 'metadata-dropping replay must fail the regression')
  assert.match(text, /readsRetained/, 'failure must identify dropped replay reads')
  console.log('CORE_REPLAY_NEGATIVE_CONTROL_OK')
} finally { writeFileSync(path, original) }
