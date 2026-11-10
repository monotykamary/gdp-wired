import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {stripVTControlCharacters} from 'node:util'
const {restore, command} = await import(resolve('recovery-input/final-gate-common.ts'))
const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
assert.equal(config.composition.patchSha256, '2c98e5dc8d92da3b1f6833c1e1a331de24b559349c30cc44f52ec5c2a6c53ac2')
const temp = mkdtempSync('/tmp/lane-i-numeric-negative-'), root = join(temp, 'source')
try {
  restore(resolve('recovery-input'), root, config.integrationBase)
  command('git', ['apply', resolve('validation-input/candidate.patch')], root)
  for (const [path, blob] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  command('bun', ['install','--frozen-lockfile'], root, 180000)
  const fixture = 'core/work-finiteness.test.ts'
  writeFileSync(join(root, fixture), readFileSync('numeric-input/work-finiteness.test.source'))
  const result = spawnSync('bun', ['test', './' + fixture], {cwd: root, encoding: 'utf8', timeout: 60000, maxBuffer: 2 * 1024 * 1024})
  assert.equal(result.status, 1); assert.equal(result.signal, null); assert.equal(result.error, undefined)
  const plain = stripVTControlCharacters(result.stdout + '\n' + result.stderr)
  assert.equal(Number(plain.match(/(\d+) pass/)?.[1]), 2)
  assert.equal(Number(plain.match(/(\d+) fail/)?.[1]), 3)
  const failures = ['finite positive weights cannot admit an already infinite work score', 'a finite score plus a finite allowance cannot create an infinite budget end', 'nonfinite work at completion fails closed and restores the scope']
  for (const failure of failures) assert(plain.includes('(fail) ' + failure), failure)
  console.log('NUMERIC_NEGATIVE_TRACE\n' + plain)
  for (const [path, blob] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  const sha = (text: string) => createHash('sha256').update(text).digest('hex')
  console.log('NUMERIC_NEGATIVE_CONTROL ' + JSON.stringify({passed: true, baseline: '94b65671', patchSha256: config.composition.patchSha256, expectedFailures: failures, passingTests: 2, failingTests: 3, fixtureBlob: command('git', ['hash-object', fixture], root), oldSourceUnchanged: true, sourceFiles: Object.keys(config.expectedCandidateBlobs).length, stdoutSha256: sha(result.stdout), stderrSha256: sha(result.stderr), scope: 'same five regression tests against the unchanged broken source; failures are required controls'}))
} finally { rmSync(temp, {recursive: true, force: true}) }
