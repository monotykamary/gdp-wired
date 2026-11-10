import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync, mkdirSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const {restore, command} = await import(resolve('recovery-input/final-gate-common.ts'))
const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
assert.equal(config.composition.patchSha256, '2c98e5dc8d92da3b1f6833c1e1a331de24b559349c30cc44f52ec5c2a6c53ac2')
const temp = mkdtempSync('/tmp/lane-i-numeric-probe-'), root = join(temp, 'source')
try {
  restore(resolve('recovery-input'), root, config.integrationBase)
  command('git', ['apply', resolve('validation-input/candidate.patch')], root)
  for (const [path, blob] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  command('bun', ['install','--frozen-lockfile'], root, 180000)
  mkdirSync(join(root, 'research/lane-i'), {recursive: true})
  writeFileSync(join(root, 'research/lane-i/work-finiteness-probe.ts'), readFileSync('numeric-input/work-finiteness.probe.source'))
  const result = spawnSync('bun', ['research/lane-i/work-finiteness-probe.ts'], {cwd: root, encoding: 'utf8', timeout: 45000, maxBuffer: 1024 * 1024})
  console.log(result.stdout); if (result.stderr) console.error(result.stderr)
  assert.equal(result.status, 0); assert.equal(result.signal, null); assert.equal(result.error, undefined)
  for (const [path, blob] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  console.log('FINITE_BUDGET_SOURCE_UNCHANGED ' + JSON.stringify({source: '94b65671', sourceFiles: Object.keys(config.expectedCandidateBlobs).length, sourceUnchanged: true}))
} finally { rmSync(temp, {recursive: true, force: true}) }
