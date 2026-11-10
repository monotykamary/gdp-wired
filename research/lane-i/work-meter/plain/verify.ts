import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
const {restore, command} = await import(resolve('recovery-input/final-gate-common.ts'))
const text = readFileSync('plain-result/plain-work-clock-prototype.log', 'utf8')
function tagged(tag: string): any { const rows = text.split('\n').filter(line => line.startsWith(tag + ' ')); assert.equal(rows.length, 1, tag); return JSON.parse(rows[0]!.slice(tag.length + 1)) }
const source = tagged('PLAIN_CLOCK_SOURCE'), artifact = tagged('PLAIN_CLOCK_PATCH'), original = tagged('PLAIN_ORIGINAL_CONTROL')
const checks = text.split('\n').filter(line => line.startsWith('PLAIN_CLOCK_CHECK ')).map(line => JSON.parse(line.slice('PLAIN_CLOCK_CHECK '.length)))
assert.deepEqual(checks.map(row => row.label), ['dependencies','ordinary-clock-controls','type-lint'])
assert(checks.every(row => row.exit === 0 && row.signal === null && row.error === ''))
assert(/22 pass/.test(text)); assert(/0 fail/.test(text))
assert.equal(artifact.encoding, 'gzip-base64'); assert.equal(artifact.admitted, false)
const patch = gunzipSync(Buffer.from(artifact.data, 'base64'))
assert.equal(patch.byteLength, artifact.bytes)
assert.equal(createHash('sha256').update(patch).digest('hex'), artifact.patchSha256)
assert.equal(artifact.patchSha256, source.patchSha256)
assert.equal(source.parentTree, '1938f7d70a7ed5fb0369a0e76e2e0c2b5a113131')
assert.equal(source.parentPatch, 'f59720c766a68a2647cb150c6f3e0793363aa36804eb6bc3185430488f0eebe0')
const expectedFiles = ['core/bmc.ts','core/dsl.ts','core/kind.ts','core/tpa.ts','kernel/prove.ts']
assert.deepEqual([...source.changed].sort((a: string, b: string) => a.localeCompare(b)), expectedFiles)
const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
const temp = mkdtempSync('/tmp/lane-i-plain-roundtrip-'), root = join(temp, 'source')
try {
  restore(resolve('recovery-input'), root, config.integrationBase)
  command('git', ['apply', resolve('validation-input/candidate.patch')], root)
  command('git', ['add','-A'], root)
  assert.equal(command('git', ['write-tree'], root), source.parentTree)
  const path = join(temp, 'delta.patch'); writeFileSync(path, patch)
  command('git', ['apply','--check',path], root); command('git', ['apply',path], root)
  assert.deepEqual(command('git', ['diff','--name-only'], root).split('\n').sort(), expectedFiles)
  for (const [path, blob] of Object.entries(source.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object',path], root), blob, path)
  assert.equal(source.expectedCandidateBlobs['research/protocols/ic3syn/models.ts'], config.expectedCandidateBlobs['research/protocols/ic3syn/models.ts'])
  console.log('PLAIN_CLOCK_ARTIFACT_AUDIT ' + JSON.stringify({passed: true, parentSource: '41d39043', parentTree: source.parentTree, patchSha256: artifact.patchSha256, changed: expectedFiles, sourceFiles: Object.keys(source.expectedCandidateBlobs).length, tests: 22, originalConsensus: {result: original.result, preflightEvals: original.raw.evals, solverFm: original.raw.fm}, admitted: false, scope: 'artifact roundtrip only; consensus exercised preflight, not complete ordinary/EPR coverage; fixture weights are not calibration'}))
} finally { rmSync(temp, {recursive: true, force: true}) }
