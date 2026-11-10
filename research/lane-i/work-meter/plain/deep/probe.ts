import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync, mkdirSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
const {restore, command} = await import(resolve('recovery-input/final-gate-common.ts'))
const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
assert.equal(config.composition.patchSha256, '8df0cf2ac466465a45683a639124d5f774e1b85b72d7f36c1b42b682c4e46fbd')
const text = readFileSync('plain-result/plain-numeric-parent-prototype.log', 'utf8')
const tagged = (tag: string) => { const lines = text.split('\n').filter(line => line.startsWith(tag + ' ')); assert.equal(lines.length, 1); return JSON.parse(lines[0]!.slice(tag.length + 1)) }
const source = tagged('PLAIN_CLOCK_SOURCE'), artifact = tagged('PLAIN_CLOCK_PATCH')
assert.equal(source.parentTree, '27b8a07cbd5500c7c7f7549df7d6f15fa41092ab')
assert.equal(source.parentPatch, config.composition.patchSha256)
assert.equal(artifact.patchSha256, '35344c91aa210e57de591bfd0250226aef04a713378cb7c5be865fa3a426a2e9')
const patch = gunzipSync(Buffer.from(artifact.data, 'base64'))
assert.equal(createHash('sha256').update(patch).digest('hex'), artifact.patchSha256)
const temp = mkdtempSync('/tmp/lane-i-plain-depth-'), root = join(temp, 'source')
try {
  restore(resolve('recovery-input'), root, config.integrationBase)
  command('git', ['apply', resolve('validation-input/candidate.patch')], root)
  for (const [path, blob] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  writeFileSync(join(temp, 'prototype.patch'), patch)
  command('git', ['apply', join(temp, 'prototype.patch')], root)
  for (const [path, blob] of Object.entries(source.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  command('bun', ['install','--frozen-lockfile'], root, 180000)
  mkdirSync(join(root, 'research/lane-i'), {recursive: true})
  writeFileSync(join(root, 'research/lane-i/ordinary-depth.ts'), readFileSync('deep-input/control.source'))
  const cases: any[] = []
  for (const work of [500000, 5000000, 15000000]) {
    const child = spawnSync('bun', ['research/lane-i/ordinary-depth.ts', 'consensus', String(work)], {cwd: root, encoding: 'utf8', timeout: 300000, maxBuffer: 4 * 1024 * 1024})
    console.log('PLAIN_DEEP_PROCESS ' + JSON.stringify({allowance: work, exit: child.status, signal: child.signal, error: String(child.error ?? '')}))
    console.log(child.stdout); if (child.stderr) console.error(child.stderr)
    assert.equal(child.status, 0, 'external guard or forbidden control read is not an unknown proof result')
    assert.equal(child.signal, null)
    const rows = child.stdout.split('\n').filter(line => line.startsWith('PLAIN_DEEP_CASE '))
    assert.equal(rows.length, 1)
    const row = JSON.parse(rows[0]!.slice('PLAIN_DEEP_CASE '.length)); cases.push(row)
    assert.equal(row.allowance, work); assert.equal(row.originalModel, true)
    assert.equal(row.positiveFixtureWeightsOnly, true); assert.equal(row.forbiddenWallAndUnseededRandomReads, true)
    if (row.solverWorkObserved) break
  }
  for (const [path, blob] of Object.entries(source.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  console.log('PLAIN_DEEP_SUMMARY ' + JSON.stringify({parent: '32a59b2a', prototypePatch: artifact.patchSha256, cases: cases.map(row => ({allowance: row.allowance, result: row.result, solverWorkObserved: row.solverWorkObserved})), solverWorkObserved: cases.some(row => row.solverWorkObserved), sourceFilesUnchanged: Object.keys(source.expectedCandidateBlobs).length, admitted: false, scope: 'fresh-process bounded coverage only; no source promotion, calibrated weights/W or complete ordinary/EPR qualification'}))
} finally { rmSync(temp, {recursive: true, force: true}) }
