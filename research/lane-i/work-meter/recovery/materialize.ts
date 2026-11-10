import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
import {restore, command} from './final-gate-common.ts'

// Recover the already collected artifact, never re-run its constructor generator.
const input = resolve('validation-input')
const text = readFileSync('artifact-input/complete-ast-artifact.log', 'utf8')
const rows = text.split('\n')
function tagged<T>(tag: string): T {
  const selected = rows.filter(line => line.startsWith(tag + ' '))
  assert.equal(selected.length, 1, 'one ' + tag)
  return JSON.parse(selected[0]!.slice(tag.length + 1)) as T
}
const meta = tagged<{rawBytes: number, sha256: string, encoding: string, chunks: number}>('AST_SOURCE_META')
assert.equal(meta.encoding, 'gzip-base64')
assert.equal(meta.rawBytes, 982162)
assert.equal(meta.sha256, '52571387a7f165ec76af1e34ea9fe06192abd43d555cd6aa78b2cef93c1734ba')
assert.equal(meta.chunks, 29)
const chunks = rows.filter(line => line.startsWith('AST_SOURCE_CHUNK ')).map((line, index) => {
  const match = /^AST_SOURCE_CHUNK (\d+) ([A-Za-z0-9+/=]+)$/.exec(line)
  assert(match, 'complete unredacted source chunk')
  assert.equal(Number(match[1]), index, 'contiguous, ordered source chunks')
  return match[2]!
})
assert.equal(chunks.length, meta.chunks)
assert.deepEqual(rows.filter(line => line.startsWith('AST_SOURCE_END ')), ['AST_SOURCE_END 29'])
const patch = gunzipSync(Buffer.from(chunks.join(''), 'base64'))
assert.equal(patch.byteLength, meta.rawBytes)
assert.equal(createHash('sha256').update(patch).digest('hex'), meta.sha256)
const audit = tagged<{passed: boolean, sites: number, files: {path: string, before: string, after: string, sites: number}[]}>('AST_CONSTRUCTOR_AUDIT')
assert.equal(audit.passed, true)
assert.equal(audit.sites, 1626)
assert.equal(audit.files.reduce((n, file) => n + file.sites, 0), audit.sites)
assert.equal(new Set(audit.files.map(file => file.path)).size, audit.files.length)
const before = JSON.parse(readFileSync('complete-input/identity.json', 'utf8'))
const original = tagged<{blobs: Record<string, string>}>('GENERATOR_SOURCE')
assert.deepEqual(original.blobs, before.expectedCandidateBlobs)
const temp = mkdtempSync('/tmp/lane-i-artifact-')
try {
  const root = join(temp, 'source')
  restore(resolve('recovery-input'), root, before.integrationBase)
  const path = join(temp, 'candidate.patch')
  writeFileSync(path, patch)
  command('git', ['apply', '--check', path], root)
  command('git', ['apply', path], root)
  const expected = {...before.expectedCandidateBlobs} as Record<string, string>
  for (const file of audit.files) {
    const originalBlob = expected[file.path] ?? command('git', ['rev-parse', 'HEAD:' + file.path], root)
    assert.equal(originalBlob, file.before, 'constructor input: ' + file.path)
    expected[file.path] = file.after
  }
  const actual = Object.fromEntries(Object.keys(expected).sort().map(file => [file, command('git', ['hash-object', file], root)]))
  assert.deepEqual(actual, expected)
  assert.equal(actual['research/protocols/ic3syn/models.ts'], before.originalModelBlob)
  const changed = [...command('git', ['diff', '--name-only'], root).split('\n'), ...command('git', ['ls-files', '--others', '--exclude-standard'], root).split('\n')].filter(Boolean)
  assert(changed.every(file => file in expected), 'all modified/new source files are hash-bound')
  const identity = {...before, candidate: 'complete raw accounting artifact 52571387a7f1', expectedCandidateBlobs: actual,
    artifact: {...meta, sites: audit.sites}, scope: 'raw instrumentation validation only; no calibrated extra weights or W'}
  if (!process.argv.includes('--verify-only')) {
    writeFileSync(join(input, 'candidate.patch'), patch)
    writeFileSync(join(input, 'identity.json'), JSON.stringify(identity, null, 2) + '\n')
  }
  console.log('ARTIFACT_VERIFIED ' + JSON.stringify({passed: true, ...meta, sites: audit.sites, constructorFiles: audit.files.length,
    base: before.integrationBase, originalModel: before.originalModelBlob, expectedCandidateBlobs: actual, scope: identity.scope}))
} finally { rmSync(temp, {recursive: true, force: true}) }
