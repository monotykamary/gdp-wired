import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync, mkdtempSync, rmSync, existsSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {restore, command} from './final-gate-common.ts'

// Research staging only. Never choose a side of a conflict automatically.
const mode = process.env.METER_COMPOSITION ?? process.argv[2]
assert(['ledger', 'boundaries', 'bitmap'].includes(mode ?? ''), 'ledger, boundaries or bitmap required')
const rawConfig = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
const baseConfig = JSON.parse(readFileSync('complete-input/identity.json', 'utf8'))
const ledgerConfig = JSON.parse(readFileSync('ledger-input/identity.json', 'utf8'))
assert.equal(rawConfig.artifact.sha256, '52571387a7f165ec76af1e34ea9fe06192abd43d555cd6aa78b2cef93c1734ba')
const temp = mkdtempSync('/tmp/lane-i-compose-'), records: object[] = []
const root = (name: string, patch: string, config: typeof rawConfig) => {
  const dir = join(temp, name)
  restore(resolve('recovery-input'), dir, config.integrationBase)
  command('git', ['apply', '--check', resolve(patch)], dir)
  command('git', ['apply', resolve(patch)], dir)
  for (const [path, hash] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], dir), hash, name + ': ' + path)
  return dir
}
try {
  const base = root('pre-constructor', 'complete-input/candidate.patch', baseConfig)
  const ledger = root('ledger', 'ledger-input/candidate.patch', ledgerConfig)
  const out = root('combined', 'validation-input/candidate.patch', rawConfig)
  let index = 0
  const merge = (path: string, before: string | undefined, after: string, phase: string) => {
    const target = join(out, path), old = existsSync(target) ? readFileSync(target, 'utf8') : undefined
    if (before === undefined) { assert.equal(old, undefined, 'new ledger file collision: ' + path); writeFileSync(target, after) }
    else {
      assert.notEqual(old, undefined)
      const a = join(temp, 'ours-' + index), b = join(temp, 'base-' + index), c = join(temp, 'theirs-' + index++)
      writeFileSync(a, old!); writeFileSync(b, before); writeFileSync(c, after)
      const result = spawnSync('git', ['merge-file', '-p', a, b, c], {encoding: 'utf8', maxBuffer: 16 * 1024 * 1024})
      if (result.status !== 0) console.error('COMPOSITION_CONFLICT ' + JSON.stringify({phase, path, exit: result.status, detail: result.stdout.slice(-16000)}))
      assert.equal(result.status, 0, 'unresolved composition conflict: ' + path)
      writeFileSync(target, result.stdout)
    }
    records.push({phase, path, before: before === undefined ? null : createHash('sha256').update(before).digest('hex'), merged: command('git', ['hash-object', path], out)})
  }
  for (const [path, hash] of Object.entries(ledgerConfig.expectedCandidateBlobs)) {
    if (hash === baseConfig.expectedCandidateBlobs[path]) continue
    merge(path, existsSync(join(base, path)) ? readFileSync(join(base, path), 'utf8') : undefined, readFileSync(join(ledger, path), 'utf8'), 'ledger')
  }
  if (mode === 'boundaries' || mode === 'bitmap') {
    const paths = ['core/counts.ts', 'kernel/prove.ts'], before = Object.fromEntries(paths.map(path => [path, readFileSync(join(ledger, path), 'utf8')]))
    command('git', ['apply', '--check', resolve('ledger-input/boundaries.patch')], ledger)
    command('git', ['apply', resolve('ledger-input/boundaries.patch')], ledger)
    for (const path of paths) merge(path, before[path], readFileSync(join(ledger, path), 'utf8'), 'boundaries')
  }
  if (mode === 'bitmap') {
    writeFileSync(join(out, 'core/bitsets.ts'), readFileSync('coverage-input/bitsets.source'))
    writeFileSync(join(out, 'core/bitsets-meter.test.ts'), readFileSync('coverage-input/bitsets-meter.test.source'))
    const path = join(out, 'scripts/test-shards.ts'), source = readFileSync(path, 'utf8'), anchor = 'bitsets.test.ts'
    assert.equal(source.split(anchor).length, 2)
    writeFileSync(path, source.replace(anchor, anchor + ' bitsets-meter.test.ts'))
  }
  assert.equal(command('git', ['hash-object', 'research/protocols/ic3syn/models.ts'], out), rawConfig.originalModelBlob)
  command('git', ['add', '--', 'core', 'kernel', 'scripts/test-shards.ts'], out)
  const paths = command('git', ['diff', '--cached', '--name-only'], out).split('\n')
  const expected = Object.fromEntries([...new Set([...Object.keys(rawConfig.expectedCandidateBlobs), ...paths])].sort().map(path => [path, command('git', ['hash-object', path], out)]))
  const result = spawnSync('git', ['diff', '--cached', '--binary', 'HEAD', '--', 'core', 'kernel', 'scripts/test-shards.ts'], {cwd: out, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024})
  assert.equal(result.status, 0)
  const hash = createHash('sha256').update(result.stdout).digest('hex')
  const config = {...rawConfig, candidate: 'complete raw accounting + ' + mode + ' ' + hash.slice(0, 12), expectedCandidateBlobs: expected,
    composition: {mode, patchSha256: hash, records}, scope: 'research composition only; no new weights, W or production promotion'}
  writeFileSync('validation-input/candidate.patch', result.stdout)
  writeFileSync('validation-input/identity.json', JSON.stringify(config, null, 2) + '\n')
  console.log('COMPOSITION_VERIFIED ' + JSON.stringify({mode, patchSha256: hash, bytes: Buffer.byteLength(result.stdout), records, expectedCandidateBlobs: expected}))
} finally { rmSync(temp, {recursive: true, force: true}) }
