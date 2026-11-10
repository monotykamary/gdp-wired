import {strict as assert} from 'node:assert'
import {readFileSync, copyFileSync, mkdirSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {spawnSync, type SpawnSyncReturns} from 'node:child_process'
import {createHash} from 'node:crypto'
const {restore, command} = await import(resolve('recovery-input/final-gate-common.ts'))
const source = '41d39043a75e279dc9600e6a33c8107014b67025'
const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
assert.equal(config.composition.patchSha256, 'f59720c766a68a2647cb150c6f3e0793363aa36804eb6bc3185430488f0eebe0')
const id = process.argv[2]
assert(id && /^[a-z0-9_]+$/.test(id), 'original protocol id required')
const temp = mkdtempSync('/tmp/lane-i-raw-census-'), root = join(temp, 'source')
try {
  restore(resolve('recovery-input'), root, config.integrationBase)
  command('git', ['apply', resolve('validation-input/candidate.patch')], root)
  for (const [path, hash] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), hash)
  command('bun', ['install', '--frozen-lockfile'], root, 180000)
  const tooling = join(root, 'research/lane-i/f3'); mkdirSync(tooling, {recursive: true})
  copyFileSync('f3-input/facade.source', join(tooling, 'facade.ts'))
  copyFileSync('f4-input/census.source', join(tooling, 'census.ts'))
  const results: any[] = []
  for (let repetition = 1; repetition <= 2; repetition++) {
    const child: SpawnSyncReturns<string> = spawnSync('bun', ['research/lane-i/f3/census.ts', id, String(repetition)], {cwd: root, encoding: 'utf8', timeout: 1800000, maxBuffer: 32 * 1024 * 1024, env: {...process.env, RAW_CENSUS_SOURCE: source}})
    console.log('RAW_CENSUS_PROCESS ' + JSON.stringify({id, repetition, exit: child.status, signal: child.signal, error: String(child.error ?? ''), stdoutSha256: createHash('sha256').update(child.stdout ?? '').digest('hex')}))
    console.log(child.stdout); if (child.stderr) console.error(child.stderr.slice(-12000))
    assert.equal(child.status, 0, 'external crash guard is infrastructure failure, not unknown')
    const lines = child.stdout.split('\n').filter(line => line.startsWith('RAW_CENSUS_RECORD '))
    assert.equal(lines.length, 1)
    const row = JSON.parse(lines[0]!.slice('RAW_CENSUS_RECORD '.length))
    assert.equal(row.id, id); assert.equal(row.source, source); assert.equal(row.repetition, repetition)
    results.push(row)
  }
  assert.deepEqual(results[0].raw, results[1].raw)
  assert.deepEqual(results[0].result, results[1].result)
  assert.equal(results[0].fingerprint, results[1].fingerprint)
  for (const [path, hash] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), hash, 'source unchanged after census')
  console.log('RAW_CENSUS_PAIR ' + JSON.stringify({passed: true, source, id, fingerprint: results[0].fingerprint, cpu: results[0].cpu, arch: results[0].arch, runtime: results[0].runtime, result: results[0].result, raw: results[0].raw, repeats: 2, scope: 'same-host fresh-process raw determinism only; not cross-CPU or calibrated W'}))
} finally { rmSync(temp, {recursive: true, force: true}) }
