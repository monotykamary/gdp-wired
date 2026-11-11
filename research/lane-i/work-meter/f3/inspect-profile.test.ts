import {strict as assert} from 'node:assert'
import {mkdtempSync, writeFileSync, rmSync} from 'node:fs'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'

const root = mkdtempSync(join(tmpdir(), 'profile-archive-fixtures-'))
try {
  const raw = JSON.stringify({startTime: 1000, endTime: 2000, samples: [1, 1, 1], timeDeltas: [200, -300, 1100], nodes: [{id: 1, callFrame: {functionName: 'fixture'}}]})
  const record = {report: 1, retained: true, encoding: 'gzip-base64', bytes: Buffer.byteLength(raw), sha256: createHash('sha256').update(raw).digest('hex'), data: gzipSync(raw).toString('base64')}
  const run = (records: unknown[]) => {
    const file = join(root, 'input.log')
    writeFileSync(file, records.map(value => 'F3_INVALID_PROFILE ' + JSON.stringify(value)).join('\n'))
    const result = spawnSync(process.execPath, [new URL('./inspect-profile.ts', import.meta.url).pathname, file], {encoding: 'utf8', timeout: 10000})
    assert.equal(result.signal, null)
    assert.equal(result.error, undefined)
    return result
  }
  const ok = run([record])
  assert.equal(ok.status, 0, ok.stderr)
  const result = JSON.parse(ok.stdout.trim().slice('F3_INVALID_PROFILE_INSPECTION '.length))
  assert.equal(result.negativeDeltaCount, 1)
  assert.equal(result.negativeDeltas[0].deltaUs, -300)
  assert.equal(result.negativeDeltas[0].sampleTimeUs, 900)
  assert.equal(result.outsideIntervalCount, 1)
  assert.equal(result.lastSampleUs, 2000)
  assert.equal(result.minSampleUs, 900)
  for (const records of [[], [record, record, record], [{...record, retained: false}], [{...record, sha256: 'wrong'}], [{...record, bytes: 8 * 1024 * 1024 + 1}], [{...record, data: 'not-gzip'}]]) assert.notEqual(run(records).status, 0)
  console.log('F3_PROFILE_ARCHIVE_FIXTURES ' + JSON.stringify({passed: true, positive: 1, negative: 6, timestampsNormalized: false}))
} finally { rmSync(root, {recursive: true, force: true}) }
