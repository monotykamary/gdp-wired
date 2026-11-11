import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'

// Diagnostic only: never normalize timestamps or turn rejected data into evidence.
const file = process.argv[2]
assert(file, 'usage: bun inspect-profile.ts pilot.log')
const prefix = 'F3_INVALID_PROFILE '
const records = readFileSync(file, 'utf8').split('\n').filter(line => line.startsWith(prefix)).map(line => JSON.parse(line.slice(prefix.length)))
assert(records.length > 0 && records.length <= 2, 'one or two bounded retained profiles required')
for (const record of records) {
  assert.equal(record.retained, true)
  assert.equal(record.encoding, 'gzip-base64')
  assert(Number.isSafeInteger(record.bytes) && record.bytes > 0 && record.bytes <= 8 * 1024 * 1024)
  const raw = gunzipSync(Buffer.from(record.data, 'base64'), {maxOutputLength: 8 * 1024 * 1024})
  assert.equal(raw.length, record.bytes)
  assert.equal(createHash('sha256').update(raw).digest('hex'), record.sha256)
  const profile = JSON.parse(raw.toString('utf8'))
  assert(Array.isArray(profile.samples) && Array.isArray(profile.timeDeltas))
  assert.equal(profile.samples.length, profile.timeDeltas.length)
  assert(Number.isFinite(profile.startTime) && Number.isFinite(profile.endTime))
  assert(profile.endTime >= profile.startTime)
  const nodes = new Map<number, any>(profile.nodes.map((node: any) => [node.id, node]))
  const negative = [], outside = []
  let time = profile.startTime, minTime = time, maxTime = time
  for (let index = 0; index < profile.timeDeltas.length; index++) {
    const delta = profile.timeDeltas[index]
    assert(Number.isFinite(delta))
    const previousSampleUs = time
    time += delta
    minTime = Math.min(minTime, time); maxTime = Math.max(maxTime, time)
    if (delta < 0) negative.push({index, deltaUs: delta, previousSampleUs, sampleTimeUs: time, frame: nodes.get(profile.samples[index])?.callFrame})
    if (time < profile.startTime || time > profile.endTime) outside.push({index, sampleTimeUs: time})
  }
  console.log('F3_INVALID_PROFILE_INSPECTION ' + JSON.stringify({report: record.report, sha256: record.sha256, samples: profile.samples.length,
    profileStartUs: profile.startTime, profileEndUs: profile.endTime, lastSampleUs: time, minSampleUs: minTime, maxSampleUs: maxTime,
    negativeDeltaCount: negative.length, negativeDeltas: negative.slice(0, 16), outsideIntervalCount: outside.length, outsideInterval: outside.slice(0, 16),
    scope: 'raw invalid-profile diagnosis only; strict rejection unchanged'}))
}
