import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {gzipSync, gunzipSync} from 'node:zlib'

export function decodeGeneration(text: string, id: string) {
  const prefix = 'T13_DATA_GZIP_BASE64 '
  const lines = text.split('\n').filter(line => line.startsWith(prefix))
  assert.equal(lines.length, 1, 'one complete generation payload')
  const data = JSON.parse(gunzipSync(Buffer.from(lines[0]!.slice(prefix.length), 'base64'), {maxOutputLength: 64 * 1024 * 1024}).toString())
  assert.equal(data.queries, 0, 'generation must not issue proof queries')
  assert(Array.isArray(data.records) && data.records.length === 1, 'one protocol record')
  const record = data.records[0]
  assert.equal(record.id, id, 'protocol identity')
  assert(Number.isInteger(record.count) && record.count >= 0, 'law count')
  for (const key of ['canonical', 'names']) {
    assert(Array.isArray(record[key]) && record[key].length === record.count, key + ' completeness')
    assert(record[key].every((value: unknown) => typeof value === 'string'), key + ' strings')
  }
  const hash = (value: unknown) => createHash('sha256').update(JSON.stringify(value)).digest('hex')
  return {id, count: record.count, canonicalHash: hash(record.canonical), namesHash: hash(record.names), phases: record.phases, legacyCprof: record.cprof, states: record.states}
}

if (import.meta.main) {
  assert.equal(process.argv[2], 'self-test')
  const record = {id: 'fixture', count: 1, canonical: ['body'], names: ['law']}
  const encode = (value: unknown) => 'T13_DATA_GZIP_BASE64 ' + gzipSync(JSON.stringify(value)).toString('base64')
  const valid = encode({queries: 0, records: [record]})
  assert.equal(decodeGeneration(valid, 'fixture').count, 1)
  assert.throws(() => decodeGeneration('', 'fixture'))
  assert.throws(() => decodeGeneration(valid + '\n' + valid, 'fixture'))
  assert.throws(() => decodeGeneration(valid, 'other'))
  assert.throws(() => decodeGeneration(encode({queries: 1, records: [record]}), 'fixture'))
  assert.throws(() => decodeGeneration(encode({queries: 0, records: [{...record, count: 2}]}), 'fixture'))
  assert.throws(() => decodeGeneration(encode({queries: 0, records: [{...record, names: [1]}]}), 'fixture'))
  console.log('GENERATION_DECODER_CHECK ' + JSON.stringify({passed: 7}))
}
