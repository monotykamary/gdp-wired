import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {stripVTControlCharacters} from 'node:util'
const text = readFileSync(process.argv[2] ?? 'ledger-check-data/work-ledger-checks.log', 'utf8')
const checks = text.split('\n').filter(line => line.startsWith('GENERATOR_CHECK ')).map(line => JSON.parse(line.slice('GENERATOR_CHECK '.length)))
assert(checks.length > 0)
for (const row of checks) {
  const raw = gunzipSync(Buffer.from(row.traceGzipBase64, 'base64')).toString(), at = raw.indexOf('\n---stderr---\n')
  assert(at >= 0)
  assert.equal(createHash('sha256').update(raw.slice(0, at)).digest('hex'), row.stdoutSha256)
  assert.equal(createHash('sha256').update(raw.slice(at + '\n---stderr---\n'.length)).digest('hex'), row.stderrSha256)
  const plain = stripVTControlCharacters(raw)
  console.log('LEDGER_RECEIPT_SUMMARY ' + JSON.stringify({label: row.label, exit: row.exit, signal: row.signal, passed: plain.match(/(\d+) pass/)?.[1], failed: plain.match(/(\d+) fail/)?.[1], checkedHash: true}))
  if (row.exit !== 0) console.log('LEDGER_FAILED_OUTPUT\n' + plain.slice(-16000))
}
if (process.argv.includes('--require-pass')) {
  const config = JSON.parse(readFileSync('ledger-input/identity.json', 'utf8'))
  const tagged = (tag: string) => text.split('\n').filter(line => line.startsWith(tag + ' ')).map(line => JSON.parse(line.slice(tag.length + 1)))
  const source = tagged('GENERATOR_SOURCE'), end = tagged('GENERATOR_UNCHANGED')
  assert.equal(source.length, 1); assert.equal(end.length, 1)
  assert.equal(source[0].candidate, config.candidate)
  assert.deepEqual(source[0].blobs, config.expectedCandidateBlobs)
  assert.equal(end[0].candidate, config.candidate); assert.equal(end[0].production, true)
  assert.deepEqual(checks.map(row => row.label), ['targeted', 'roster', 'decoder', 'type-lint'])
  for (const row of checks) { assert.equal(row.exit, 0); assert.equal(row.signal, null) }
  console.log('LEDGER_SOURCE_AND_RECEIPT_AUDIT ' + JSON.stringify({passed: true, candidate: config.candidate, originalModel: source[0].blobs['research/protocols/ic3syn/models.ts'], sourceUnchanged: true}))
}
