import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {stripVTControlCharacters} from 'node:util'
const text = readFileSync('ledger-check-data/work-ledger-checks.log', 'utf8')
const checks = text.split('\n').filter(line => line.startsWith('GENERATOR_CHECK ')).map(line => JSON.parse(line.slice('GENERATOR_CHECK '.length)))
assert(checks.length > 0)
for (const row of checks) {
  const raw = gunzipSync(Buffer.from(row.traceGzipBase64, 'base64')).toString(), at = raw.indexOf('\n---stderr---\n')
  assert(at >= 0)
  assert.equal(createHash('sha256').update(raw.slice(0, at)).digest('hex'), row.stdoutSha256)
  const plain = stripVTControlCharacters(raw)
  console.log('LEDGER_RECEIPT_SUMMARY ' + JSON.stringify({label: row.label, exit: row.exit, signal: row.signal, passed: plain.match(/(\d+) pass/)?.[1], failed: plain.match(/(\d+) fail/)?.[1], checkedHash: true}))
  if (row.exit !== 0) console.log('LEDGER_FAILED_OUTPUT\n' + plain.slice(-16000))
}
