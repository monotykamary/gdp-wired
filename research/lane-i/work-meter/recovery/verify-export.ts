import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
const read = (file: string) => readFileSync(file, 'utf8').split('\n')
const lines = read('export-input/export-complete-ledger-source.log')
const tagged = (rows: string[], tag: string) => { const matches = rows.filter(row => row.startsWith(tag + ' ')); assert.equal(matches.length, 1); return JSON.parse(matches[0]!.slice(tag.length + 1)) }
const meta = tagged(lines, 'COMPOSE_SOURCE_META'), exported = tagged(lines, 'COMPOSITION_VERIFIED')
const tested = tagged(read('tested-input/complete-ledger-checks.log'), 'COMPOSITION_VERIFIED')
assert.deepEqual(exported, tested, 'export equals tested source')
const chunks = lines.filter(row => row.startsWith('COMPOSE_SOURCE_CHUNK ')).map((row, i) => {
  const match = /^COMPOSE_SOURCE_CHUNK (\d+) ([A-Za-z0-9+/=]+)$/.exec(row)
  assert(match); assert.equal(Number(match[1]), i); return match[2]!
})
assert.equal(chunks.length, meta.chunks)
assert.deepEqual(lines.filter(row => row.startsWith('COMPOSE_SOURCE_END ')), ['COMPOSE_SOURCE_END ' + chunks.length])
const patch = gunzipSync(Buffer.from(chunks.join(''), 'base64'))
assert.equal(patch.byteLength, meta.rawBytes)
const sha256 = createHash('sha256').update(patch).digest('hex')
assert.equal(sha256, meta.sha256); assert.equal(sha256, exported.patchSha256)
console.log('COMPOSE_EXPORT_VERIFIED ' + JSON.stringify({passed: true, mode: exported.mode, sha256, rawBytes: meta.rawBytes, chunks: chunks.length, matchesTestedSource: true}))
