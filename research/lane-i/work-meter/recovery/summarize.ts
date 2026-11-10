import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
import {stripVTControlCharacters} from 'node:util'
const sha = (s: string) => createHash('sha256').update(s).digest('hex')
const input = process.argv[2] ?? 'validation-results'
const summary = readFileSync(join(input, 'summary.tsv'), 'utf8').trim().split('\n').map(line => line.split('\t'))
const outputs = []
for (const [name, exit] of summary) {
  assert(name)
  const text = readFileSync(join(input, name + '.log'), 'utf8')
  const tags = (tag: string) => text.split('\n').filter(line => line.startsWith(tag + ' ')).map(line => JSON.parse(line.slice(tag.length + 1)))
  const source = tags('GENERATOR_SOURCE'), end = tags('GENERATOR_UNCHANGED'), checks = tags('GENERATOR_CHECK')
  const artifact = tags('ARTIFACT_VERIFIED'), composition = tags('COMPOSITION_VERIFIED')
  assert.equal(artifact.length, 1, 'one verified raw artifact')
  const expected = composition.length ? composition[0].expectedCandidateBlobs : artifact[0].expectedCandidateBlobs
  if (source.length) {
    assert.deepEqual(source[0].blobs, expected, 'exact source identity')
    assert.equal(source[0].patchSha256, composition.length ? composition[0].patchSha256 : artifact[0].sha256)
  }
  const decoded = checks.map(row => {
    const raw = gunzipSync(Buffer.from(row.traceGzipBase64, 'base64')).toString(), at = raw.indexOf('\n---stderr---\n')
    assert(at >= 0)
    assert.equal(sha(raw.slice(0, at)), row.stdoutSha256)
    assert.equal(sha(raw.slice(at + '\n---stderr---\n'.length)), row.stderrSha256)
    const plain = stripVTControlCharacters(raw)
    const mutation = plain.split('\n').filter(line => line.startsWith('KERNEL_METER_MUTATION ')).map(line => JSON.parse(line.slice('KERNEL_METER_MUTATION '.length)))
    if (name?.match(/-(zero|double|random)$/) && row.label === 'targeted') {
      assert.equal(mutation.length, 1, 'one final mutation observation')
      assert.equal(mutation[0].exercised, true)
      assert.equal(mutation[0].mode, name.split('-').at(-1))
    }
    const result = {label: row.label, exit: row.exit, signal: row.signal, pass: plain.match(/(\d+) pass/)?.[1], fail: plain.match(/(\d+) fail/)?.[1], hashesVerified: true}
    if (row.exit !== 0) console.log('VALIDATION_FAILURE ' + JSON.stringify({name, label: row.label, output: plain.slice(-24000)}))
    console.log('VALIDATION_CHECK ' + JSON.stringify({name, ...result}))
    return result
  })
  const passed = Number(exit) === 0 && source.length === 1 && end.length === 1 && checks.length > 0 && checks.every(row => row.exit === 0)
  if (!checks.length) console.log('VALIDATION_SETUP_FAILURE ' + JSON.stringify({name, output: text.slice(-16000)}))
  const row = {name, exit: Number(exit), passed, sourcePresent: source.length === 1, unchanged: end.length === 1, checks: decoded}
  outputs.push(row)
  console.log('VALIDATION_RESULT ' + JSON.stringify(row))
}
assert.equal(new Set(outputs.map(row => row.name)).size, outputs.length)
console.log('VALIDATION_SUMMARY ' + JSON.stringify({passed: outputs.every(row => row.passed), jobs: outputs}))
