import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
import {stripVTControlCharacters} from 'node:util'
const fixture = 'core/request-materialization.test.ts'
function inspect(directory: string, name: string, mutation?: string) {
  const status = readFileSync(join(directory, 'summary.tsv'), 'utf8').trim().split('\n').map(line => line.split('\t')).filter(([id]) => id === name)
  assert.equal(status.length, 1); assert.equal(Number(status[0]![1]), 0, name + ' process exit')
  const text = readFileSync(join(directory, name + '.log'), 'utf8')
  const rows = (tag: string): any[] => text.split('\n').filter(line => line.startsWith(tag + ' ')).map(line => JSON.parse(line.slice(tag.length + 1)))
  const one = (tag: string) => { const selected = rows(tag); assert.equal(selected.length, 1, tag); return selected[0] }
  const artifact = one('ARTIFACT_VERIFIED'), composition = one('COMPOSITION_VERIFIED'), source = one('GENERATOR_SOURCE'), end = one('GENERATOR_UNCHANGED'), checks = rows('GENERATOR_CHECK')
  assert.equal(artifact.passed, true)
  assert.equal(artifact.sha256, '52571387a7f165ec76af1e34ea9fe06192abd43d555cd6aa78b2cef93c1734ba')
  assert.equal(composition.mode, 'requests'); assert.deepEqual(source.blobs, composition.expectedCandidateBlobs)
  assert.equal(source.patchSha256, composition.patchSha256); assert.equal(end.candidate, source.candidate); assert.equal(end.production, true)
  assert.equal(source.blobs['research/protocols/ic3syn/models.ts'], '0541fa9436e307a6fb716aa5064637b30b893b79')
  assert.deepEqual(checks.map(row => row.label), mutation ? ['meter-audit','targeted','roster','decoder'] : ['meter-audit','targeted','roster','decoder','type-lint'])
  let tests = 0
  for (const check of checks) {
    assert.equal(check.exit, 0); assert.equal(check.signal, null)
    const raw = gunzipSync(Buffer.from(check.traceGzipBase64, 'base64')).toString(), delimiter = '\n---stderr---\n', at = raw.indexOf(delimiter)
    assert(at >= 0)
    const sha = (s: string) => createHash('sha256').update(s).digest('hex')
    assert.equal(sha(raw.slice(0, at)), check.stdoutSha256); assert.equal(sha(raw.slice(at + delimiter.length)), check.stderrSha256)
    if (check.label === 'targeted') {
      const plain = stripVTControlCharacters(raw); tests = Number(plain.match(/(\d+) pass/)?.[1]); assert.equal(Number(plain.match(/(\d+) fail/)?.[1]), 0)
      if (mutation) {
        assert.equal(tests, 267); assert(!check.args.includes('./' + fixture))
        const controls = plain.split('\n').filter(line => line.startsWith('KERNEL_METER_MUTATION ')).map(line => JSON.parse(line.slice('KERNEL_METER_MUTATION '.length)))
        assert.equal(controls.length, 1); assert.equal(controls[0].mode, mutation); assert.equal(controls[0].exercised, true)
      } else assert.equal(tests, 164)
    }
  }
  return {composition, source, tests}
}
export function verifyRequestReceipts() {
  const tested = inspect('selected-results', 'request-accounting-checks')
  const production = (blobs: Record<string, string>) => Object.fromEntries(Object.entries(blobs).filter(([path]) => path !== fixture))
  const differences: Record<string, string[]> = {}
  for (const mode of ['zero','double','random']) {
    const control = inspect('mutation-results', 'request-accounting-' + mode, mode)
    assert.deepEqual(production(control.source.blobs), production(tested.source.blobs), 'only the unused exact fixture may change')
    const changed = Object.keys(tested.source.blobs).filter(path => tested.source.blobs[path] !== control.source.blobs[path]).sort()
    assert.deepEqual(changed, [fixture]); differences[mode] = changed
  }
  return {passed: true, tests: tested.tests, mutationTestsPerMode: 267, mutationSourceDifferences: differences, patchSha256: tested.source.patchSha256, expectedCandidateBlobs: tested.source.blobs, scope: 'source and receipt audit only; no complete coverage, calibration or source admission'}
}
if (import.meta.main) console.log('REQUEST_SOURCE_RECEIPTS ' + JSON.stringify(verifyRequestReceipts()))
