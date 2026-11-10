import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
const patchSha256 = '8df0cf2ac466465a45683a639124d5f774e1b85b72d7f36c1b42b682c4e46fbd'
const file = process.argv[2]
if (file) {
  const rows = readFileSync(file, 'utf8').split('\n').filter(line => line.startsWith('F3_PILOT_COMPARISON ')).map(line => JSON.parse(line.slice('F3_PILOT_COMPARISON '.length)))
  assert.equal(rows.length, 1)
  assert.equal(rows[0].patchSha256, patchSha256)
  assert.equal(rows[0].sourceUnchanged, true); assert.equal(rows[0].sameRawAndVerdict, true)
} else {
  const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
  assert.equal(config.composition.mode, 'numeric')
  assert.equal(config.composition.patchSha256, patchSha256, 'pilot must use the independently verified source')
}
console.log('NUMERIC_F3_SOURCE_BOUND ' + JSON.stringify({stage: file ? 'after' : 'before', source: '32a59b2a4cb38e60ee14cd54a2533bfee76bce89', patchSha256}))
