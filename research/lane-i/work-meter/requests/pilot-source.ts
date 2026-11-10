import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
const patchSha256 = '2c98e5dc8d92da3b1f6833c1e1a331de24b559349c30cc44f52ec5c2a6c53ac2'
const file = process.argv[2]
if (file) {
  const rows = readFileSync(file, 'utf8').split('\n').filter(line => line.startsWith('F3_PILOT_COMPARISON ')).map(line => JSON.parse(line.slice('F3_PILOT_COMPARISON '.length)))
  assert.equal(rows.length, 1)
  assert.equal(rows[0].patchSha256, patchSha256)
  assert.equal(rows[0].sourceUnchanged, true); assert.equal(rows[0].sameRawAndVerdict, true)
} else {
  const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
  assert.equal(config.composition.mode, 'requests')
  assert.equal(config.composition.patchSha256, patchSha256, 'pilot must use the independently verified source')
}
console.log('REQUEST_F3_SOURCE_BOUND ' + JSON.stringify({stage: file ? 'after' : 'before', source: '94b65671b0f81ccfd5e7be71686fc81f35387c94', patchSha256}))
