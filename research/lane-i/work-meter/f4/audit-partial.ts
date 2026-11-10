import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {auditLog} from './audit.ts'
const snapshot = JSON.parse(readFileSync('pilot-receipts/rows.json', 'utf8'))
assert.equal(snapshot.rows.length, 3)
assert.equal(snapshot.done, false)
const pairs = snapshot.rows.map((row: any) => {
  assert.equal(row.code, 0)
  const match = /^raw-(consensus|consensus_epr|mldr)-large$/.exec(row.name)
  assert(match)
  const pair = auditLog(readFileSync('pilot-receipts/' + row.name + '.log', 'utf8'), match[1]!)
  assert.equal(pair.cpu, row.placement.cpu)
  return {id: pair.id, cpu: pair.cpu, arch: pair.arch, runtime: pair.runtime, fingerprint: pair.fingerprint, raw: pair.raw, result: pair.result, source: pair.source}
})
assert.equal(new Set(pairs.map((row: any) => row.id)).size, 3)
console.log('RAW_CENSUS_PARTIAL_AUDIT ' + JSON.stringify({passed: true, completedPairs: 3, pendingPairs: 3, pairs, scope: 'one validated fresh-process pair per protocol; cross-CPU repeat for each still missing'}))
