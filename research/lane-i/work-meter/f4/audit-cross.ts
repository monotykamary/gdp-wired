import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {auditLog, auditPairs} from './audit.ts'
const ids = ['consensus','consensus_epr','mldr']
function collect(directory: string, suffix: string) {
  const snapshot = JSON.parse(readFileSync(directory + '/rows.json', 'utf8'))
  assert.equal(snapshot.rows.length, 3)
  const seen = new Set<string>()
  return snapshot.rows.map((row: any) => {
    assert.equal(row.code, 0)
    const id = ids.find(id => row.name === 'raw-' + id + '-' + suffix)
    assert(id); assert(!seen.has(id)); seen.add(id)
    const text = readFileSync(directory + '/' + row.name + '.log', 'utf8')
    const pair = auditLog(text, id)
    assert.equal(pair.cpu, row.placement.cpu)
    if (suffix === 'cross') {
      const gates = text.split('\n').filter(line => line.startsWith('RAW_CENSUS_CPU_GATE ')).map(line => JSON.parse(line.slice('RAW_CENSUS_CPU_GATE '.length)))
      assert.equal(gates.length, 1)
      assert.equal(gates[0].id, id); assert.equal(gates[0].selected, true); assert.equal(gates[0].cpu, pair.cpu)
      assert.notEqual(gates[0].firstCpu, pair.cpu)
      return {...pair, firstCpu: gates[0].firstCpu}
    }
    return pair
  })
}
const first = collect('first-receipts', 'large'), second = collect('cross-receipts', 'cross')
for (const row of second) assert.equal(row.firstCpu, first.find((base: any) => base.id === row.id)!.cpu)
const result = auditPairs([...first, ...second])
assert.deepEqual([...result.crossCpuProtocols].sort(), [...ids].sort())
console.log('RAW_CENSUS_CROSS_CPU_AUDIT ' + JSON.stringify({...result,
  pathCoverage: first.map((row: any) => ({id: row.id, solverCountersNonzero: Object.entries(row.raw).some(([key, n]) => key !== 'astNodes' && Number(n) > 0), eprCounterNonzero: row.raw.epr > 0})),
  qualificationBlocked: ['ordinary work path refuses execution', 'EPR path not observed by its counter', 'Bun F3 unavailable', 'weights and W uncalibrated'],
}))
