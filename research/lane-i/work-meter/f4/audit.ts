import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
export const source = '41d39043a75e279dc9600e6a33c8107014b67025'
export const patch = 'f59720c766a68a2647cb150c6f3e0793363aa36804eb6bc3185430488f0eebe0'
const keys = ['fm','fcells','plainRows','values','copies','edges','scan','pivotRows','unitRows','unfoldRows','goalNodes','translateRows','tableCells','checkSteps','astNodes','evals','cubeTests','ticks','cdclNodes','epr']
export const sha = (text: string) => createHash('sha256').update(text).digest('hex')
const records = (text: string, tag: string): any[] => text.split('\n').filter(line => line.startsWith(tag + ' ')).map(line => JSON.parse(line.slice(tag.length + 1)))
export function auditLog(text: string, id: string) {
  const compositions = records(text, 'COMPOSITION_VERIFIED'), pairs = records(text, 'RAW_CENSUS_PAIR')
  assert.equal(compositions.length, 1); assert.equal(compositions[0].mode, 'canonical'); assert.equal(compositions[0].patchSha256, patch)
  assert.equal(pairs.length, 1); const pair = pairs[0]
  assert.equal(pair.passed, true); assert.equal(pair.source, source); assert.equal(pair.id, id); assert.equal(pair.repeats, 2)
  const headers = [...text.matchAll(/^RAW_CENSUS_PROCESS (.+)$/gm)]
  assert.equal(headers.length, 2)
  const end = /^RAW_CENSUS_PAIR /m.exec(text)!.index, rows: any[] = []
  for (let i = 0; i < headers.length; i++) {
    const header = headers[i]!, process = JSON.parse(header[1]!)
    assert.equal(process.id, id); assert.equal(process.repetition, i + 1); assert.equal(process.exit, 0); assert.equal(process.signal, null); assert.equal(process.error, '')
    const start = header.index! + header[0].length + 1, stop = i + 1 < headers.length ? headers[i + 1]!.index! : end
    const captured = text.slice(start, stop)
    assert(captured.endsWith('\n'), 'console framing')
    const stdout = captured.slice(0, -1)
    assert.equal(sha(stdout), process.stdoutSha256, 'lossless child stdout')
    const parsed = records(stdout, 'RAW_CENSUS_RECORD')
    assert.equal(parsed.length, 1); const row = parsed[0]
    assert.equal(row.source, source); assert.equal(row.id, id); assert.equal(row.repetition, i + 1); assert.equal(row.work, 15000000)
    assert.equal(row.phaseReconciliation, true)
    assert.equal(row.seedPolicy, 'production defaults, no override')
    assert.equal(row.unitModel, 'legacy fixed allowance for raw determinism only; not calibrated W')
    assert.equal(typeof row.affinity, 'string'); assert(row.affinity.length > 0)
    assert.equal(typeof row.cpu, 'string'); assert(row.cpu.length > 0)
    assert.equal(typeof row.arch, 'string'); assert.equal(typeof row.runtime, 'string')
    assert.deepEqual(Object.keys(row.raw).sort(), [...keys].sort())
    assert(Object.values(row.raw).every(n => Number.isSafeInteger(n) && Number(n) >= 0))
    assert.equal(row.fingerprint, sha(JSON.stringify({id: row.id, work: row.work, result: row.result, raw: row.raw})))
    rows.push(row)
  }
  assert.deepEqual(rows[0].raw, rows[1].raw); assert.deepEqual(rows[0].result, rows[1].result)
  for (const key of ['fingerprint','cpu','arch','runtime']) { assert.equal(rows[0][key], rows[1][key]); assert.equal(pair[key], rows[0][key]) }
  assert.deepEqual(pair.raw, rows[0].raw); assert.deepEqual(pair.result, rows[0].result)
  return pair
}
export function auditPairs(pairs: any[]) {
  const ids = ['consensus','consensus_epr','mldr']
  assert.equal(pairs.length, 6)
  assert.equal(new Set(pairs.map(row => row.runtime)).size, 1, 'one runtime')
  const protocols = ids.map(id => {
    const rows = pairs.filter(row => row.id === id)
    assert.equal(rows.length, 2, id + ' placement pair')
    const cpus = [...new Set(rows.map(row => row.cpu))]
    const agreement = rows[0].fingerprint === rows[1].fingerprint
    if (!agreement) console.error('RAW_CENSUS_DIFFERENCE ' + JSON.stringify({id, cpus, results: rows.map(row => row.result), raw: rows.map(row => row.raw)}))
    assert(agreement, id + ' raw/verdict disagreement across placements')
    return {id, cpus, crossCpu: cpus.length >= 2, fingerprint: rows[0].fingerprint, result: rows[0].result}
  })
  return {passed: true, source, protocols, crossCpuProtocols: protocols.filter(row => row.crossCpu).map(row => row.id), scope: 'three-protocol raw pilot, not full F4 or calibrated W'}
}
if (import.meta.main) {
  const directory = process.argv[2]!
  const summary = readFileSync(join(directory, 'summary.tsv'), 'utf8').trim().split('\n').map(line => line.split('\t'))
  assert.equal(summary.length, 6)
  const seen = new Set<string>(), pairs = summary.map(([name, code]) => {
    assert(name); assert.equal(Number(code), 0); assert(!seen.has(name)); seen.add(name)
    const match = /^raw-(consensus|consensus_epr|mldr)-(default|large)$/.exec(name)
    assert(match, 'expected pilot placement'); return auditLog(readFileSync(join(directory, name + '.log'), 'utf8'), match[1]!)
  })
  console.log('RAW_CENSUS_AUDIT ' + JSON.stringify(auditPairs(pairs)))
}
