// Collect a six-case original-source harness audit, never promote extraction to a finding.
// bun research/security/collect-solidity-harness.ts <log-dir> <frontend-snapshot> [output.json]
import {readFileSync, writeFileSync} from 'node:fs'
import {resolve} from 'node:path'
import type {SolidityHarness} from '../../core/extract-sol.ts'

type Side = {version: string, sha: string, sourceSha256: string, originalUnchanged: boolean, status: string, harness: SolidityHarness | null, [key: string]: unknown}
type Receipt = {id: string, found: boolean, sides: Side[], [key: string]: unknown}
type Case = {id: string, before: string, after?: string}
const [dir, snapshot, output = 'research/security/solidity-harness-measurement.json'] = process.argv.slice(2)
if (!dir || !snapshot || !/^[a-f0-9]{12,64}$/.test(snapshot)) throw new Error('Provide a log directory and its recorded frontend tree hash')
const cases = JSON.parse(readFileSync(new URL('./cases.json', import.meta.url), 'utf8')) as Case[]
const previous = JSON.parse(readFileSync(new URL('./measurement.json', import.meta.url), 'utf8')) as {rows: {id: string, sides: {version: string, sourceSha256: string}[]}[]}
const ids = ['oz-uups', 'oz-initializer', 'oz-supply', 'oz-quorum', 'oz-crosschain', 'oz-multicall']
const rows = ids.map(id => {
  const text = readFileSync(resolve(dir, `${id}.log`), 'utf8'), line = text.split('\n').find(s => s.startsWith('{"id"'))
  if (!line) throw new Error(`No receipt for ${id}`)
  const r = JSON.parse(line) as Receipt, c = cases.find(c => c.id === id)
  if (!c || r.id !== id || r.found !== false || r.sides.length !== 2 || r.sides.map(s => s.version).join(',') !== 'vulnerable,fixed') throw new Error(`Invalid pair ${id}`)
  for (const s of r.sides) {
    if (s.sha !== (s.version === 'vulnerable' ? c.before : c.after) || !s.originalUnchanged || !['refused', 'needs-reviewed-policy-and-original-replay'].includes(s.status)) throw new Error(`Invalid original revision ${id}/${s.version}`)
    const old = previous.rows.find(r => r.id === id)?.sides.find(p => p.version === s.version)
    if (!old || old.sourceSha256 !== s.sourceSha256) throw new Error(`Original hash changed: ${id}/${s.version}`)
    if (!s.harness || !s.harness.source || !s.harness.entry || !s.harness.notes.some(n => n.includes('harness scope'))) throw new Error(`Missing deployment assumptions: ${id}/${s.version}`)
  }
  return r
})
const readable = (s: Side) => s.status === 'needs-reviewed-policy-and-original-replay'
const report = {frontendSnapshot: snapshot, base: '927a521', collectedAt: new Date().toISOString(),
  scope: 'Six Solidity cases only; a conditional concrete-deployment experiment, not the full published corpus',
  published: {found: 0, total: rows.length}, extractionCoverage: {readable: rows.filter(r => r.sides.every(readable)).length, total: rows.length},
  sideCoverage: {readable: rows.flatMap(r => r.sides).filter(readable).length, total: rows.length * 2}, originalsVerified: rows.length * 2, rows}
writeFileSync(output, `${JSON.stringify(report, null, 2)}\n`)
console.log(JSON.stringify({output, frontendSnapshot: snapshot, published: report.published, extractionCoverage: report.extractionCoverage, sideCoverage: report.sideCoverage, originalsVerified: report.originalsVerified}))
