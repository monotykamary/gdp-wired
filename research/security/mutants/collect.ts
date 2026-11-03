import assert from 'node:assert/strict'
import {readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {spawnSync} from 'node:child_process'
import {fixtures, harnessHashes, summarize, type Measurement} from './run.ts'

const [directory, output] = process.argv.slice(2)
if (!directory || !output) throw new Error('usage: bun research/security/mutants/collect.ts <boat-output-dir> <measurement.json>')
const rows: Measurement[] = []
for (const file of readdirSync(directory).filter(f => f.endsWith('.log')).sort()) {
  for (const line of readFileSync(join(directory, file), 'utf8').split('\n')) {
    if (line.startsWith('MUTATION_RESULT ')) rows.push(JSON.parse(line.slice('MUTATION_RESULT '.length)) as Measurement)
  }
}
rows.sort((a, b) => a.fixture.localeCompare(b.fixture))
assert.deepEqual(rows.map(r => r.fixture), fixtures, 'complete corpus, no missing or duplicate receipts')
for (const row of rows) assert.deepEqual(row.harness, harnessHashes(), 'all workers measured the current harness')
const base = spawnSync('git', ['rev-parse', 'HEAD'], {encoding: 'utf8'})
assert.equal(base.status, 0, 'record the local base commit')
const document = {schema: 1, baseCommit: base.stdout.trim(), scope: 'owned synthetic modules, not upstream CVE recall',
  configuration: {msPerLaw: 8000, security: true, propose: false, vmType: 'large', cpu: 2, isolated: true},
  summary: summarize(rows), rows}
writeFileSync(output, JSON.stringify(document, null, 2) + '\n')
console.log(JSON.stringify(document.summary))
