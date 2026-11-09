// Join small projection records to exact checker-only receipts; never replay a
// proof here or treat conditional acceptance as a complete-family gate.
import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync, writeFileSync} from 'node:fs'
import {basename, join} from 'node:path'

type FocusRecord = {name: string, side: string, tag: string, checked: boolean, units: number, wallMs: number, results: unknown, [key: string]: unknown}
type Projection = {range: FocusRecord[], early: FocusRecord[], followup: FocusRecord[], [key: string]: unknown}
type AuditSource = {path: string, text: string, exitCode: number}
export function linkFocusAudits(summary: Projection, sources: AuditSource[]) {
  const records = new Map<string, Record<string, unknown>>()
  for (const source of sources) {
    assert.equal(source.exitCode, 0, `failed audit: ${source.path}`)
    const logSha256 = createHash('sha256').update(source.text).digest('hex')
    let input: string | undefined
    for (const line of source.text.split('\n')) {
      if (line.startsWith('INPUT=')) { input = basename(line.slice(6)); continue }
      let record: Record<string, unknown>
      try { record = JSON.parse(line) } catch { continue }
      if (record.conditional !== true) continue
      assert(typeof input === 'string' && input.endsWith('.json.gz'), 'audit record has no input')
      assert(!records.has(input), `duplicate audit: ${input}`)
      assert.equal(record.familyVerified, true, input)
      assert.equal(record.originalHarness, true, input)
      records.set(input, {...record, sourceLog: source.path, logSha256})
      input = undefined
    }
  }
  const rows = [...summary.range, ...summary.early, ...summary.followup]
  const key = (r: FocusRecord) => `${r.name}${r.side === 'run' ? '' : '-' + r.side}.json.gz`
  const expected = rows.map(key)
  assert.equal(new Set(expected).size, expected.length, 'duplicate projection arm')
  assert.deepEqual([...records.keys()].sort(), [...expected].sort(), 'audit roster differs')
  const link = (row: FocusRecord) => {
    const audit = records.get(key(row))!
    for (const field of ['tag', 'checked', 'units', 'wallMs', 'results'] as const) assert.deepEqual(audit[field], row[field], `${key(row)}: ${field}`)
    return {...row, audit: {sourceLog: audit.sourceLog, logSha256: audit.logSha256, checked: audit.checked, familyVerified: true, conditional: true}}
  }
  const checked = rows.filter(r => r.checked).length
  return {...summary, range: summary.range.map(link), early: summary.early.map(link), followup: summary.followup.map(link),
    independentAuditPending: false, originalFamilyVerified: true, gateGreen: false,
    independentAudit: {outcomes: rows.length, checked, unknown: rows.length - checked}}
}

if (import.meta.main) {
  const [file, ...dirs] = process.argv.slice(2)
  if (!file || !dirs.length) throw Error('PROJECTION AUDIT_DIR... required')
  const summary: Projection = JSON.parse(readFileSync(file, 'utf8'))
  assert.equal([...summary.range, ...summary.early, ...summary.followup].length, 13)
  const sources = dirs.map(dir => {
    const statuses = readFileSync(join(dir, 'summary.tsv'), 'utf8').trim().split('\n').map(line => line.split('\t'))
    const audit = statuses.find(([name]) => name === 'audit')
    assert(audit, `missing audit status: ${dir}`)
    return {path: join(dir, 'audit.log'), text: readFileSync(join(dir, 'audit.log'), 'utf8'), exitCode: Number(audit[1])}
  })
  const result = linkFocusAudits(summary, sources)
  writeFileSync(file, JSON.stringify(result, null, 2) + '\n')
  console.log(JSON.stringify(result.independentAudit))
}
