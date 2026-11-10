// Run on Boat for completed campaign logs containing --emit-cases.
import {readFileSync} from 'node:fs'
import {FAMILIES} from './model.ts'
const files = process.argv.slice(2)
if (!files.length) throw new Error('usage: aggregate.ts LOG...')
const hashes = new Set<string>(), seen = new Set<string>(), findings: unknown[] = [], blocked: unknown[] = []
const byRevision: Record<string, {cases: number, extracted: number, laws: number, proven: number, kernelProven: number, rows: number, findings: number, blocked: number, falseRejections: number, unsafeVerdicts: number, errors: number, families: Record<string, number>, acceptedTags: Record<string, number>, nontrivialProvenTags: Record<string, number>}> = {}
for (const file of files) {
  const lines = readFileSync(file, 'utf8').split('\n'), head = lines.find(l => l.startsWith('CLEAN_CHECKOUT_HEAD '))?.slice(20)
  if (!head) throw new Error(`missing exact target identity: ${file}`)
  const summaries = lines.filter(l => l.startsWith('FUZZ_SUMMARY ')).map(l => JSON.parse(l.slice(13)))
  if (summaries.length !== 1) throw new Error(`expected one terminal summary: ${file}`)
  const s = summaries[0], rows = lines.filter(l => l.startsWith('FUZZ_CASE ')).map(l => JSON.parse(l.slice(10)))
  if (s.replay !== 'default' || !s.generatorHash || rows.length !== s.generated || s.generated + s.errors !== s.count) throw new Error(`invalid default-replay receipt: ${file}`)
  hashes.add(s.generatorHash)
  const total = byRevision[head] ??= {cases: 0, extracted: 0, laws: 0, proven: 0, kernelProven: 0, rows: 0, findings: 0, blocked: 0, falseRejections: 0, unsafeVerdicts: 0, errors: 0, families: {}, acceptedTags: {}, nontrivialProvenTags: {}}
  total.errors += s.errors
  let found = 0, proven = 0, kernel = 0, checked = 0, blockedCount = 0, rejected = 0, unsafe = 0
  for (const row of rows) {
    const identity = `${head}:${row.id}`
    if (seen.has(identity)) throw new Error(`duplicate case: ${identity}`)
    seen.add(identity); total.cases++; total.extracted += Number(row.extracted)
    total.families[row.family] = (total.families[row.family] ?? 0) + 1
    if (row.extracted) for (const tag of row.tags) total.acceptedTags[tag] = (total.acceptedTags[tag] ?? 0) + 1
    for (const law of row.laws) {
      total.laws++
      if (law.native) { kernel++; checked += law.native.checked; total.kernelProven++; total.rows += law.native.checked }
      if (law.status === 'FINDING' || law.status === 'proven-native-valid') { proven++; total.proven++; if (law.nontrivial) for (const tag of row.tags) total.nontrivialProvenTags[tag] = (total.nontrivialProvenTags[tag] ?? 0) + 1 }
      const item = {revision: head, id: row.id, family: row.family, source: row.source, law}
      if (law.status === 'FINDING') { found++; total.findings++; findings.push(item) }
      if (law.status === 'BLOCKED_FINDING') { blockedCount++; total.blocked++; blocked.push(item) }
      if (law.status === 'FALSE_REJECTION') { rejected++; total.falseRejections++ }
      if (law.status === 'UNSAFE_VERDICT') { unsafe++; total.unsafeVerdicts++ }
    }
  }
  if (found !== s.findings || proven !== s.proven || kernel !== s.kernelProven || checked !== s.nativeCheckedRows || blockedCount !== s.blockedFindings || rejected !== s.falseRejections || unsafe !== s.unsafeVerdicts) throw new Error(`counter mismatch: ${file}`)
}
if (hashes.size !== 1) throw new Error('mixed generator versions')
for (const [revision, total] of Object.entries(byRevision)) if (FAMILIES.some(f => !total.families[f])) throw new Error(`missing generated families: ${revision}`)
console.log('FUZZ_AGGREGATE ' + JSON.stringify({generatorHash: [...hashes][0], files, byRevision, findings, blocked}))
