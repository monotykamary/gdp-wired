// Iteration-only census formatter, NOT Lane D's authoritative final gate.
import {existsSync, readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
type Record = {id: string, count: number, canonical: string[], wallMs: number}
type Pair = {baseline: {queries: number, records: Record[]}, candidate: {queries: number, records: Record[]}}
const [output, candidateSHA, baselineSHA, ...dirs] = process.argv.slice(2)
if (!output || !candidateSHA || !baselineSHA || !dirs.length) throw Error('output candidateSHA baselineSHA dirs... required')
const jobs = JSON.parse(readFileSync('research/track-gen/t16-audit-generation-jobs.json', 'utf8')) as {name: string}[]
if (jobs.length !== 87 || new Set(jobs.map(j => j.name)).size !== 87) throw Error('expected 87 distinct census jobs')
const hash = (value: unknown) => createHash('sha256').update(JSON.stringify(value)).digest('hex')
const missing: string[] = [], failed: {name: string, source: string, reason: string}[] = []
const rows: {name: string, source: string, id: string, repeat: number, cpu: string, baseline: number, candidate: number, baselineHash: string, candidateHash: string, identical: boolean, baselineMs: number, candidateMs: number}[] = []
for (const {name} of jobs) {
  const match = /^generation-(.+)-([123])$/.exec(name)
  if (!match) throw Error('bad census job name: ' + name)
  const id = match[1]!, repeat = Number(match[2])
  let found = false
  for (const dir of dirs) {
    const source = join(dir, name + '.log')
    if (!existsSync(source)) continue
    try {
      const text = readFileSync(source, 'utf8'), marker = text.match(/^T13_PAIR_GZIP_BASE64 (\S+)$/m)
      const summary = readFileSync(join(dir, 'summary.tsv'), 'utf8').split('\n').find(l => l.split('\t')[0] === name)?.split('\t')
      if (summary?.[1] !== '0' || !marker) throw Error('missing successful receipt or complete pair payload')
      if (!text.includes(`ITERATION_REVISIONS candidate=${candidateSHA} baseline=${baselineSHA}\n`)) throw Error('revision mismatch')
      const pair = JSON.parse(gunzipSync(Buffer.from(marker[1]!, 'base64')).toString()) as Pair
      if (pair.baseline.queries || pair.candidate.queries) throw Error('generation ran proof queries')
      if (pair.baseline.records.length !== 1 || pair.candidate.records.length !== 1) throw Error('not one paired protocol')
      const b = pair.baseline.records[0]!, c = pair.candidate.records[0]!
      if (b.id !== id || c.id !== id || b.count !== b.canonical.length || c.count !== c.canonical.length) throw Error('record identity/count mismatch')
      const cpu = text.match(/^T14_CPU_MODEL (.+)$/m)?.[1]
      if (!cpu) throw Error('missing CPU label')
      const baselineHash = hash(b.canonical), candidateHash = hash(c.canonical)
      rows.push({name, source, id, repeat, cpu, baseline: b.count, candidate: c.count, baselineHash, candidateHash, identical: baselineHash === candidateHash, baselineMs: b.wallMs, candidateMs: c.wallMs})
      found = true; break
    } catch (e) { failed.push({name, source, reason: e instanceof Error ? e.message : String(e)}) }
  }
  if (!found) missing.push(name)
}
const regressions = rows.filter(r => r.id !== 'mldr' && !r.identical)
const result = {scope: 'iteration only, not a final gate', candidateSHA, baselineSHA, complete: rows.length, expected: 87, missing, regressions, failedReceipts: failed, rows}
writeFileSync(output, JSON.stringify(result, null, 2) + '\n')
console.log(JSON.stringify({complete: rows.length, missing, regressions: regressions.map(r => r.name), mldr: rows.filter(r => r.id === 'mldr')}, null, 2))
if (missing.length || regressions.length) process.exitCode = 1
