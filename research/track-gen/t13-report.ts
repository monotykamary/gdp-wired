// Receipt summarizer only; no model generation or proof work.
import {readFileSync, writeFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const dir = process.argv[2]!, output = process.argv[3]!, repeat2 = process.argv[4]
const digest = (x: unknown) => createHash('sha256').update(JSON.stringify(x)).digest('hex')
const pairs = [1, 2, 3].map(repeat => {
  const source = `${repeat === 2 && repeat2 ? repeat2 : dir}/generation-pair-${repeat}.log`
  const log = readFileSync(source, 'utf8')
  const raw = JSON.parse(gunzipSync(Buffer.from(log.match(/T13_PAIR_GZIP_BASE64 (\S+)/)![1]!, 'base64')).toString()) as {baseline: {queries: number, records: {id: string, count: number, canonical: string[], names: string[], wallMs: number, phases: object}[]}, candidate: {queries: number, records: {id: string, count: number, canonical: string[], names: string[], wallMs: number, phases: object}[]}}
  const ids = raw.baseline.records.map(r => r.id)
  if (ids.length !== 29 || new Set(ids).size !== 29 || raw.candidate.records.length !== 29 || new Set(raw.candidate.records.map(r => r.id)).size !== 29 || raw.candidate.records.some(r => !ids.includes(r.id))) throw Error(`incomplete census: ${source}`)
  return {repeat, source, queries: [raw.baseline.queries, raw.candidate.queries], records: raw.baseline.records.map(b => {
    const c = raw.candidate.records.find(c => c.id === b.id)!
    return {id: b.id, baseline: b.count, candidate: c.count, baselineHash: digest(b.canonical), candidateHash: digest(c.canonical), identical: JSON.stringify(b.canonical) === JSON.stringify(c.canonical), baselineMs: b.wallMs, candidateMs: c.wallMs, baselinePhases: b.phases, candidatePhases: c.phases, ...(b.id === 'mldr' ? {names: c.names} : {})}
  })}
})
writeFileSync(output, JSON.stringify({pairs}, null, 2) + '\n')
for (const b of pairs[0]!.records) {
  const rows = pairs.map(p => p.records.find(r => r.id === b.id)!)
  console.log(`| ${b.id} | ${b.baseline} → ${b.candidate} | ${rows.every(r => r.identical) ? 'identical ×3' : 'changed'} | ${rows.map(r => (r.baselineMs / 1000).toFixed(2)).join(', ')} | ${rows.map(r => (r.candidateMs / 1000).toFixed(2)).join(', ')} |`)
}
if (pairs.some(p => p.queries.some(Boolean) || p.records.some(r => r.id !== 'mldr' && !r.identical))) throw Error('T-13 receipt regression')
