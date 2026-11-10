// Aggregate already-completed per-protocol generation receipts, not proof work.
import {readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const dir = process.argv[2]!, output = process.argv[3]!
const digest = (x: unknown) => createHash('sha256').update(JSON.stringify(x)).digest('hex')
const records = readdirSync(dir).filter(f => /^gen-.+-[123]\.log$/.test(f)).map(file => {
  const text = readFileSync(join(dir, file), 'utf8'), packed = text.match(/T13_PAIR_GZIP_BASE64 (\S+)/)?.[1]
  if (!packed) throw Error(`missing complete pair: ${file}`)
  const raw = JSON.parse(gunzipSync(Buffer.from(packed, 'base64')).toString())
  if (raw.baseline.records.length !== 1 || raw.candidate.records.length !== 1 || raw.baseline.queries || raw.candidate.queries) throw Error(`not one generation-only pair: ${file}`)
  const b = raw.baseline.records[0], c = raw.candidate.records[0]
  if (b.id !== c.id) throw Error(`mismatched protocol: ${file}`)
  return {id: b.id, repeat: Number(file.match(/-([123])\.log$/)![1]), source: join(dir, file), baseline: b.count, candidate: c.count, baselineHash: digest(b.canonical), candidateHash: digest(c.canonical), identical: JSON.stringify(b.canonical) === JSON.stringify(c.canonical), baselineMs: b.wallMs, candidateMs: c.wallMs, candidateProfile: c.cprof, ...(b.id === 'mldr' ? {names: c.names} : {})}
})
const ids = [...new Set(records.map(r => r.id))]
if (ids.length !== 29 || ids.some(id => records.filter(r => r.id === id).length !== 3) || records.length !== 87) throw Error('incomplete 29 x 3 census')
const changed = records.filter(r => !r.identical).map(r => `${r.id}/${r.repeat}`)
const result = {records, changed, protocols: ids.length, pairs: records.length, queries: 0}
writeFileSync(output, JSON.stringify(result, null, 2) + '\n')
console.log(JSON.stringify({protocols: ids.length, pairs: records.length, queries: 0, changed, mldr: records.filter(r => r.id === 'mldr').map(r => ({repeat: r.repeat, baseline: r.baseline, candidate: r.candidate, candidateMs: r.candidateMs, hash: r.candidateHash}))}, null, 2))
if (records.some(r => r.id !== 'mldr' && !r.identical)) throw Error('non-MLDR generation regression')
