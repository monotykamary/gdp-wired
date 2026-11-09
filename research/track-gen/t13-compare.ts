import {readFileSync} from 'node:fs'
import {gzipSync, gunzipSync} from 'node:zlib'
type Record = {id: string, count: number, canonical: string[], wallMs: number, phases: {[k: string]: number}}
const read = (path: string): {queries: number, records: Record[]} => JSON.parse(gunzipSync(Buffer.from(readFileSync(path, 'utf8').match(/T13_DATA_GZIP_BASE64 (\S+)/)![1]!, 'base64')).toString())
const baseline = read(process.argv[2]!), candidate = read(process.argv[3]!)
const comparisons = baseline.records.map(b => {
  const c = candidate.records.find(c => c.id === b.id)!
  return {id: b.id, baseline: b.count, candidate: c.count, identical: JSON.stringify(b.canonical) === JSON.stringify(c.canonical), baselineWallMs: b.wallMs, candidateWallMs: c.wallMs, baselinePhases: b.phases, candidatePhases: c.phases}
})
console.log(JSON.stringify({baselineQueries: baseline.queries, candidateQueries: candidate.queries, comparisons}))
console.log('T13_PAIR_GZIP_BASE64 ' + gzipSync(JSON.stringify({baseline, candidate})).toString('base64'))
if (baseline.queries || candidate.queries || comparisons.some(c => c.id !== 'mldr' && !c.identical)) throw Error('T-13.1: other-port regression')
