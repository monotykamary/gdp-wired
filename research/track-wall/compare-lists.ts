// Two generation receipts (research/track-gen/t13-generation.ts stdout): per protocol, whether the canonical law lists
// are byte-identical, with counts and phase walls. Reads only the receipts it is given.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
const load = (file: string) => {
  const m = /T13_DATA_GZIP_BASE64 (\S+)/.exec(readFileSync(file, 'utf8'))
  if (!m) throw Error(`${file}: no generation receipt`)
  return JSON.parse(gunzipSync(Buffer.from(m[1]!, 'base64')).toString()) as {queries: number, records: {id: string, count: number, canonical: string[], wallMs: number, phases: Record<string, number>}[]}
}
const [a, b] = [load(process.argv[2]!), load(process.argv[3]!)]
for (const ra of a.records) {
  const rb = b.records.find(r => r.id === ra.id)
  const same = !!rb && JSON.stringify(ra.canonical) === JSON.stringify(rb.canonical)
  console.log(JSON.stringify({id: ra.id, identical: same, baseCount: ra.count, candidateCount: rb?.count, baseWallMs: Math.round(ra.wallMs), candidateWallMs: rb && Math.round(rb.wallMs), basePhases: ra.phases, candidatePhases: rb?.phases, queries: [a.queries, b.queries]}))
}
