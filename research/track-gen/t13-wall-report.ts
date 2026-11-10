// Decode receipts only; no model execution or proving.
import {readFileSync, writeFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const dir = process.argv[2]!, output = process.argv[3]!
const pairs = [1, 2, 3].map(repeat => {
  const log = readFileSync(`${dir}/strict-pair-${repeat}.log`, 'utf8')
  const sides = ['BASELINE', 'CANDIDATE'].map(side => {
    const text = log.split(`=== ${side} ===`)[1]!.split('=== ')[0]!, name = side.toLowerCase()
    const code = Number(text.match(new RegExp(`T13_EXIT ${name} (\\d+)`))![1])
    const seconds = Number(text.match(new RegExp(`STRICT_PROCESS_SECONDS ${name} ([\\d.]+)`))![1])
    const line = text.split('\n').find(l => l.startsWith('{"id":"mldr"'))
    const result = line ? JSON.parse(line).search : undefined
    const tries = text.split('\n').filter(l => l.startsWith('counts: try ')).map(l => l.replace(/ wall \d+ \[.*\] -> /, ' -> '))
    return {side: name, code, seconds, result, tries}
  })
  const [b, c] = sides
  let equalPrefix = 0
  while (equalPrefix < Math.min(b!.tries.length, c!.tries.length) && b!.tries[equalPrefix] === c!.tries[equalPrefix]) equalPrefix++
  if (c!.code !== 0 || c!.seconds > 60 || !c!.result || c!.result.ms > 60_000) throw Error(`strict candidate failed: ${repeat}`)
  return {repeat, sides, equalPrefix, firstDifference: [b!.tries[equalPrefix], c!.tries[equalPrefix]]}
})
type Record = {id: string, count: number, canonical: string[], wallMs: number}
type Receipt = {queries: number, records: Record[]}
const parts = ['rest', 'switch', 'switch-i4'].map(name => {
  const text = readFileSync(`${dir}/generation-${name}.log`, 'utf8')
  return JSON.parse(gunzipSync(Buffer.from(text.match(/T13_PAIR_GZIP_BASE64 (\S+)/)![1]!, 'base64')).toString()) as {baseline: Receipt, candidate: Receipt}
})
const baseline = parts.flatMap(p => p.baseline.records), candidate = parts.flatMap(p => p.candidate.records)
if (baseline.length !== 29 || candidate.length !== 29 || new Set(baseline.map(r => r.id)).size !== 29 || new Set(candidate.map(r => r.id)).size !== 29 || parts.some(p => p.baseline.queries || p.candidate.queries)) throw Error('incomplete generation census')
const digest = (xs: string[]) => createHash('sha256').update(JSON.stringify(xs)).digest('hex')
const generation = baseline.map(b => {
  const c = candidate.find(r => r.id === b.id)!
  if (!c || JSON.stringify(b.canonical) !== JSON.stringify(c.canonical)) throw Error(`changed generation: ${b.id}`)
  return {id: b.id, count: c.count, hash: digest(c.canonical), baselineMs: b.wallMs, candidateMs: c.wallMs}
})
writeFileSync(output, JSON.stringify({baseline: '189eefcd', pairs, generation}, null, 2) + '\n')
console.log(JSON.stringify({pairs: pairs.map(p => ({repeat:p.repeat, sides:p.sides.map(({tries, ...rest})=>({...rest, attempts:tries.length})), equalPrefix:p.equalPrefix, firstDifference:p.firstDifference})), generation:{protocols:generation.length, changed:0, mldr:generation.find(r=>r.id==='mldr')}}, null, 2))
