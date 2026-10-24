// The capture jobs' logs (interchange/suite-jobs.ts) summed: per kind, the documents, the kernel's answers and each
// checker's agreement with them; the tampered twins; the capture's identity checks and what was outside the format; the
// jobs whose own command failed under the capture; the trusted files' blob ids each job built from.
//   bun interchange/aggregate.ts <run dir> [--md]
import {readFileSync, readdirSync} from 'node:fs'
import {join} from 'node:path'

const dir = process.argv[2]
if (!dir) { console.error('usage: aggregate.ts <run dir>'); process.exit(2) }
type Row = Record<string, number>
const add = (a: Row, b: Row) => { for (const [k, v] of Object.entries(b)) if (typeof v === 'number') a[k] = (a[k] ?? 0) + v }
const byKind: Record<string, Row> = {}, tampered: Record<string, Row> = {}, seen: Row = {}, outside: Row = {}
let docs = 0, twins = 0, acceptedTampers = 0, idOk = 0, idFailed = 0, valid = 0, invalid = 0
const disagreements: string[] = [], failedJobs: string[] = [], missing: string[] = [], blobs = new Set<string>(), outsideWhy = new Set<string>(), idFirst: string[] = [], schemaFirst: string[] = []
const ms: Row = {}
for (const f of readdirSync(dir).filter(f => f.endsWith('.log')).sort()) {
  const text = readFileSync(join(dir, f), 'utf8'), job = f.replace(/\.log$/, '')
  for (const m of text.matchAll(/^(kernel\/kernel\.ts|kernel\/cyclic\.ts|core\/check\.ts): ([0-9a-f]{40})/gm)) blobs.add(`${m[1]} ${m[2]}`)
  const exit = /JOB EXIT (\d+)/.exec(text)
  if (exit && exit[1] !== '0') failedJobs.push(`${job} (${exit[1]})`)
  const at = text.indexOf('SUMMARY-JSON')
  if (at < 0) { missing.push(job); continue }
  let s: {documents: number, tampered: number, byKind: Record<string, Row>, tamperedBy: Record<string, Row>, acceptedTampersCount: number, disagreements: string[],
    capture: {seen: Row, identityOk: number, identityFailed: number, identityFirst: string[], outside: Row, outsideWhy: string[]}, schema?: {valid: number, invalid: number, first: string[]}, ms: Row}
  try { s = JSON.parse(text.slice(at + 'SUMMARY-JSON'.length).replace(/\n--- stderr ---[\s\S]*$/, '').trim()) } catch { missing.push(`${job} (unreadable summary)`); continue }
  docs += s.documents; twins += s.tampered; acceptedTampers += s.acceptedTampersCount
  for (const [k, r] of Object.entries(s.byKind)) add(byKind[k] ??= {}, r)
  for (const [k, r] of Object.entries(s.tamperedBy)) add(tampered[k] ??= {}, r)
  add(seen, s.capture.seen); add(outside, s.capture.outside); add(ms, s.ms)
  idOk += s.capture.identityOk; idFailed += s.capture.identityFailed
  for (const x of s.capture.identityFirst) if (idFirst.length < 10) idFirst.push(`${job}: ${x}`)
  for (const w of s.capture.outsideWhy) outsideWhy.add(w.replace(/\[\d+\]/g, '[i]'))
  for (const d of s.disagreements) disagreements.push(`${job}: ${d}`)
  if (s.schema) { valid += s.schema.valid; invalid += s.schema.invalid; for (const x of s.schema.first) if (schemaFirst.length < 10) schemaFirst.push(`${job}: ${x}`) }
}
const cols = ['docs', 'kernelAccepted', 'kernelRefused', 'tsAgree', 'malformed', 'cliAgree', 'wasmRun', 'wasmAgree', 'goals', 'pyRun', 'pyAgree']
const total: Row = {}
for (const r of Object.values(byKind)) add(total, r)
console.log(`${dir}\njobs with a summary: ${readdirSync(dir).filter(f => f.endsWith('.log')).length - missing.length}; without: ${missing.length ? missing.join(', ') : 'none'}`)
console.log(`trusted files built from: ${[...blobs].join('; ')}`)
console.log(`jobs whose command failed under the capture: ${failedJobs.length ? failedJobs.join(', ') : 'none'}\n`)
console.log(`kind          ${cols.join('  ')}`)
for (const [k, r] of [...Object.entries(byKind).sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)), ['TOTAL', total] as const]) console.log(`${k.padEnd(13)} ${cols.map(c => String(r[c] ?? 0).padStart(c.length)).join('  ')}`)
console.log(`\ntampered twins: ${twins}`)
const tcols = ['docs', 'tsRefused', 'cliAgree', 'wasmRun', 'wasmAgree', 'goals', 'pyRun', 'pyAgree']
console.log(`${'tamper'.padEnd(38)} ${tcols.join('  ')}`)
for (const [k, r] of Object.entries(tampered)) console.log(`${k.padEnd(38)} ${tcols.map(c => String(r[c] ?? 0).padStart(c.length)).join('  ')}`)
console.log(`twins the checker accepts (the tamper left a proof): ${acceptedTampers}`)
console.log(`\ncapture: seen ${JSON.stringify(seen)}\nidentity (read back in the capturing process): ${idOk} ok, ${idFailed} failed${idFirst.length ? `\n  ${idFirst.join('\n  ')}` : ''}`)
console.log(`outside the format (not written; the kernel's answer beside): ${JSON.stringify(outside)}${outsideWhy.size ? `\n  ${[...outsideWhy].slice(0, 12).join('\n  ')}` : ''}`)
console.log(`schema: ${valid} valid, ${invalid} invalid${schemaFirst.length ? `\n  ${schemaFirst.join('\n  ')}` : ''}`)
console.log(`disagreements: ${disagreements.length}${disagreements.length ? `\n  ${disagreements.slice(0, 40).join('\n  ')}` : ''}`)
console.log(`ms (summed): ${JSON.stringify(ms)}`)
