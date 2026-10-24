#!/usr/bin/env node
// gdp-wired-check: interchange documents in, the kernel's verdict on each claim out.
//   gdp-wired-check [--json] [--goals <out.json>] <file.json>... (or - for standard input)
// Each file: `accepted` or `refused`, with each claim (a law, a step law, a node, a goal) and why a refused one is.
// Exit 0 when every claim of every file is accepted, 1 when one is refused (or a file isn't a document), 2 on bad use.
// --goals: the first file's goals, each with its tree, written as a `goals` document (the tree part of the check, for a
// second checker: interchange/py/check.py).
import {readFileSync, writeFileSync} from 'node:fs'
import {type Report, checkDocument, goalsOf} from './check.ts'
import {fromInterchange, toInterchange} from './format.ts'

const args = process.argv.slice(2), json = args.includes('--json'), gi = args.indexOf('--goals'), goalsOut = gi >= 0 ? args[gi + 1] : undefined
const files = args.filter((a, i) => !a.startsWith('--') && (gi < 0 || i !== gi + 1))
if (!files.length || (gi >= 0 && !goalsOut)) {
  console.error('usage: gdp-wired-check [--json] [--goals <out.json>] <file.json>... (- reads standard input)')
  process.exit(2)
}
const read = (f: string): unknown => JSON.parse(f === '-' ? readFileSync(0, 'utf8') : readFileSync(f, 'utf8'))
const out: {file: string, report: Report}[] = []
for (const file of files) {
  let report: Report
  try { report = checkDocument(read(file)) } catch (e) { report = {accepted: false, claims: [], malformed: `not JSON: ${e instanceof Error ? e.message : String(e)}`} }
  out.push({file, report})
}
if (goalsOut) writeFileSync(goalsOut, JSON.stringify(toInterchange(goalsOf(fromInterchange(read(files[0]!))))))
if (json) console.log(JSON.stringify(out.length === 1 ? out[0]!.report : out))
else for (const {file, report} of out) {
  console.log(`${file}: ${report.accepted ? 'accepted' : 'refused'}${report.kind ? ` (${report.kind})` : ''}${report.malformed ? `: ${report.malformed}` : ''}`)
  for (const c of report.claims) console.log(`  ${c.accepted ? 'accepted' : 'refused '}  ${c.name}${c.why ? `: ${c.why}` : ''}`)
}
process.exit(out.every(o => o.report.accepted) ? 0 : 1)
