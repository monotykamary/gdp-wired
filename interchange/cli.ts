#!/usr/bin/env node
// gdp-wired-check: interchange documents in, the kernel's verdict on each claim out.
//   gdp-wired-check [--json] [--goals <out.json>] <file.json>... (or - for standard input)
// Each file: `accepted` or `refused` with the kind and the kernel's entry point that decided it, then each claim (a
// law, a step law, a node, a goal) and why a refused one is. Exit 0 when every claim of every file is accepted, 1 when
// one is refused (or a file isn't a document), 2 on bad use.
// --goals: the first file's goals, each with its tree, written as a `goals` document (the tree part of the check, for a
// second checker: interchange/py/check.py).
// Shipped as the package's `gdp-wired-check` bin; built alone (interchange/build.ts) as one file, an executable and a
// WebAssembly module. Node's modules are reached at run time (as core/cli.ts reaches them), so the library's build
// carries no Node types.
import {type Report, checkDocument, decidedBy, goalsOf} from './check.ts'
import {fromInterchange, toInterchange} from './format.ts'

type FS = {readFileSync: (p: string | number, e: string) => string, writeFileSync: (p: string, s: string) => void}
const proc = (globalThis as unknown as {process: {argv: string[], exit: (c: number) => never, stdout: {write: (s: string) => void}, stderr: {write: (s: string) => void}, getBuiltinModule: (id: string) => unknown}}).process
const fs = proc.getBuiltinModule('node:fs') as FS

const args = proc.argv.slice(2), json = args.includes('--json'), gi = args.indexOf('--goals'), goalsOut = gi >= 0 ? args[gi + 1] : undefined
const files = args.filter((a, i) => !a.startsWith('--') && (gi < 0 || i !== gi + 1))
if (!files.length || (gi >= 0 && !goalsOut)) {
  proc.stderr.write('usage: gdp-wired-check [--json] [--goals <out.json>] <file.json>... (- reads standard input)\n')
  proc.exit(2)
}
const read = (f: string): unknown => JSON.parse(f === '-' ? fs.readFileSync(0, 'utf8') : fs.readFileSync(f, 'utf8'))
const out: {file: string, report: Report}[] = []
for (const file of files) {
  let report: Report
  try { report = checkDocument(read(file)) } catch (e) { report = {accepted: false, claims: [], malformed: `not JSON: ${e instanceof Error ? e.message : String(e)}`} }
  out.push({file, report})
}
if (goalsOut) fs.writeFileSync(goalsOut, JSON.stringify(toInterchange(goalsOf(fromInterchange(read(files[0]!))))))
const say = (s: string) => proc.stdout.write(`${s}\n`)
if (json) say(JSON.stringify(out.length === 1 ? out[0]!.report : out))
else for (const {file, report} of out) {
  say(`${file}: ${report.accepted ? 'accepted' : 'refused'}${report.kind ? ` (${report.kind}, by ${decidedBy[report.kind as keyof typeof decidedBy] ?? 'the kernel'})` : ''}${report.malformed ? `: ${report.malformed}` : ''}`)
  for (const c of report.claims) say(`  ${c.accepted ? 'accepted' : 'refused '}  ${c.name}${c.why ? `: ${c.why}` : ''}`)
}
proc.exit(out.every(o => o.report.accepted) ? 0 : 1)
