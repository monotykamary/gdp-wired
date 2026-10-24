// The captured certificates (interchange/capture.ts) checked again, away from the process that made them, and compared
// with the kernel's answer there (each document's meta.capture.kernel):
//   - the checker in this process (checkDocument, which reads the document back and guards the reading);
//   - the bundled CLI (interchange/dist/gdp-wired-check.js, built by interchange/build.ts), in batches;
//   - the WebAssembly module (--wasm "<runner>": e.g. "wasmtime run" or "wasmer run", reading the document on stdin);
//   - the second checker (--python <python3>: interchange/py/check.py) on each certificate's goals and trees, against
//     the kernel's check of each goal here.
// With --tamper, each accepted document is also tampered three ways (a leaf's last step dropped, a multiplier raised, a
// split's constant moved), and each twin checked by all of them. Prints a summary; --out writes it as JSON.
// With --schema <python3> (with the jsonschema package), every document, twin and goals document against schema.json.
//   bun interchange/verify.ts <dir>... [--tamper] [--wasm "<runner>"] [--python python3] [--schema python3] [--out summary.json] [--keep <dir>]
import {mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync} from 'node:fs'
import {cpus, tmpdir} from 'node:os'
import {join} from 'node:path'
import {check} from '../kernel/kernel.ts'
import {checkDocument, goalsOf} from './check.ts'
import {type Document, type Json, fromInterchange, toInterchange} from './format.ts'

const argv = process.argv.slice(2), flag = (f: string) => { const i = argv.indexOf(f); return i >= 0 ? argv[i + 1] : undefined }
const valued = new Set(['--wasm', '--python', '--out', '--keep', '--schema'])
const dirs = argv.filter((a, i) => !a.startsWith('--') && !valued.has(argv[i - 1] ?? ''))
const tamper = argv.includes('--tamper'), wasm = flag('--wasm'), python = flag('--python'), outFile = flag('--out'), schemaPy = flag('--schema')
const here = import.meta.dir, bundle = join(here, 'dist', 'gdp-wired-check.js'), wasmModule = join(here, 'dist', 'gdp-wired-check.wasm')
const work = flag('--keep') ?? mkdtempSync(join(tmpdir(), 'gdp-verify-'))
mkdirSync(join(work, 'goals'), {recursive: true}); mkdirSync(join(work, 'tampered'), {recursive: true})

type Item = {file: string, kind: string, kernel: boolean | string | undefined, tampered?: string, ts?: boolean, malformed?: string, cli?: boolean, wasm?: boolean,
  goals?: {file: string, expect: boolean[]}, py?: boolean[]}
const items: Item[] = []
const asAnswer = (k: unknown): boolean | undefined => (k === true ? true : k === false || (typeof k === 'string' && k.startsWith('throws')) ? false : undefined)

// --- tampering, on the JSON: the first leaf (in document order) with two steps or more, the first combination, the
// first split ---------------------------------------------------------------------------------------------------------
type Edit = (x: Json) => boolean
const firstWhere = (x: Json | undefined, f: Edit): boolean => {
  if (Array.isArray(x)) return x.some(y => firstWhere(y, f))
  if (x && typeof x === 'object') { if (f(x)) return true; return Object.entries(x).some(([k, y]) => k !== 'meta' && k !== 'columns' && firstWhere(y, f)) }
  return false
}
const TAMPERS: [string, Edit][] = [
  ['a leaf\'s last step dropped', x => { const o = x as {leaf?: Json[]}; if (Array.isArray(o.leaf) && o.leaf.length >= 2) { o.leaf.pop(); return true } return false }],
  ['a combination\'s multiplier raised', x => { const o = x as {leaf?: Json[]}; const s = Array.isArray(o.leaf) ? o.leaf.find(y => Array.isArray(y) && y[0] === 'combine') as number[] | undefined : undefined; if (s) { s[3] = s[3]! + 1; return true } return false }],
  ['a split\'s constant moved', x => { const o = x as {split?: Json[]}; if (Array.isArray(o.split)) { o.split[0] = ((o.split[0] as number | null) ?? 0) + 1; return true } return false }],
]

// --- this process: the checker, each certificate's goals and the kernel's answer on each ---------------------------------
// (a directory the capture never made: the run handed the kernel nothing from its own bun processes)
const ls = (d: string) => { try { return readdirSync(d) } catch { return [] } }
const files = dirs.flatMap(d => ls(d).filter(f => f.endsWith('.json')).sort().map(f => join(d, f)))
const t0 = performance.now()
const expand = (it: Item, doc: unknown) => {
  try {
    const g = goalsOf(fromInterchange(doc))
    if (g.kind !== 'goals' || !g.goals.length) return
    const expect = g.goals.map(x => { try { return check(x.goal, x.tree) } catch { return false } })
    const file = join(work, 'goals', `${items.length}.json`)
    writeFileSync(file, JSON.stringify(toInterchange(g)))
    it.goals = {file, expect}
  } catch { /* outside the kernel's builders: the checker's answer covers it */ }
}
for (const file of files) {
  const doc = JSON.parse(readFileSync(file, 'utf8')) as Document
  const it: Item = {file, kind: String(doc.kind), kernel: (doc.meta as {capture?: {kernel?: boolean | string}} | undefined)?.capture?.kernel}
  const r = checkDocument(doc)
  it.ts = r.accepted
  if (r.malformed) it.malformed = r.malformed
  if (python) expand(it, doc)
  items.push(it)
  if (tamper && r.accepted) for (const [what, edit] of TAMPERS) {
    const twin = JSON.parse(JSON.stringify(doc)) as Document
    if (!firstWhere(twin as Json, edit)) continue
    twin.meta = {tamper: what, of: file}
    const tf = join(work, 'tampered', `${items.length}.json`)
    writeFileSync(tf, JSON.stringify(twin))
    const ti: Item = {file: tf, kind: String(doc.kind), kernel: undefined, tampered: what}
    const tr = checkDocument(twin)
    ti.ts = tr.accepted
    if (tr.malformed) ti.malformed = tr.malformed
    if (python) expand(ti, twin)
    items.push(ti)
  }
}
const tTs = performance.now() - t0

// --- the bundled CLI, in batches ------------------------------------------------------------------------------------------
const t1 = performance.now()
for (let i = 0; i < items.length; i += 100) {
  const batch = items.slice(i, i + 100)
  const r = Bun.spawnSync(['bun', bundle, '--json', ...batch.map(b => b.file)], {stdout: 'pipe', stderr: 'pipe'})
  const out = JSON.parse(r.stdout.toString()) as {file: string, report: {accepted: boolean}}[] | {accepted: boolean}
  const reports = Array.isArray(out) ? out.map(o => o.report) : [out]
  batch.forEach((b, j) => { b.cli = reports[j]?.accepted })
}
const tCli = performance.now() - t1

// --- the WebAssembly module, a process each, as many at once as there are cores ------------------------------------------
const t2 = performance.now()
if (wasm) {
  let next = 0
  const lane = async () => {
    for (;;) {
      const it = items[next++]
      if (!it) return
      const p = Bun.spawn(['sh', '-c', `${wasm} ${JSON.stringify(wasmModule)} < ${JSON.stringify(it.file)}`], {stdout: 'pipe', stderr: 'ignore'})
      const text = await new Response(p.stdout).text()
      await p.exited
      try { it.wasm = (JSON.parse(text.trim().split('\n').at(-1) ?? '') as {accepted: boolean}).accepted } catch { it.wasm = undefined }
    }
  }
  await Promise.all(Array.from({length: Math.max(1, cpus().length)}, lane))
}
const tWasm = performance.now() - t2

// --- the second checker, on the goals ---------------------------------------------------------------------------------------
const t3 = performance.now()
if (python) {
  const withGoals = items.filter(i => i.goals)
  for (let i = 0; i < withGoals.length; i += 50) {
    const batch = withGoals.slice(i, i + 50)
    const r = Bun.spawnSync([python, join(here, 'py', 'check.py'), '--json', ...batch.map(b => b.goals!.file)], {stdout: 'pipe', stderr: 'pipe'})
    const lines = r.stdout.toString().trim().split('\n')
    batch.forEach((b, j) => { try { b.py = (JSON.parse(lines[j] ?? '') as [string, boolean][]).map(x => x[1]) } catch { b.py = undefined } })
  }
}
const tPy = performance.now() - t3

// --- the schema ---------------------------------------------------------------------------------------------------------
const schema = {valid: 0, invalid: 0, first: [] as string[]}
if (schemaPy) {
  const all = [...items.map(i => i.file), ...items.flatMap(i => (i.goals ? [i.goals.file] : []))]
  for (let i = 0; i < all.length; i += 200) {
    const r = Bun.spawnSync([schemaPy, join(here, 'py', 'validate.py'), join(here, 'schema.json'), ...all.slice(i, i + 200)], {stdout: 'pipe', stderr: 'pipe'})
    try { const o = JSON.parse(r.stdout.toString()) as typeof schema; schema.valid += o.valid; schema.invalid += o.invalid; schema.first.push(...o.first) } catch { schema.first.push(`validate.py: ${r.stderr.toString().slice(0, 300)}`) }
  }
}

// --- the summary ------------------------------------------------------------------------------------------------------------
type Row = {docs: number, kernelAccepted: number, kernelRefused: number, tsAgree: number, malformed: number, cliAgree: number, wasmRun: number, wasmAgree: number, goals: number, pyRun: number, pyAgree: number}
const row = (): Row => ({docs: 0, kernelAccepted: 0, kernelRefused: 0, tsAgree: 0, malformed: 0, cliAgree: 0, wasmRun: 0, wasmAgree: 0, goals: 0, pyRun: 0, pyAgree: 0})
const byKind: Record<string, Row> = {}, tampered: Record<string, Row & {tsRefused: number}> = {}
const disagree: string[] = [], acceptedTampers: string[] = []
for (const it of items) {
  const ref = it.tampered ? it.ts : asAnswer(it.kernel)
  const r = it.tampered ? (tampered[it.tampered] ??= {...row(), tsRefused: 0}) : (byKind[it.kind] ??= row())
  r.docs++
  if (ref === true) r.kernelAccepted++
  if (ref === false) r.kernelRefused++
  if (it.malformed) r.malformed++
  if (!it.tampered && it.ts === ref) r.tsAgree++
  if (it.tampered && it.ts === false) (r as Row & {tsRefused: number}).tsRefused++
  if (it.tampered && it.ts === true) acceptedTampers.push(`${it.file} (${it.tampered})`)
  if (it.cli === ref) r.cliAgree++
  if (wasm && it.wasm !== undefined) { r.wasmRun++; if (it.wasm === ref) r.wasmAgree++ }
  if (it.goals) {
    r.goals += it.goals.expect.length
    if (it.py) { r.pyRun += it.py.length; r.pyAgree += it.py.filter((x, j) => x === it.goals!.expect[j]).length }
  }
  const bad = [!it.tampered && it.ts !== ref && 'ts', it.cli !== ref && 'cli', wasm && it.wasm !== undefined && it.wasm !== ref && 'wasm', it.py && it.py.some((x, j) => x !== it.goals!.expect[j]) && 'python'].filter(Boolean)
  if (bad.length && disagree.length < 40) disagree.push(`${it.file}: ${bad.join(', ')} (reference ${ref}${it.malformed ? `, malformed: ${it.malformed}` : ''})`)
}
// The capture's own summaries: what it took, what it couldn't write (outside the format) and its identity checks.
const caps = dirs.flatMap(d => ls(d).filter(f => f.endsWith('.summary')).map(f => JSON.parse(readFileSync(join(d, f), 'utf8')) as {seen: Record<string, number>, kept: Record<string, number>, identity: {ok: number, failed: number, first?: string}, outside: Record<string, number>, outsideWhy: string[]}))
const sum = (rs: Record<string, number>[]) => rs.reduce<Record<string, number>>((acc, r) => { for (const [k, n] of Object.entries(r)) acc[k] = (acc[k] ?? 0) + n; return acc }, {})
const summary = {
  documents: items.filter(i => !i.tampered).length, tampered: items.filter(i => i.tampered).length, byKind, tamperedBy: tampered, acceptedTampers: acceptedTampers.slice(0, 40), acceptedTampersCount: acceptedTampers.length,
  disagreements: disagree, capture: {processes: caps.length, seen: sum(caps.map(c => c.seen)), identityOk: caps.reduce((s, c) => s + c.identity.ok, 0), identityFailed: caps.reduce((s, c) => s + c.identity.failed, 0),
    identityFirst: caps.map(c => c.identity.first).filter(Boolean).slice(0, 5), outside: sum(caps.map(c => c.outside)), outsideWhy: [...new Set(caps.flatMap(c => c.outsideWhy))].slice(0, 12)},
  schema: schemaPy ? {...schema, first: schema.first.slice(0, 8)} : undefined,
  ms: {ts: Math.round(tTs), cli: Math.round(tCli), wasm: Math.round(tWasm), python: Math.round(tPy)},
}
const cols = ['docs', 'kernelAccepted', 'kernelRefused', 'tsAgree', 'malformed', 'cliAgree', 'wasmRun', 'wasmAgree', 'goals', 'pyRun', 'pyAgree'] as const
console.log(`kind          ${cols.join('  ')}`)
for (const [k, r] of [...Object.entries(byKind), ['TOTAL', Object.values(byKind).reduce((acc, r) => { for (const c of cols) acc[c] += r[c]; return acc }, row())] as const]) console.log(`${k.padEnd(13)} ${cols.map(c => String(r[c]).padStart(c.length)).join('  ')}`)
if (tamper) {
  console.log(`\ntampered (reference: the checker here)   docs  tsRefused  cliAgree  wasmRun  wasmAgree  goals  pyRun  pyAgree`)
  for (const [w, r] of Object.entries(tampered)) console.log(`${w.padEnd(40)} ${[r.docs, r.tsRefused, r.cliAgree, r.wasmRun, r.wasmAgree, r.goals, r.pyRun, r.pyAgree].map(String).join('  ')}`)
  console.log(`tampered twins the checker accepts (the tamper left a proof): ${acceptedTampers.length}`)
}
console.log(`\ncapture: ${caps.length} processes, identity ${summary.capture.identityOk} ok, ${summary.capture.identityFailed} failed; outside the format: ${JSON.stringify(summary.capture.outside)}`)
if (schemaPy) console.log(`schema: ${schema.valid} valid, ${schema.invalid} invalid${schema.first.length ? `\n  ${schema.first.slice(0, 8).join('\n  ')}` : ''}`)
console.log(`disagreements: ${disagree.length}${disagree.length ? `\n  ${disagree.join('\n  ')}` : ''}`)
console.log(`ms: ${JSON.stringify(summary.ms)}`)
if (outFile) writeFileSync(outFile, JSON.stringify(summary, null, 1))
if (!flag('--keep')) rmSync(work, {recursive: true, force: true})
