// The Go front end (core/extract-go.ts) on the real-world corpus's Go code: every Go source of research/realworld's
// sources.json, its package fetched at the pinned commit (a sparse checkout of the package's directory and the files
// above it, so its go.mod), each name its `export` gives read: a struct and its methods (Type.method, a type the
// methods in its pinned lines, or a method named alone), a function probed for where the subset stops. One JSON line
// per source in <out>/results.jsonl, the rules in <out>/rules/.
//
//   . research/extract/go-setup.sh && bun research/extract/go-run.ts --out runs/extract-go/<name> [--only <id substring>]
//
// A source whose names don't all extract is refused (the first refusal, where and why); its part that does (the
// methods that extract, read together) is reported beside it as `part`, not counted as the source extracted.
import {appendFileSync, mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {type GoOptions, type GoPkg, extractGo, probeGoFunc, readGoPackage} from '../../core/extract-go.ts'
import {checkout, withImports} from './go-fetch.ts'

const here = import.meta.dir, args = process.argv.slice(2)
const flag = (n: string) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : undefined }
const out = flag('--out') ?? join(here, '../../runs/extract-go/local'), only = flag('--only')
mkdirSync(join(out, 'rules'), {recursive: true})
type Src = {item: string, domain: string, role: string, repo: string, commit: string, licence: string, language: string, path: string, lines: string, export: string}
const sources = (JSON.parse(readFileSync(join(here, '../realworld/sources.json'), 'utf8')) as Src[]).filter(s => s.language === 'Go' && (!only || `${s.item} :: ${s.path}`.includes(only)))
// What a source's callers do with an object a failed call wrote, where the code says (core/extract-go.ts's onError).
const options = JSON.parse(readFileSync(join(here, 'go-options.json'), 'utf8')) as Record<string, Partial<GoOptions> & {why: string}>

// --- the names a source's `export` gives ------------------------------------------------------------------------------
type Unit = {k: 'struct', entry: string, methods?: string[], pinned?: boolean} | {k: 'func', name: string} | {k: 'none', what: string}
function unitsOf(s: Src, pkg: GoPkg, dir: string): Unit[] {
  // "name: a, b": the calls of a and b in name (a function of the package, or what the lines cited do).
  const label = /^(\w+):\s*/.exec(s.export.trim())?.[1]
  let text = s.export.trim().replace(/^[\w ]+:\s*/, '')
  if (!s.path.endsWith('.go')) return [{k: 'none', what: `${s.path.split('/').pop()}: not Go code (a document)`}]
  if (label && pkg.funcs.some(f => !f.recv && f.name === label)) text = label
  if (/\(doc\)$/.test(text)) return [{k: 'none', what: `${text}: the corpus cites a type's documentation here, not code to read`}]
  if (/_test\.go$/.test(s.path)) return [{k: 'none', what: `${text}: a test (it sets up the code it checks; the code is read where it is declared)`}]
  const isType = (n: string) => pkg.types.some(t => t.name === n)
  const methodsOf = (t: string) => pkg.funcs.filter(f => f.recv?.type === t && f.body).map(f => f.name)
  const ownerOf = (m: string) => pkg.funcs.find(f => f.recv && f.name === m && f.body)?.recv?.type
  const units: Unit[] = [], byType = new Map<string, string[]>()
  let cur: string | undefined
  const ranges = s.lines.split(',').map(r => r.split('-').map(Number) as [number, number?]).map(([a, b]) => [a, b ?? a] as const)
  const file = s.path.split('/').pop()!
  for (let tok of text.split(',').map(x => x.trim()).filter(Boolean)) {
    tok = tok.replace(/\s*\(.*\)$/, '')
    const dot = /^(\w+)\.(\w+\*?)$/.exec(tok)
    if (dot) { cur = dot[1]!; tok = dot[2]! }
    const add = (t: string, ms: string[]) => { const xs = byType.get(t) ?? []; for (const m of ms) if (!xs.includes(m)) xs.push(m); byType.set(t, xs) }
    if (tok.endsWith('*')) {
      const pre = tok.slice(0, -1), t = cur ?? pkg.types.find(x => methodsOf(x.name).some(m => m.startsWith(pre)))?.name
      const ms = t ? methodsOf(t).filter(m => m.startsWith(pre)) : []
      if (!t || !ms.length) { units.push({k: 'none', what: `${tok}: no method the package declares by that name`}); continue }
      add(t, ms); continue
    }
    if (cur && methodsOf(cur).includes(tok)) { add(cur, [tok]); continue }
    if (!dot && isType(tok)) {
      // A type alone: the methods of it its pinned lines hold.
      const ms = pkg.funcs.filter(f => f.recv?.type === tok && f.body && f.p.startsWith(`${file}:`) && ranges.some(([a, b]) => f.span[0] <= b && f.span[1] >= a)).map(f => f.name)
      if (!ms.length) units.push({k: 'none', what: `${tok}: a type with no methods in the lines cited (data, not a step)`})
      else units.push({k: 'struct', entry: tok, methods: ms, pinned: true})
      continue
    }
    const owner = ownerOf(tok)
    if (owner) { add(owner, [tok]); continue }
    if (pkg.funcs.some(f => !f.recv && f.name === tok)) { units.push({k: 'func', name: tok}); continue }
    const src = readFileSync(join(dir, file), 'utf8')
    units.push({k: 'none', what: new RegExp(`\\.${tok}\\(`).test(src) ? `${tok}: not a name the package declares (the lines cited call it from another package)` : `${tok}: not a name the package declares`})
  }
  for (const [t, ms] of byType) units.unshift({k: 'struct', entry: t, methods: ms})
  return units
}
// Why a refusal: a short key, for the tally.
const reason = (what: string): string => {
  const rules: [RegExp, string][] = [
    [/another module|of [\w.-]+\.[a-z]+\/|another package's/, "another module's code"], [/a loop|a range over/, 'loops'], [/float/, 'floats'],
    [/an interface|type assertion|type switch/, 'interfaces'], [/the clock|time\.Now/, 'the clock'], [/generic/, 'generics'], [/a goroutine|a channel/, 'concurrency'],
    [/a closure|function value|a function\)/, 'functions as values'], [/a test|documentation|not Go code/, 'not code to read'], [/not a name the package|no method/, 'not a declaration of the code'],
    [/no methods in the lines|data, not a step/, 'data, not a step'], [/not a step of a state/, 'not a step over a state'], [/after the state is written/, 'a write before an error'],
    [/package variable/, 'package variables'], [/standard library/, 'standard library outside the subset'], [/differ/, 'check: a difference'], [/string/, 'strings'],
  ]
  return rules.find(([re]) => re.test(what))?.[1] ?? 'other'
}

class NotGo extends Error {}
const results = join(out, 'results.jsonl')
writeFileSync(results, '')
const t0 = performance.now()
const budget = args.includes("--quick") ? {runs: 20, depth: 6, states: 40} : {runs: 200, depth: 12, states: 400}
for (const s of sources) {
  const id = `${s.item} :: ${s.path}`, start = performance.now()
  const row: Record<string, unknown> = {set: 'realworld-go', id, item: s.item, role: s.role, repo: s.repo, commit: s.commit, path: s.path, lines: s.lines, export: s.export, language: s.language}
  try {
    if (!s.path.endsWith('.go')) throw new NotGo(`${s.path.split('/').pop()}: not Go code (a document the corpus cites beside it)`)
    const dir = checkout(s.repo, s.commit, s.path.split('/').slice(0, -1).join('/'))
    let pkg: GoPkg
    const read = () => { try { return readGoPackage(dir) } catch (e) { throw new Error(`the reader: ${String((e as {stderr?: string}).stderr ?? (e as Error).message).slice(0, 300)}`) } }
    pkg = read()
    // The repo's packages it imports, checked out too (the reader reads their types; the check builds with them).
    if (withImports(s.repo, s.commit, dir, [...new Set(pkg.files.flatMap(f => f.imports.filter(i => !i.std).map(i => i.path)))])) pkg = read()
    const units = unitsOf(s, pkg, dir), opt = options[`${s.repo}/${s.path}`]
    row.units = units
    const done: Record<string, unknown>[] = []
    for (const u of units) {
      if (u.k === 'none') { done.push({unit: u, ok: false, refusal: {where: s.path, what: u.what}}); continue }
      if (u.k === 'func') { done.push({unit: u, ok: false, refusal: probeGoFunc(pkg, u.name)}); continue }
      const x = extractGo(dir, {entry: u.entry, ...(u.methods ? {methods: u.methods} : {}), ...(opt ? {onError: opt.onError} : {}), check: budget})
      const r: Record<string, unknown> = {unit: u, ok: x.ok, ...(x.ok ? {} : {refusal: x.refusals[0]}), ...(x.evidence ? {evidence: x.evidence} : {}), notes: x.notes}
      if (x.ok && x.source) { r.rule = `${id.replace(/[^\w.-]+/g, '_')}__${u.entry}.ts`; writeFileSync(join(out, 'rules', r.rule as string), x.source) }
      // Refused with several methods: the part that extracts (each method alone, then those that pass together).
      if (!x.ok && u.methods && u.methods.length > 1) {
        const alone = u.methods.filter(m => extractGo(dir, {entry: u.entry, methods: [m], ...(opt ? {onError: opt.onError} : {}), check: {runs: 40, depth: 8, states: 80}}).ok)
        if (alone.length) {
          const y = extractGo(dir, {entry: u.entry, methods: alone, ...(opt ? {onError: opt.onError} : {}), check: budget})
          r.part = {methods: alone, ok: y.ok, ...(y.ok ? {} : {refusal: y.refusals[0]}), ...(y.evidence ? {evidence: y.evidence} : {})}
          if (y.ok && y.source) { const f = `${id.replace(/[^\w.-]+/g, '_')}__${u.entry}.part.ts`; (r.part as Record<string, unknown>).rule = f; writeFileSync(join(out, 'rules', f), y.source) }
        }
      }
      if (opt) r.onError = {mode: opt.onError, why: opt.why}
      done.push(r)
    }
    row.results = done
    const first = done.find(d => !d.ok)
    Object.assign(row, {ok: !first, ...(first ? {refusal: first.refusal, reason: reason((first.refusal as {what: string}).what)} : {})})
  } catch (e) {
    if (e instanceof NotGo) Object.assign(row, {ok: false, refusal: {where: s.path, what: e.message}, reason: 'not code to read'})
    else Object.assign(row, {ok: false, refusal: {where: s.path, what: `the front end failed: ${(e as Error).message.slice(0, 400)}`}, reason: 'front end error'})
  }
  row.ms = Math.round(performance.now() - start)
  appendFileSync(results, `${JSON.stringify(row)}\n`)
  const r = row as {ok: boolean, refusal?: {where: string, what: string}, results?: {part?: {methods: string[], ok: boolean}}[]}
  const part = r.results?.find(x => x.part)?.part
  console.log(`${r.ok ? 'EXTRACTED' : 'refused  '} ${id}${r.ok ? '' : `: ${r.refusal?.where}: ${r.refusal?.what.slice(0, 200)}`}${part ? ` [part: ${part.methods.join(', ')} ${part.ok ? 'extracted' : 'refused'}]` : ''}`)
}
const rows = readFileSync(results, 'utf8').trim().split('\n').filter(Boolean).map(l => JSON.parse(l) as {ok: boolean, reason?: string, item: string, role: string})
const tally: Record<string, number> = {}
for (const r of rows) if (!r.ok) tally[r.reason!] = (tally[r.reason!] ?? 0) + 1
const items = [...new Set(rows.map(r => r.item))]
console.log(`${rows.length} Go sources: ${rows.filter(r => r.ok).length} extracted, ${rows.filter(r => !r.ok).length} refused ${JSON.stringify(tally)}`)
console.log(`${items.length} items: ${items.filter(i => rows.some(r => r.item === i && r.role === 'rule' && r.ok)).length} with their rule source extracted`)
console.log(`${Math.round(performance.now() - t0)} ms`)
