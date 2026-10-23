// The extractor (core/extract.ts) on real code: each source fetched at its pinned commit, extracted, and checked
// against itself; one JSON line per source in <out>/results.jsonl (extracted or refused, the reason and where, the
// check's evidence), and the rule's source in <out>/rules/ where one was extracted.
//
//   bun research/extract/run.ts --out runs/extract/<name> [--only <id substring>] [--set ours|realworld|all]
//
// Two lists: sources.json (examples from well-known open-source code, picked for this, each with repo and commit) and
// realworld-sources.json (research/realworld's corpus, its sources.json as of 6c675e4 on research/realworld, read
// as it is: the entry named by its `export`, the whole file read).
import {mkdirSync, readFileSync, writeFileSync, existsSync, appendFileSync} from 'node:fs'
import {dirname, join} from 'node:path'
import * as xstate from 'xstate'
import {extract, extractXState} from '../../core/extract.ts'

type Ours = {id: string, repo: string, commit: string, path: string, lines?: string, file?: string, entry: string, shape?: 'xstate' | 'class' | 'functions', functions?: string[], methods?: string[], init?: unknown, close?: string, licence: string, note: string}
type Real = {item: string, domain: string, role: string, repo: string, commit: string, licence: string, language: string, path: string, lines: string, export: string}
type Job = {set: 'ours' | 'realworld', id: string, role?: string, repo: string, commit: string, path: string, lines?: string, file: string, entry: string, shape?: 'xstate' | 'class' | 'functions', functions?: string[], methods?: string[], init?: unknown, close?: string, language: string}

const here = import.meta.dir, args = process.argv.slice(2)
const flag = (n: string) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : undefined }
const out = flag('--out') ?? join(here, '../../runs/extract/local'), only = flag('--only'), set = flag('--set') ?? 'all'
mkdirSync(join(out, 'rules'), {recursive: true})

const ours: Job[] = (JSON.parse(readFileSync(join(here, 'sources.json'), 'utf8')) as Ours[]).map(s => ({set: 'ours', ...s, file: s.file ?? s.path.split('/').pop()!, language: /\.tsx?$/.test(s.file ?? s.path) ? 'TypeScript' : 'JavaScript'}))
// The corpus's export names a class, a function, a machine, Class.method, or Name (a, b, c) for the methods it reads.
const real: Job[] = (JSON.parse(readFileSync(join(here, 'realworld-sources.json'), 'utf8')) as Real[]).map(s => {
  const m = /^([\w$]+)(?:\.([\w$]+))?(?:\s*\(([^)]*)\))?/.exec(s.export.trim())
  const entry = m?.[1] ?? s.export, method = m?.[2], list = m?.[3]?.split(',').map(x => x.trim().replace(/\{.*$/, '')).filter(x => /^[\w$]+$/.test(x))
  return {set: 'realworld', id: `${s.item} :: ${s.path}`, role: s.role, repo: s.repo, commit: s.commit, path: s.path, file: s.path.split('/').pop()!, entry, language: s.language,
    ...(s.domain === 'xstate' ? {shape: 'xstate' as const} : {}), ...(method ? {methods: [method]} : list?.length ? {methods: list} : {})}
})
const jobs = [...(set === 'realworld' ? [] : ours), ...(set === 'ours' ? [] : real)].filter(j => !only || j.id.includes(only))

// The file at its commit (cached under .cache/, not committed: the code is its authors').
async function fetchSource(j: Job): Promise<string> {
  const cache = join(here, '.cache', j.repo, j.commit, j.path)
  if (existsSync(cache)) return readFileSync(cache, 'utf8')
  const res = await fetch(`https://raw.githubusercontent.com/${j.repo}/${j.commit}/${j.path}`)
  if (!res.ok) throw new Error(`fetch ${j.repo}@${j.commit}:${j.path}: ${res.status}`)
  const text = await res.text()
  mkdirSync(dirname(cache), {recursive: true})
  writeFileSync(cache, text)
  return text
}
const slice = (text: string, lines?: string) => {
  if (!lines) return text
  const all = text.split('\n'), parts = lines.split(',').map(r => r.split('-').map(Number) as [number, number?])
  return parts.map(([a, b]) => all.slice(a - 1, b ?? a).join('\n')).join('\n')
}
// Why a refusal: a short key, for the tally.
const reason = (what: string): string => {
  const rules: [RegExp, string][] = [
    [/not TypeScript or JavaScript/, 'language'], [/another module|from another module/, 'imports'], [/async|await|generator/, 'async'],
    [/a loop/, 'loop'], [/an array|lists are not/, 'arrays'], [/string|template/, 'strings'], [/safe integer|division|a power|fraction/, 'floats and division'],
    [/no type the subset reads|any or unknown/, 'untyped'], [/fromXState: .*`(invoke|after|always|onDone)`/, 'xstate: invoke, after, always or onDone'], [/fromXState: .*inline/, 'xstate: inline actions or guards'],
    [/fromXState/, 'xstate: other'], [/made by a function|makes the machine/, 'xstate: a machine made by a function'], [/v4 `cond`/, 'xstate: v4 cond'], [/extends another/, 'class extends'],
    [/state it was given/, 'mutates its argument'], [/differ/, 'check: a difference'], [/no function|no class|no machine/, 'entry not found'], [/may be missing|undefined/, 'missing values'],
    [/function value|a call the subset|a method the subset|new /, 'calls and objects outside the subset'], [/try\/catch/, 'try/catch'],
  ]
  return rules.find(([re]) => re.test(what))?.[1] ?? 'other'
}

const results = join(out, 'results.jsonl')
writeFileSync(results, '')
const t0 = performance.now()
for (const j of jobs) {
  const row: Record<string, unknown> = {set: j.set, id: j.id, role: j.role, repo: j.repo, commit: j.commit, path: j.path, ...(j.lines ? {lines: j.lines} : {}), entry: j.entry, language: j.language}
  const start = performance.now()
  try {
    if (!/^(TypeScript|JavaScript)$/.test(j.language)) {
      Object.assign(row, {ok: false, refusal: {where: j.path, what: `${j.language}: not TypeScript or JavaScript`}, reason: 'language'})
    } else {
      let code = slice(await fetchSource(j), j.lines)
      if (j.close) code += `\n${j.close}\n`
      const shape = j.shape ?? (new RegExp(`\\bclass\\s+${j.entry}\\b`).test(code) ? 'class' : /\bcreateMachine\b/.test(code) && !/\bfunction\s+\w+\s*\(\s*state/.test(code) ? 'xstate' : 'functions')
      if (shape === 'xstate') {
        const x = extractXState(code, {file: j.file, entry: j.entry, xstate: xstate as never, check: {runs: 200, depth: 16}})
        Object.assign(row, {ok: x.ok, shape, ...(x.ok ? {} : {refusal: x.refusals[0], reason: reason(x.refusals[0]?.what ?? '')}), ...(x.evidence ? {evidence: x.evidence} : {}), notes: x.notes})
        if (x.source) writeFileSync(join(out, 'rules', `${j.id.replace(/[^\w.-]+/g, '_')}.ts`), x.source)
      } else {
        const x = extract(code, {file: j.file, entry: j.entry, ...(shape === 'class' ? {shape: 'class' as const} : {shape: 'functions' as const}),
          ...(j.functions ? {functions: j.functions} : {}), ...(j.methods ? {methods: j.methods} : {}), ...(j.init !== undefined ? {init: j.init} : {}), check: {runs: 200, depth: 12, states: 400}})
        Object.assign(row, {ok: x.ok, shape, ...(x.ok ? {} : {refusal: x.refusals[0], reason: reason(x.refusals[0]?.what ?? '')}), ...(x.evidence ? {evidence: x.evidence} : {}), notes: x.notes})
        if (x.source) writeFileSync(join(out, 'rules', `${j.id.replace(/[^\w.-]+/g, '_')}.ts`), x.source)
      }
    }
  } catch (e) {
    Object.assign(row, {ok: false, refusal: {where: j.path, what: `the extractor failed: ${(e as Error).message}`}, reason: 'extractor error'})
  }
  row.ms = Math.round(performance.now() - start)
  appendFileSync(results, `${JSON.stringify(row)}\n`)
  const r = row as {ok: boolean, refusal?: {where: string, what: string}, evidence?: {requests?: number, events?: number, coverage?: {hit: number, arms: number}}}
  console.log(`${r.ok ? 'EXTRACTED' : 'refused  '} ${j.id}${r.ok ? `: ${r.evidence?.requests ?? r.evidence?.events} requests, branches ${r.evidence?.coverage?.hit}/${r.evidence?.coverage?.arms}` : `: ${r.refusal?.where}: ${r.refusal?.what.slice(0, 160)}`}`)
}
const rows = readFileSync(results, 'utf8').trim().split('\n').filter(Boolean).map(l => JSON.parse(l) as {set: string, ok: boolean, reason?: string})
const tally = (xs: typeof rows) => { const t: Record<string, number> = {}; for (const r of xs) if (!r.ok) t[r.reason!] = (t[r.reason!] ?? 0) + 1; return t }
for (const s of ['ours', 'realworld']) {
  const xs = rows.filter(r => r.set === s)
  if (xs.length) console.log(`${s}: ${xs.length} sources, ${xs.filter(r => r.ok).length} extracted, ${xs.filter(r => !r.ok).length} refused ${JSON.stringify(tally(xs))}`)
}
console.log(`${Math.round(performance.now() - t0)} ms`)
