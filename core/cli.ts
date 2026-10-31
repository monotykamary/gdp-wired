#!/usr/bin/env node
// gdp-wired's command line: a rule read from code in any language the extractor reads, its laws proven, with nothing
// written. A thin layer over the library: the front ends (core/extract*.ts, core/effect.ts) read the rule with its
// boundary inferred, core/laws.ts reads the laws stated in the code, the prover (core/dsl.ts's proveRule and
// proveSteps, with their search) proves them, and laws nobody stated are proposed from the rule's own comparisons.
//
//   gdp-wired check <file|dir>... [--entry X] [--methods a,b] [--failures kept] [--json] [--ms 10000] [--no-propose]
//
// The language is the file's (.py .rb .ex .java .kt .go .rs .swift .c .h .cpp .cc .hpp .ts .js .sol; a directory with go.mod
// or .go files is a Go package, with Cargo.toml a Rust crate, with Package.swift a Swift package); the options a rule needs (failures, onError, methods,
// answers, skip, stores) from the flags or from gdp.toml (configFor, below). Exit code: 0 when no law stated in
// the code is broken, 1 when one is, 2 when one couldn't be checked (the rule refused, or the law not read).
import type {Extraction, Name} from './extract.ts'
import {type Verdict, proveRule, proveSteps} from './dsl.ts'
import type {Law} from './machine.ts'
import {type Built, type Cite, LawError, type LawText, buildLaw, buildTwoRuns, citesIn, isTwoRuns, lawsIn, namesWithClock} from './laws.ts'
import {type TwoRunLaw, certify, proveTwoRuns} from './relational.ts'

type FS = {existsSync: (p: string) => boolean, readFileSync: (p: string, e: string) => string, readdirSync: (p: string) => string[], statSync: (p: string) => {isDirectory: () => boolean},
  mkdirSync: (p: string, o: {recursive: boolean}) => unknown, writeFileSync: (p: string, s: string) => void}
type Path = {resolve: (...p: string[]) => string, dirname: (p: string) => string, join: (...p: string[]) => string, basename: (p: string) => string, extname: (p: string) => string, relative: (a: string, b: string) => string}
const proc = (globalThis as unknown as {process: {argv: string[], exitCode?: number, cwd: () => string, env: Record<string, string | undefined>, stdout: {write: (s: string) => void, isTTY?: boolean}, getBuiltinModule: (id: string) => unknown}}).process
const fs = proc.getBuiltinModule('node:fs') as FS, path = proc.getBuiltinModule('node:path') as Path
const out = (s = '') => proc.stdout.write(`${s}\n`)
// Color, plain ANSI: only on a terminal, never with --json, NO_COLOR (any value) or TERM=dumb; FORCE_COLOR turns it on.
// Uncolored, the text is the same byte for byte.
export const colors = (env: Record<string, string | undefined>, tty: boolean, json = false): boolean =>
  !json && (env.FORCE_COLOR !== undefined && !['0', 'false'].includes(env.FORCE_COLOR) ? true : env.NO_COLOR === undefined && env.TERM !== 'dumb' && tty)
let tint = false
const SGR = {green: 32, red: 31, yellow: 33, dim: 2}
const paint = (c: keyof typeof SGR, s: string | number) => (tint && s !== '' ? `\x1b[${SGR[c]}m${s}\x1b[0m` : String(s))
const VERDICT = {proven: 'green', broken: 'red', unknown: 'yellow', 'not read': 'yellow'} as const

// --- the options ---------------------------------------------------------------------------------------------------------
export type Opts = {entry?: string, methods?: string[], failures?: 'refuse' | 'kept', onError?: 'refuse' | 'discard', json?: boolean, ms: number, propose: boolean, root?: string,
  python?: string, clock?: string, cert?: string, [k: string]: unknown}
function args(argv: string[]): {cmd: string, targets: string[], o: Opts} {
  const o: Opts = {ms: 10_000, propose: true}, targets: string[] = []
  let cmd = ''
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]!
    if (a === '--json') o.json = true
    else if (a === '--no-propose') o.propose = false
    else if (a.startsWith('--')) {
      const [k, inline] = a.slice(2).split('=') as [string, string | undefined], v = inline ?? argv[++i] ?? ''
      const key = k.replace(/-(\w)/g, (_, c: string) => c.toUpperCase())
      o[key] = key === 'methods' ? v.split(',') : key === 'ms' ? Number(v) : v
    } else if (!cmd) cmd = a
    else targets.push(a)
  }
  return {cmd, targets, o}
}

// --- the languages -------------------------------------------------------------------------------------------------------
export type Lang = 'python' | 'ruby' | 'elixir' | 'java' | 'kotlin' | 'go' | 'rust' | 'swift' | 'c' | 'cpp' | 'ts' | 'solidity'
const EXT: Record<string, Lang> = {'.py': 'python', '.rb': 'ruby', '.ex': 'elixir', '.exs': 'elixir', '.java': 'java', '.kt': 'kotlin', '.go': 'go', '.rs': 'rust', '.swift': 'swift', '.c': 'c', '.h': 'c',
  '.cpp': 'cpp', '.cc': 'cpp', '.cxx': 'cpp', '.hpp': 'cpp', '.ts': 'ts', '.mts': 'ts', '.tsx': 'ts', '.js': 'ts', '.mjs': 'ts', '.sol': 'solidity'}
const COMMENT: Record<Lang, string> = {python: '#', ruby: '#', elixir: '#', java: '//', kotlin: '//', go: '//', rust: '//', swift: '//', c: '//', cpp: '//', ts: '//', solidity: '//'}
export const LANG_NAME: Record<Lang, string> = {python: 'Python', ruby: 'Ruby', elixir: 'Elixir', java: 'Java', kotlin: 'Kotlin', go: 'Go', rust: 'Rust', swift: 'Swift', c: 'C', cpp: 'C++', ts: 'TypeScript', solidity: 'Solidity'}
// A target: the path a front end reads (a file, a Go package, a Rust crate), its language and the files its laws are in.
type Target = {lang: Lang, at: string, files: string[]}
function targetsOf(p: string): Target[] {
  const abs = path.resolve(p)
  if (!fs.existsSync(abs)) throw new Error(`${p}: no such file or directory`)
  const src = (d: string, ext: RegExp) => fs.readdirSync(d).filter(f => ext.test(f) && !/_test\.go$|\.test\.|_spec\./.test(f)).map(f => path.join(d, f))
  if (fs.statSync(abs).isDirectory()) {
    if (fs.existsSync(path.join(abs, 'Cargo.toml'))) return [{lang: 'rust', at: abs, files: rustFiles(abs)}]
    if (fs.existsSync(path.join(abs, 'Package.swift'))) return [{lang: 'swift', at: abs, files: swiftFiles(path.join(abs, 'Sources'))}]
    if (fs.existsSync(path.join(abs, 'go.mod')) || src(abs, /\.go$/).length) return [{lang: 'go', at: abs, files: src(abs, /\.go$/)}]
    return fs.readdirSync(abs).filter(f => EXT[path.extname(f)] && !/\.test\.|_test\.|_spec\.|\.d\.ts$/.test(f)).flatMap(f => targetsOf(path.join(abs, f)))
  }
  const lang = EXT[path.extname(abs)]
  if (!lang) throw new Error(`${p}: not a language gdp-wired reads (${Object.keys(EXT).join(' ')})`)
  if (lang === 'go') return [{lang, at: path.dirname(abs), files: src(path.dirname(abs), /\.go$/)}]
  if (lang === 'rust') { const crate = up(path.dirname(abs), d => fs.existsSync(path.join(d, 'Cargo.toml'))); return [{lang, at: crate ?? path.dirname(abs), files: crate ? rustFiles(crate) : [abs]}] }
  return [{lang, at: abs, files: [abs]}]
}
const swiftFiles = (d: string): string[] => (fs.existsSync(d) ? fs.readdirSync(d).flatMap(f => { const p = path.join(d, f); return fs.statSync(p).isDirectory() ? swiftFiles(p) : f.endsWith('.swift') ? [p] : [] }) : [])
const rustFiles = (crate: string): string[] => { const d = path.join(crate, 'src'); return fs.existsSync(d) ? fs.readdirSync(d).filter(f => f.endsWith('.rs')).map(f => path.join(d, f)) : [] }
// The nearest directory from `d` up where `ok` holds.
export function up(d: string, ok: (d: string) => boolean): string | undefined {
  for (let x = d; ; x = path.dirname(x)) { if (ok(x)) return x; if (path.dirname(x) === x) return undefined }
}

// A front end run on a target with the options (each loaded only when its language is read).
async function extractOne(t: Target, o: Record<string, unknown>): Promise<Extraction> {
  try { return await extractWith(t, o) } catch (e) {
    // (every front end is read through the TypeScript extractor's terms: the typescript package beside gdp-wired)
    if (/typescript/.test(String((e as Error).message)) && /find|resolve/i.test(String((e as Error).message))) throw new Error('the extractors need the typescript package beside gdp-wired: npx gdp-wired-cli check ... (gdp-wired with TypeScript beside it), or npm i -D gdp-wired typescript')
    throw e
  }
}
async function extractWith(t: Target, o: Record<string, unknown>): Promise<Extraction> {
  const f = t.at, dir = path.dirname(f)
  switch (t.lang) {
    case 'python': {
      const {extractPython} = await import('./extract-py.ts')
      // (the repository's root: the project's (pyproject.toml, setup.py), else above the outermost package the file is
      // in; the Python of a virtualenv beside it)
      const root = (o.root as string | undefined) ?? up(dir, d => ['pyproject.toml', 'setup.py', 'setup.cfg'].some(m => fs.existsSync(path.join(d, m)))) ?? up(dir, d => !fs.existsSync(path.join(d, '__init__.py'))) ?? dir
      const venv = up(root, d => fs.existsSync(path.join(d, '.venv', 'bin', 'python')))
      return extractPython(f, {root, ...(venv ? {python: path.join(venv, '.venv', 'bin', 'python')} : {}), ...o})
    }
    case 'ruby': { const {extractRuby} = await import('./extract-rb.ts'); return extractRuby(f, {root: up(dir, d => path.basename(d) === 'lib') ?? dir, ...o}) }
    case 'elixir': { const {extractElixir} = await import('./extract-ex.ts'); return extractElixir(f, o) }
    case 'java': { const {extractJava} = await import('./extract-jvm.ts'); return extractJava(f, o) }
    case 'kotlin': { const {extractKotlin} = await import('./extract-jvm.ts'); return extractKotlin(f, o) }
    case 'go': { const {extractGo} = await import('./extract-go.ts'); return extractGo(f, o) }
    case 'rust': { const {extractRust} = await import('./extract-rs.ts'); return extractRust(f, o) }
    case 'swift': { const {extractSwift} = await import('./extract-swift.ts'); return extractSwift(f, o) }
    case 'c': case 'cpp': { const {extractC} = await import('./extract-c.ts'); return extractC(f, o, t.lang === 'cpp') }
    case 'solidity': { const {extractSolidity} = await import('./extract-sol.ts'); return extractSolidity(f, {root: up(dir, d => ['foundry.toml', 'hardhat.config.js', 'hardhat.config.ts', 'package.json'].some(m => fs.existsSync(path.join(d, m)))) ?? dir, ...o}) }
    case 'ts': {
      // (Effect and XState run on the package the file's own project has, imported here as the code imports it)
      const code = fs.readFileSync(f, 'utf8'), file = path.relative(proc.cwd(), f) || f, {createRequire} = proc.getBuiltinModule('node:module') as {createRequire: (p: string) => {resolve: (s: string) => string}}
      const own = async (spec: string) => { try { return await import(createRequire(f).resolve(spec)) as Record<string, unknown> } catch { return undefined } }
      if (/from\s+['"]effect(\/\w+)?['"]/.test(code)) { const {extractEffect} = await import('./effect.ts'), effect = await own('effect'); return extractEffect(file, {...(effect ? {effect} : {}), ...o} as never) }
      if (/from\s+['"]xstate['"]/.test(code) && /\bcreateMachine\b/.test(code)) { const {extractXState} = await import('./extract-xstate.ts'), xstate = await own('xstate'); return extractXState(file, {...(xstate ? {xstate} : {}), ...o} as never) as Extraction }
      const {extract} = await import('./extract.ts')
      return extract(file, o as never)
    }
  }
}

// --- gdp.toml: the modelling choices of each rule, written once beside the code -------------------------------------------
// The nearest gdp.toml, pyproject.toml's [tool.gdp] or package.json's "gdp" from the code up: its top-level keys for
// every rule, [rules.<entry>] for one (failures, onError, methods, answers, skip, stores and their attrs, strict, root,
// python, ...: the front end's own options). TOML has no null: "None" (or "null", "nil") is one, Redis off.
//
//   failures = "kept"
//   [rules._PROXY_MaxIterationsHandler]
//   methods = ["async_pre_call_hook"]
//   stores.internal_usage_cache.attrs = {"dual_cache.redis_cache" = "None"}
type Config = {all: Record<string, unknown>, rules: Record<string, Record<string, unknown>>, at?: string}
export function configFor(from: string): Config {
  // (the first of the three in a directory that holds gdp's options)
  const holder = (d: string) => ['gdp.toml', 'pyproject.toml', 'package.json'].find(f => fs.existsSync(path.join(d, f)) && (f === 'gdp.toml' || (f === 'pyproject.toml' ? /^\[tool\.gdp\b/m : /"gdp"\s*:/).test(fs.readFileSync(path.join(d, f), 'utf8'))))
  const dir = up(from, d => !!holder(d))
  if (!dir) return {all: {}, rules: {}}
  const f = holder(dir)!
  const text = fs.readFileSync(path.join(dir, f), 'utf8')
  let c: Record<string, unknown>
  if (f === 'package.json') c = (JSON.parse(text) as {gdp?: Record<string, unknown>}).gdp ?? {}
  else if (f === 'pyproject.toml') {
    // (only its [tool.gdp...] tables, read as a gdp.toml's)
    let on = false
    c = (toml(text.split('\n').filter(l => { const h = /^\s*\[([^\]]*)\]/.exec(l); if (h) on = /^tool\.gdp\b/.test(h[1]!.trim()); return on }).join('\n')) as {tool?: {gdp?: Record<string, unknown>}}).tool?.gdp ?? {}
  } else c = toml(text)
  const {rules, ...all} = c as {rules?: Record<string, Record<string, unknown>>}
  return {all, rules: rules ?? {}, at: path.join(dir, f)}
}
// TOML's subset a gdp.toml needs: tables ([a.b."c.d"]), dotted and quoted keys, strings, integers, booleans, arrays and
// inline tables on one line, # comments.
export function toml(text: string): Record<string, unknown> {
  const root: Record<string, unknown> = {}
  let table = root
  const keys = (s: string): string[] => [...s.matchAll(/\s*(?:"((?:[^"\\]|\\.)*)"|'([^']*)'|([\w-]+))\s*(?:\.|$)/g)].map(m => m[1] ?? m[2] ?? m[3]!)
  const at = (o: Record<string, unknown>, ks: string[]) => ks.reduce((t, k) => (t[k] ??= {}) as Record<string, unknown>, o)
  // (a dotted key = value set in a table; what follows it)
  const pair = (s: string, into: Record<string, unknown>): string => {
    const eq = /^((?:"(?:[^"\\]|\\.)*"|'[^']*'|[\w.-]+|\s)+?)\s*=/.exec(s) ?? fail(`gdp.toml: can't read ${s.slice(0, 40)}`)
    const ks = keys(eq[1]!), [v, r] = value(s.slice(eq[0].length))
    at(into, ks.slice(0, -1))[ks.at(-1)!] = v
    return r
  }
  const value = (s: string): [unknown, string] => {
    s = s.trimStart()
    const str = /^"((?:[^"\\]|\\.)*)"|^'([^']*)'/.exec(s)
    if (str) { const v = str[1] !== undefined ? JSON.parse(`"${str[1]}"`) as string : str[2]!; return [['None', 'null', 'nil'].includes(v) ? null : v, s.slice(str[0].length)] }
    if (s[0] === '[' || s[0] === '{') {
      const arr = s[0] === '[', out: unknown[] = [], obj: Record<string, unknown> = {}
      s = s.slice(1)
      for (;;) {
        s = s.trimStart()
        if (s[0] === (arr ? ']' : '}')) return [arr ? out : obj, s.slice(1)]
        if (s[0] === ',') { s = s.slice(1); continue }
        if (arr) { const [v, r] = value(s); out.push(v); s = r } else s = pair(s, obj)
      }
    }
    const m = /^(true|false|-?\d+)/.exec(s) ?? fail(`gdp.toml: can't read ${s.slice(0, 40)}`)
    return [m[1] === 'true' ? true : m[1] === 'false' ? false : Number(m[1]), s.slice(m[0].length)]
  }
  for (const raw of text.split('\n')) {
    const l = raw.trim()
    if (!l || l.startsWith('#')) continue
    const h = /^\[([^\]]+)\]\s*(?:#.*)?$/.exec(l)
    if (h) { table = at(root, keys(h[1]!)); continue }
    const r = pair(l, table).trim()
    if (r && !r.startsWith('#')) fail(`gdp.toml: can't read ${l}`)
  }
  return root
}
const fail = (s: string): never => { throw new Error(s) }
// Two option objects merged, the second's winning (objects merged key by key: a store's attrs beside its methods).
const merge = (a: Record<string, unknown>, b: Record<string, unknown>): Record<string, unknown> => {
  const out = {...a}
  for (const [k, v] of Object.entries(b)) out[k] = v && typeof v === 'object' && !Array.isArray(v) && out[k] && typeof out[k] === 'object' && !Array.isArray(out[k]) ? merge(out[k] as Record<string, unknown>, v as Record<string, unknown>) : v
  return out
}

// --- one target: its rules, their laws -------------------------------------------------------------------------------------
type LawOut = {name: string, expr: string, where?: string, kind?: 'law' | 'step' | 'two runs', verdict: 'proven' | 'broken' | 'unknown' | 'not read', run?: string[], replayed?: string, why?: string, assumes?: string[], found?: string[], cites?: string[], cert?: string, ms: number}
export type RuleOut = {file: string, lang: string, entry?: string, ok: boolean, refusals: {where: string, what: string}[], notes: string[], names: Name[], checked?: string,
  laws: LawOut[], proposed: LawOut[], brokenProposed?: number, source?: string}

// The entries to read: the one given, else the one inferred; where several classes or structs qualify, each of them; a
// file of functions, each function a law is stated on.
async function rulesOf(t: Target, o: Opts, laws: Scoped[]): Promise<{entry?: string, x: Extraction}[]> {
  const {json: _j, ms: _m, propose: _p, clock: _c, cert: _t, ...flags} = o
  void _j; void _m; void _p; void _c; void _t
  // (the options: gdp.toml's for every rule, then the rule's own, then the flags; a rule found with no entry named is
  // read again where gdp.toml has options of its own for it)
  const cfg = configFor(t.lang === 'go' || t.lang === 'rust' || fs.statSync(t.at).isDirectory() ? t.at : path.dirname(t.at))
  const {clock: _k, ...shared} = cfg.all
  void _k
  const optsFor = (entry?: string) => merge(merge(shared, (entry && cfg.rules[entry]) || {}), flags)
  const one = async (entry?: string) => {
    const x = await extractOne(t, {...optsFor(entry), ...(entry ? {entry} : {})}), found = x.model?.name
    return !entry && found && cfg.rules[found] ? {entry: found, x: await extractOne(t, {...optsFor(found), entry: found})} : {entry, x}
  }
  const given = o.entry ?? (cfg.all.entry as string | undefined)
  if (given) return [await one(given)]
  if (t.lang === 'ts' || t.lang === 'cpp') {
    const code = t.files.map(f => fs.readFileSync(f, 'utf8')).join('\n')
    const re = t.lang === 'cpp' ? /^\s*(?:class|struct)\s+(\w+)\s*(?::[^{]*)?\{/gm : /export\s+(?:default\s+)?(?:abstract\s+)?class\s+(\w+)|export\s+(?:const|function)\s+(\w+)/g
    const cands = [...new Set([...code.matchAll(re)].map(m => m[1] ?? m[2]!))]
    const all = await Promise.all(cands.map(c => one(c)))
    const good = all.filter(r => r.x.ok)
    return good.length ? good : all.length ? all : [{x: {ok: false, refusals: [{where: t.at, what: 'no class or exported function to read: name the entry (--entry)'}], notes: []}}]
  }
  const first = await one()
  if (first.x.ok) return [first]
  // (refused with no entry named: the rules gdp.toml names that the code has, each with its options)
  const named = Object.keys(cfg.rules).filter(k => t.files.some(f => new RegExp(`\\b${k.replace(/[^\w]/g, '\\$&')}\\b`).test(fs.readFileSync(f, 'utf8'))))
  if (named.length) return Promise.all(named.map(k => one(k)))
  // (else each class the refusal names, and each function outside a class a law is stated on)
  const what = first.x.refusals[0]?.what ?? ''
  const several = /several (?:classes|structs) (?:write their state|written by the file's functions) \(([^)]*)\)/.exec(what)?.[1]!.split(', ') ?? []
  const fns = [...new Set(laws.filter(l => !l.cls && l.fn).map(l => l.fn!))]
  return several.length || fns.length ? Promise.all([...several, ...fns].map(c => one(c))) : [first]
}

// A law with where it sits in the code: the class (or struct, module) it is in and the function after it.
type Scoped = LawText & {cls?: string, fn?: string}
function scoped(file: string): Scoped[] {
  const text = fs.readFileSync(file, 'utf8'), lines = text.split('\n')
  return lawsIn(text, path.basename(file)).map(l => {
    let cls: string | undefined, fn: string | undefined
    for (let i = l.line! - 1; i >= 0 && !cls; i--) { const m = /\b(?:class|struct|actor|defmodule|module|object|impl|record|interface|contract)\s+([\w.:]+)|\btype\s+(\w+)\s+struct\b/.exec(lines[i]!.replace(/(#|\/\/).*$/, '')); if (m) cls = (m[1] ?? m[2])!.split(/[.:]/).pop() }
    for (let i = l.line! - 1; i < lines.length && !fn; i++) { const code = i === l.line! - 1 ? lines[i]!.replace(/(#|\/\/|--).*$/, '') : lines[i]!; const m = /\b(?:def|defp|fn|fun|func|function)\s+(?:\([^)]*\)\s*)?(?:self\.)?(\w+)|^\s*(?:(?:public|private|protected|static|final|synchronized|async|override|open|suspend|inline|virtual|const|[\w<>[\],?]+)\s+)*(\w+)\s*\(/.exec(code); if (m && !/^(if|for|while|switch|return|catch|new)$/.test(m[1] ?? m[2]!)) fn = m[1] ?? m[2] }
    // (a Python function at the module's top level is in no class, whatever precedes it)
    if (fn && file.endsWith('.py') && lines.slice(l.line! - 1).some(x => new RegExp(`^(?:async\\s+)?def\\s+${fn}\\b`).test(x))) cls = undefined
    return {...l, ...(cls ? {cls} : {}), ...(fn ? {fn} : {})}
  })
}

export async function checkTarget(t: Target, o: Opts): Promise<RuleOut[]> {
  const laws = t.files.flatMap(scoped), cites = t.files.flatMap(f => citesIn(fs.readFileSync(f, 'utf8'), path.basename(f)))
  const rules = await rulesOf(t, o, laws)
  const outs: RuleOut[] = []
  // (the clock's unit, for durations in a law: the language's clock, or clock = "s" | "ms" in gdp.toml or --clock)
  const unit = o.clock ?? configFor(t.lang === 'go' || t.lang === 'rust' || fs.statSync(t.at).isDirectory() ? t.at : path.dirname(t.at)).all.clock ?? CLOCK[t.lang]
  const others = Object.fromEntries(rules.filter(r => r.x.ok).map(r => [r.entry ?? r.x.model?.name ?? '', r.x]))
  const ctx: Ctx = {ms: o.ms, clock: unit === 's' ? 1 : unit === 'ms' ? 1000 : undefined, others, cites, cert: o.cert, file: path.relative(proc.cwd(), t.at) || t.at}
  for (const {entry, x} of rules) {
    const name = entry ?? (x.model?.name || undefined)
    // (a target that is the working directory, a crate's or a package's: `.`)
    const r: RuleOut = {file: path.relative(proc.cwd(), t.at) || '.', lang: LANG_NAME[t.lang], ...(name ? {entry: name} : {}), ok: x.ok, refusals: x.refusals, notes: x.notes, names: x.names ?? [], laws: [], proposed: [], ...(x.source ? {source: x.source} : {})}
    outs.push(r)
    // (the laws of this rule: all where it is the file's one, else those in its class or on it or its methods, and those
    // outside every class and function)
    const ms0 = new Set((x.names ?? []).map(n => n.method))
    const mine = rules.length === 1 ? laws : laws.filter(l => (!l.cls && !l.fn) || (l.cls ? l.cls === name : l.fn === name || ms0.has(l.fn)))
    if (!x.ok || !x.rule) { r.laws = mine.map(l => ({name: l.name, expr: l.expr, where: l.where, verdict: 'not read', why: 'the rule was refused', ms: 0})); continue }
    const ev = x.evidence
    if (ev) r.checked = `checked against ${'probes' in ev ? `the code: ${ev.requests} requests from the start, ${ev.fromStates} from drawn states, ${ev.probes.steps} from the prover's witnesses` : `XState's own actor: ${(ev as unknown as {events: number}).events} events`}${ev.coverage.arms ? `, ${ev.coverage.hit} of ${ev.coverage.arms} branch arms` : ''}`
    // (the rule's methods: the choice of method where it has several, else the one each name says)
    const evSort = x.model?.inputs.find(v => v.name === x.model?.event)?.sort
    const methods = new Set([...(x.names ?? []).filter(n => n.method).map(n => n.method!), ...(evSort?.k === 'choice' ? evSort.values : [])])
    const stated = mine.map(l => ({...l, ...(l.fn && methods.has(l.fn) ? {method: l.fn} : {})}))
    const proven: unknown[] = []
    // (a law is known by its name: a name stated twice in one rule is refused, both times)
    const twice = (l: LawText) => stated.filter(m => m.name === l.name).map(m => m.where)
    r.laws = stated.map(l => (twice(l).length > 1 ? {name: l.name, expr: l.expr, where: l.where, verdict: 'not read' as const, why: `a law of this name is stated twice (${twice(l).join(', ')}): a law is known by its name`, ms: 0} : prove(x, l, o.ms, proven, {...ctx, entry: name})))
    if (o.propose && x.model) { const p = propose(x, t.lang, o, proven, new Set(stated.map(l => l.expr.replace(/\s+/g, '')))); r.proposed = p.shown; r.brokenProposed = p.broken }
  }
  // (a citation of no law stated in the target: refused, as a law not read is)
  const named = new Set(laws.map(l => l.name))
  for (const c of cites.filter(c => !named.has(c.law))) outs[0]?.laws.push({name: c.law, expr: '', where: c.where, verdict: 'not read', why: `a citation of no law stated here (gdp: cite <law name>: <clause>): ${c.text}`, ms: 0})
  return outs
}
// The unit of each language's clock (Date.now() and a Clock's millis count milliseconds; time.time(), DateTime.diff in
// seconds and Instant's as_secs count seconds); the others say it in gdp.toml (clock = "s" or "ms").
const CLOCK: Partial<Record<Lang, string>> = {python: 's', elixir: 's', rust: 's', ts: 'ms', java: 'ms', kotlin: 'ms'}
type Ctx = {ms: number, clock?: number, others: Record<string, Extraction>, cites: Cite[], cert?: string, file: string, entry?: string}

// A law proven: an invariant with the rule's own invariants beside it, a step law with them and the invariants proven
// so far (each holds in every reachable state, so the step laws may assume them); a law about two runs with the rule's
// invariants holding of each run (core/relational.ts). Its citations go beside it, and with --cert <dir> the proof, as
// an interchange document whose meta holds them.
function prove(x: Extraction, l: LawText, ms: number, proven: unknown[], ctx?: Ctx): LawOut {
  const t0 = Date.now(), cites = ctx?.cites.filter(c => c.law === l.name).map(c => c.text) ?? []
  const base = {name: l.name, expr: l.expr, ...(l.where ? {where: l.where} : {}), ...(cites.length ? {cites} : {})}
  const inv = x.invariants ?? [], search = {search: {ms}}
  let b: Built | undefined, two: TwoRunLaw | undefined
  try { if (isTwoRuns(l.expr)) two = buildTwoRuns(x, l, ctx?.others); else b = buildLaw(x, l, {clock: ctx?.clock}) } catch (e) { if (e instanceof LawError || two === undefined && isTwoRuns(l.expr)) return {...base, verdict: 'not read', why: (e as Error).message, ms: 0}; throw e }
  const kind = two ? 'two runs' as const : b!.kind
  let v: Verdict & {given?: Law[]}
  try { v = two ? proveTwoRuns(two, {...search, invariants: [two.sides[0] === x.rule ? inv : (ctx?.others && Object.values(ctx.others).find(o => o.rule === two!.sides[0])?.invariants) ?? [], inv]}) : b!.kind === 'law' ? proveRule(x.rule!, [...inv, b!.law], search) : proveSteps(x.rule!, [...inv, ...proven] as never, [b!.law], search) }
  catch (e) { return {...base, kind, verdict: 'unknown', why: (e as Error).message, ms: Date.now() - t0} }
  let verdict: LawOut['verdict'] = v.proven && v.checked ? 'proven' : v.run ? 'broken' : 'unknown', replayed: string | undefined
  // (a run the front end replays on the code: broken only where the code runs it so)
  if (verdict === 'broken' && x.replay && v.run && !two) { const r = x.replay(v.run, b!.law); if (r.ok) replayed = r.what; else { verdict = 'unknown'; v.why = `a run breaks it in the rule, not on the code: ${r.what}` } }
  // (a state the laws allow from which a step breaks the law, no run from the start reaching it: shown, not a break)
  const at = !v.run && v.witness && !two ? (x.names ?? []).filter(n => n.rule && n.rule in v.witness! && n.role !== 'const').map(n => `${label(n)} = ${shownValue(x, n.rule, v.witness!, n.none)}`) : []
  if (verdict === 'proven' && b?.kind === 'law') proven.push(b.law)
  const found = v.found?.laws?.map(f => f.text)
  let cert: string | undefined
  if (verdict === 'proven' && ctx?.cert) {
    const more = v.found?.laws?.map(f => f.law) ?? []
    const meta = {producer: 'gdp-wired check', file: ctx.file, ...(ctx.entry ? {entry: ctx.entry} : {}), law: l.name, expr: l.expr, ...(l.where ? {where: l.where} : {}), cites}
    const doc = v.k ? undefined : two ? certify(two.rule, [...v.given ?? [], ...more, ...two.laws], two.stepLaws, meta)
      : b!.kind === 'law' ? certify(x.rule!, [...inv, ...more, b!.law], [], meta) : certify(x.rule!, [...inv, ...proven as Law[], ...more], [b!.law], meta)
    if (doc) { fs.mkdirSync(ctx.cert, {recursive: true}); cert = path.join(ctx.cert, `${[ctx.entry ?? path.basename(ctx.file), l.name].join('.').replace(/[^\w.-]+/g, '-')}.json`); fs.writeFileSync(cert, JSON.stringify(doc)) }
  }
  return {...base, kind, verdict, ...(replayed ? {replayed} : {}), ...(v.run && verdict === 'broken' ? {run: two ? pairRunOf(x, v.run, two) : runOf(x, v.run)} : {}), ...(verdict === 'unknown' ? {why: [v.why ?? v.stuck ?? 'not proven', ...(at.length ? [`a state the laws allow where a step breaks it, no run from the start found reaching it: ${at.join(', ')}`] : [])].join('; ')} : {}),
    ...(v.run && !two ? {assumes: assumedOf(x, v.run)} : {}), ...(found?.length ? {found} : {}), ...(cert ? {cert} : {}), ms: Date.now() - t0}
}
// Two runs as calls of the code: each request once, the values the two runs take apart as `a | b`, and the run b leaves
// out (isolation's: the others' calls) marked.
function pairRunOf(x: Extraction, run: NonNullable<Verdict['run']>, two: TwoRunLaw): string[] {
  const sideOf = (vars: Record<string, unknown>, p: string): Record<string, unknown> => Object.fromEntries(Object.entries(vars).flatMap(([k, val]) => (k.startsWith(p) ? [[k.slice(2), val]] : /^[ab]_/.test(k) ? [] : [[k, val]])))
  const a = runOf(x, {params: sideOf(run.params, 'a_') as Record<string, number>, trace: run.trace.map(q => sideOf(q, 'a_'))})
  const b = runOf(x, {params: sideOf(run.params, 'b_') as Record<string, number>, trace: run.trace.map(q => sideOf(q, 'b_'))})
  const tenant = 'tenant' in run.params && !two.shared.every(n => n !== 'tenant') ? [`B is ${run.params.tenant} (run b takes only B's calls)`] : []
  return [...tenant, ...a.map((s, i) => (s === b[i] ? s : `${s}  |  ${b[i]}`))]
}
// What a refutation assumes of the answers inferred (core/extract-step.ts's `assumed`), at the run's last request.
function assumedOf(x: Extraction, run: NonNullable<Verdict['run']>): string[] {
  const last = run.trace.at(-1) as Record<string, unknown> | undefined, out: string[] = []
  for (const n of (x.names ?? []).filter(m => m.role === 'answer')) {
    if (!last || !(n.rule in last)) continue
    const how = (x as {read?: {answers: {key: string, how?: string, sort: string}[]}}).read?.answers.find(a => a.key === n.code)
    if (how?.how) out.push(`assumes ${n.code.split('.').pop()}(...) may return ${shownValue(x, n.rule, last, n.none)} (${how.how}: any ${how.sort})`)
  }
  return out
}

// --- runs in the code's terms --------------------------------------------------------------------------------------------
type KindLike = {decode: (n: string, v: Record<string, number>) => unknown}
function kindOf(x: Extraction, rule: string): KindLike | undefined {
  const r = x.rule as unknown as {parts: {params: [string, KindLike][], inputs: [string, KindLike][]}, kindsOfState: () => [string, KindLike][]}
  return [...r.parts.params, ...r.parts.inputs, ...r.kindsOfState()].find(([n]) => n === rule)?.[1]
}
function shownValue(x: Extraction, rule: string, vars: Record<string, unknown>, none?: string): string {
  if (none && (vars[none] === 1 || vars[none] === true)) return 'None'
  const k = kindOf(x, rule)
  try { const v = k ? k.decode(rule, vars as Record<string, number>) : vars[rule]; return typeof v === 'string' ? JSON.stringify(v) : String(v) }
  catch { return `a string (#${String(vars[rule])})` }
}
// A run as calls of the code: the constructor's arguments, then each request (the method, its arguments by the code's
// names, the answers and the clock), the last the one that breaks the law.
export function runOf(x: Extraction, run: NonNullable<Verdict['run']>): string[] {
  const names = namesWithClock(x), code = (n: Name) => n.code
  const ps = names.filter(n => n.role === 'param' && n.rule && n.rule in run.params)
  const lines = ps.length ? [`made with ${ps.map(n => `${code(n)} = ${shownValue(x, n.rule, run.params, n.none)}`).join(', ')}`] : []
  const ev = names.find(n => n.role === 'method')
  for (const req of run.trace as Record<string, unknown>[]) {
    const m = ev ? String(kindOf(x, ev.rule)?.decode(ev.rule, req as Record<string, number>) as string | undefined ?? '') : names.find(n => n.method)?.method ?? ''
    // (an object the caller gives: None, or its fields read; a field of an object that is None not shown)
    const none = (n: Name) => !!n.none && (req[n.none] === 1 || req[n.none] === true)
    const objs = names.filter(n => n.role === 'input' && n.method === m && !n.rule && n.none && n.none in req)
    const as = names.filter(n => n.role === 'input' && n.method === m && (n.rule ? n.rule in req : none(n)) && !objs.some(o => none(o) && n.code.startsWith(`${o.code}.`)))
    const call = `${m || 'step'}(${as.map(n => `${code(n)}=${n.rule ? shownValue(x, n.rule, req, n.none) : 'None'}`).join(', ')})`
    const extra = names.filter(n => (n.role === 'answer' || n.role === 'clock') && n.rule in req).map(n => `${label(n)} = ${shownValue(x, n.rule, req, n.none)}`)
    lines.push(extra.length ? `${call} with ${extra.join(', ')}` : call)
  }
  return lines
}

// --- laws proposed: the rule's own comparisons, as laws in the code's terms ----------------------------------------------
// From each comparison, min or max of the step between a number of the state and another number of the state or the
// params, or two fields of one map's cells: that one is at most the other (both ways); an integer of the state never
// below 0; a number of the state that never goes down, or up. Each proven or broken by the prover; the broken ones only
// counted (they are guesses, not claims).
function propose(x: Extraction, lang: Lang, o: Opts, proven: unknown[], stated: Set<string>): {shown: LawOut[], broken: number} {
  const m = x.rule!.machine, names = x.names ?? [], model = x.model!
  const nums = new Set([...model.state, ...model.params].filter(v => v.sort.k === 'num' && !model.outputs.includes(v.name) && v.name !== 'made_at').map(v => v.name))
  const state = new Set(model.state.filter(v => nums.has(v.name)).map(v => v.name))
  // (the code's name for a variable, or the rule's where the code's names another first)
  const codeOf = (rule: string): string => { const n = names.find(y => y.rule === rule && (y.role === 'state' || y.role === 'param')); if (!n) return rule; const first = names.find(y => y.code === n.code && (y.role === 'state' || y.role === 'param')); return first === n ? n.code : rule }
  const base = (v: string) => v.replace(/\$neg$/, '')
  const sides = (e: unknown): Set<string> => { const s = new Set<string>(); JSON.stringify(e, (k, v) => { if (k === 'name' && typeof v === 'string') s.add(base(v)); if (k === 'map' && typeof v === 'string') s.add(base(v)); return v }); return s }
  const pairs = new Set<string>()
  JSON.stringify(m.step, (_, v) => {
    if (v && typeof v === 'object' && ['<', '<=', 'min', 'max'].includes((v as {op?: string}).op ?? '') && 'a' in v && 'b' in v) {
      const a = sides((v as {a: unknown}).a), b = sides((v as {b: unknown}).b)
      for (const p of a) for (const q of b) if (p !== q) { pairs.add(`${p}\0${q}`); pairs.add(`${q}\0${p}`) }
    }
    return v
  })
  const cands: LawText[] = []
  const add = (name: string, expr: string) => { if (!stated.has(expr.replace(/\s+/g, '')) && !cands.some(c => c.expr === expr)) cands.push({name, expr}) }
  for (const pq of pairs) {
    const [p, q] = pq.split('\0') as [string, string]
    if (state.has(p) && nums.has(q)) add(`${codeOf(p)} stays at most ${codeOf(q)}`, `${codeOf(p)} <= ${codeOf(q)}`)
    const mp = /^(.+)\.(\w+)$/.exec(p), mq = /^(.+)\.(\w+)$/.exec(q)
    if (mp && mq && mp[1] === mq[1] && mp[2] !== mq[2] && mp[2] !== 'has' && mq[2] !== 'has') {
      const map = names.find(n => n.rule === mp[1] && n.map)
      if (map && map.map!.fields.includes(mp[2]!) && map.map!.fields.includes(mq[2]!)) add(`every ${map.code}'s ${mp[2]} stays at most its ${mq[2]}`, `forall k in ${map.code}: ${map.code}[k].${mp[2]} <= ${map.code}[k].${mq[2]}`)
    }
  }
  for (const v of state) {
    if (`${v}$neg` in m.state) add(`${codeOf(v)} is never negative`, `${codeOf(v)} >= 0`)
    add(`${codeOf(v)} never changes`, `${codeOf(v)} == old(${codeOf(v)})`)
    add(`${codeOf(v)} never goes down`, `${codeOf(v)} >= old(${codeOf(v)})`)
    add(`${codeOf(v)} never goes up`, `${codeOf(v)} <= old(${codeOf(v)})`)
  }
  const shown: LawOut[] = [], until = Date.now() + Math.max(5000, o.ms * 2)
  let broken = 0
  const fixed = new Set<string>()
  for (const c of cands.slice(0, 40)) {
    if (Date.now() > until) break
    const v = /^(.+) never (?:changes|goes (?:down|up))$/.exec(c.name)?.[1]
    if (v && fixed.has(v)) continue
    const r = prove(x, c, Math.min(o.ms, 2000), proven)
    if (r.verdict === 'broken' || r.verdict === 'not read') broken++
    else { shown.push({...r, where: `${COMMENT[lang]} gdp: law ${c.name}: ${c.expr}`}); if (v && r.verdict === 'proven' && c.name.endsWith('changes')) fixed.add(v) }
  }
  return {shown, broken}
}

// The laws `check` proposes for an extraction with nothing stated, each proven (`shown`: those not broken by a run).
export const proposedLaws = (x: Extraction, lang: Lang, ms = 2000): {shown: LawOut[], broken: number} => propose(x, lang, {ms, propose: true}, [], new Set())

// --- printing ------------------------------------------------------------------------------------------------------------
const ROLE: Record<Name['role'], string> = {state: 'state', param: 'made with', input: 'request', answer: 'answered', result: 'result', failed: 'failed', method: 'method', clock: 'clock', const: 'constant'}
function printRule(r: RuleOut, o: Opts) {
  out(`${r.file}${r.entry ? `: ${r.entry}` : ''} (${r.lang})`)
  if (!r.ok) {
    for (const f of r.refusals) out(`  ${paint('yellow', `refused at ${f.where}:`)} ${f.what}`)
  } else {
    if (r.checked) out(`  ${paint('dim', r.checked)}`)
    const inferred = r.notes.filter(n => /inferred|tagged|left out|answered|injected|the entry/.test(n))
    for (const n of inferred.slice(0, 12)) out(`  ${n}`)
    out(`  ${paint('dim', 'names (the code\'s, then the rule\'s):')}`)
    const w = Math.min(36, Math.max(...r.names.map(n => label(n).length), 8))
    for (const n of r.names) out(`    ${paint('dim', `${label(n).padEnd(w)}  ${ROLE[n.role].padEnd(9)} ${n.rule}${n.none ? `${n.rule ? ', ' : ''}None: ${n.none}` : ''}${n.map ? ` (cells: ${n.map.fields.join(', ')}${n.map.tpl ? `; key ${JSON.stringify(n.map.tpl)}` : ''})` : ''}${n.role === 'const' ? String(n.value) : ''}`)}`)
  }
  const law = (l: LawOut, proposed: boolean) => {
    out(`    ${paint(VERDICT[l.verdict], l.verdict)}${' '.repeat(Math.max(0, 9 - l.verdict.length))}${l.name}${proposed ? '' : `  ${paint('dim', `(${l.where})`)}`}`)
    if (!proposed && l.verdict !== 'proven') out(`             ${l.expr}`)
    for (const c of l.cites ?? []) out(`             cites: ${c}`)
    if (l.cert) out(`             ${paint('dim', `certificate: ${l.cert}`)}`)
    if (l.run) for (const [i, s] of l.run.entries()) out(`             ${i === 0 ? 'run: ' : '     '}${paint('red', s)}`)
    if (l.replayed) out(`             ${l.replayed}`)
    for (const a of l.assumes ?? []) out(`             ${a}`)
    if (l.found) out(`             proven with what the search found: ${l.found.join('; ')}`)
    if (l.why && l.verdict !== 'proven') out(`             ${l.why}`)
    if (proposed) out(`             ${l.where}`)
  }
  if (r.laws.length) { out('  laws stated in the code:'); for (const l of r.laws) law(l, false) }
  if (r.proposed.length || r.brokenProposed) {
    out('  laws proposed (nothing written; state one with the comment under it):')
    for (const l of r.proposed) law(l, true)
    if (r.brokenProposed) out(`    (${r.brokenProposed} more proposed and broken by a run: not shown)`)
  }
  if (r.ok && !r.laws.length) out(`  no law stated: write one as \`${COMMENT[(Object.keys(LANG_NAME) as Lang[]).find(k => LANG_NAME[k] === r.lang)!]} gdp: law <name>: <expr>\` over the names above`)
  void o
  out()
}
const label = (n: Name) => (n.role === 'answer' ? `${n.code.split('.').pop()}(...)` : n.role === 'input' && n.method ? `${n.method}(${n.code})` : n.role === 'result' && n.method ? `${n.method}() result` : n.code)

const USAGE = `gdp-wired check <file|dir>... [--entry X] [--methods a,b] [--failures kept] [--on-error discard] [--json] [--ms 10000] [--no-propose] [--clock s|ms] [--cert <dir>]

Reads the rule in each file (Python, Ruby, Elixir, Java, Kotlin, Go, Rust, Swift, C, C++, TypeScript, Effect, XState), checks it
against the code by running both, proves the laws stated in the code (\`# gdp: law <name>: <expr>\`, \`// gdp: law ...\`,
@GdpLaw("<name>: <expr>")) and proposes others. Laws about two runs: \`<secret> never reaches <fields>\`, \`isolated by <argument>\`,
\`agrees with <Class>\`; a duration over the clock: \`now - t < 30 days\`; the clause a law answers: \`gdp: cite <law name>: <clause>\`;
--cert <dir> writes each proven law's certificate (its meta the citations). Exit code: 1 when a stated law is broken, 2 when
one couldn't be checked.`

// Every target's rules and their laws, and the exit code (1: a stated law broken; 2: one not checked).
export async function check(targets: string[], given: Partial<Opts> = {}, each?: (r: RuleOut) => void): Promise<{rules: RuleOut[], exit: number}> {
  const o: Opts = {ms: 10_000, propose: true, ...given}, all: RuleOut[] = []
  for (const p of targets) for (const t of targetsOf(p)) { const rs = await checkTarget(t, o); all.push(...rs); if (each) rs.forEach(each) }
  const stated = all.flatMap(r => r.laws)
  return {rules: all, exit: stated.some(l => l.verdict === 'broken') ? 1 : stated.some(l => l.verdict === 'not read') ? 2 : 0}
}
export async function main(argv: string[]): Promise<number> {
  const {cmd, targets, o} = args(argv)
  if (cmd !== 'check' || !targets.length) { out(USAGE); return cmd === 'help' || cmd === '--help' || cmd === '-h' || !cmd ? 0 : 2 }
  tint = colors(proc.env, !!proc.stdout.isTTY, !!o.json)
  const {rules: all, exit: code} = await check(targets, o, o.json ? undefined : r => printRule(r, o))
  const stated = all.flatMap(r => r.laws)
  if (o.json) out(JSON.stringify({rules: all.map(({source: _s, ...r}) => r), exit: code}, null, 1))
  else if (stated.length) { const n = (v: LawOut['verdict']) => stated.filter(l => l.verdict === v).length; out(`${paint('green', n('proven'))} of ${stated.length} stated laws proven, ${paint('red', n('broken'))} broken, ${paint('yellow', n('unknown'))} unknown, ${paint('yellow', n('not read'))} not read`) }
  return code
}

if (import.meta.url === `file://${proc.argv[1]}` || /\/(cli\.(ts|js)|gdp-wired)$/.test(proc.argv[1] ?? '')) {
  main(proc.argv.slice(2)).then(c => { proc.exitCode = c }, e => { out(`gdp-wired: ${(e as Error).message}`); proc.exitCode = 2 })
}
