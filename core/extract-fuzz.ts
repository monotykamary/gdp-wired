// The reader fuzz: each language reader fed malformed, truncated and adversarial source, built on the extractor fuzz
// (the treadmill's xfuzz: each reader's own test file, core/extract-<lang>.test.ts, its check harness and its cases). It
// is that test file's preload: every extraction the tests make (extractPython, extractGo, extract, … through any caller,
// the CLI's too) is recorded, and after the tests (so they run, and are timed, as they always are) made again on
// mutants of its source, READER_FUZZ_N of them (2) a call, drawn from READER_FUZZ_SEED.
//   READER_FUZZ_SEED=7 bun test --preload ./extract-fuzz.ts extract-py.test.ts
// A mutant is a truncation, a junk token, a span cut out or doubled, deep nesting, a line dropped or doubled, odd
// bytes, or a change that leaves a program (an operator, a number, a name swapped). The source is mutated where it is
// (a file in place, restored after; a code string as given), so roots and options read as the tests give them: run it
// in a copy of the tree (a boat VM), as kernel/mutants.ts is. Each mutant must be:
//   - refused, each refusal with its reason (a reader's own crash, its stack trace or exception given as the reason, is
//     a crash: the reason must be about the source);
//   - or read, with the check (core/extract-check.ts's drive: the code run beside the rule) finding no difference.
// A throw, a refusal with no reason, a crash, or a mutant past READER_FUZZ_SLOW_MS (300 s) fails: a line `reader-fuzz:
// FAIL <kind> …` each. A mutant read and then refused by the check (the code and the rule differ on a request: a
// misread the check caught, no law proven of it) is `reader-fuzz: CAUGHT …`, a reader's inaccuracy to look at, not a
// failure: the check is the guard that stands there. The totals (`reader-fuzz: n mutants …`) after the tests. A hang
// past the job's limit: /tmp/reader-fuzz-<pid>.now names the mutant it was on.
import {afterAll, mock} from 'bun:test'
import {existsSync, readFileSync, readdirSync, statSync, utimesSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import * as ts from './extract.ts'
import * as py from './extract-py.ts'
import * as rb from './extract-rb.ts'
import * as ex from './extract-ex.ts'
import * as rs from './extract-rs.ts'
import * as swift from './extract-swift.ts'
import * as jvm from './extract-jvm.ts'
import * as go from './extract-go.ts'
import * as c from './extract-c.ts'
import * as sol from './extract-sol.ts'

const env = process.env
const N = Number(env.READER_FUZZ_N ?? 2), SLOW = Number(env.READER_FUZZ_SLOW_MS ?? 300_000), seed0 = (Number(env.READER_FUZZ_SEED ?? 1) >>> 0) || 1
const now = `/tmp/reader-fuzz-${process.pid}.now`
// xorshift32, one stream a run: the mutants depend on the seed and the order of the test's extractions alone
let s = seed0
const rnd = (n: number): number => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return n > 0 ? s % n : 0 }
const pick = <T>(xs: readonly T[]): T => xs[rnd(xs.length)]!

// --- the mutations ---------------------------------------------------------------------------------------------------
const junk = [')', '(', '}', '{', ']', '[', ';', ':', ',', '"', "'", '`', '/*', '*/', '#', '\\', '@', '$', '=>', '->', '::', '...', '0x', '1e999',
  '99999999999999999999999', '-', '!', '?', '\u0000', '﻿', '‮', 'é', '\u{1F642}', '\r', '\t', 'if', 'else', 'return', 'end', 'do',
  'class', 'def', 'fn', 'func', 'let', 'var', 'while', 'for', 'match', 'case', 'null', 'nil', 'None', 'self', 'this', 'super', 'import']
const ops: [string, string][] = [[' + ', ' - '], [' - ', ' + '], [' < ', ' <= '], [' <= ', ' < '], [' > ', ' >= '], [' >= ', ' > '], [' == ', ' != '],
  [' != ', ' == '], [' && ', ' || '], [' || ', ' && '], [' and ', ' or '], [' or ', ' and '], [' * ', ' + ']]
const nums = ['0', '1', '-1', '2', '255', '256', '65536', '2147483647', '2147483648', '4294967296', '9007199254740993', '18446744073709551616']
const at = (src: string, re: RegExp): RegExpExecArray | undefined => { const all = [...src.matchAll(re)]; return all.length ? all[rnd(all.length)] : undefined }
const splice = (src: string, i: number, del: number, ins: string) => src.slice(0, i) + ins + src.slice(i + del)
const lines = (src: string) => src.split('\n')
export const mutations: Record<string, (src: string) => string | undefined> = {
  truncate: src => src.slice(0, rnd(src.length)),
  'truncate at a line': src => lines(src).slice(0, rnd(lines(src).length)).join('\n'),
  junk: src => splice(src, rnd(src.length + 1), 0, pick(junk)),
  'junk at a line start': src => { const ls = lines(src), i = rnd(ls.length); ls[i] = `${pick(junk)} ${ls[i]}`; return ls.join('\n') },
  'cut a span': src => { const i = rnd(src.length); return splice(src, i, 1 + rnd(40), '') },
  'double a span': src => { const i = rnd(src.length), n = 1 + rnd(40); return splice(src, i, 0, src.slice(i, i + n)) },
  'drop a line': src => { const ls = lines(src); ls.splice(rnd(ls.length), 1); return ls.join('\n') },
  'double a line': src => { const ls = lines(src), i = rnd(ls.length); ls.splice(i, 0, ls[i]!); return ls.join('\n') },
  'swap two lines': src => { const ls = lines(src), i = rnd(ls.length), j = rnd(ls.length); [ls[i], ls[j]] = [ls[j]!, ls[i]!]; return ls.join('\n') },
  'nest deep': src => { const m = at(src, /\b\d+\b/g), d = pick([64, 512, 4096, 20_000]); return m && splice(src, m.index, m[0].length, `${'('.repeat(d)}${m[0]}${')'.repeat(d)}`) },
  'open deep': src => splice(src, rnd(src.length + 1), 0, pick(['(', '[', '{', '((', '"(']).repeat(pick([64, 4096, 20_000]))),
  'long line': src => splice(src, rnd(src.length + 1), 0, `x${'a'.repeat(100_000)}`),
  'odd bytes': src => splice(src, rnd(src.length + 1), 0, pick(['\u0000\u0001\u0002', '��', '\ud800', '\r\n\r', ' ', ' '])),
  empty: () => '',
  'an operator': src => { const [a, b] = pick(ops), m = at(src, new RegExp(a.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'g')); return m && splice(src, m.index, a.length, b) },
  'a number': src => { const m = at(src, /\b\d+\b/g); return m && splice(src, m.index, m[0].length, pick(nums)) },
  'a name': src => {
    const names = [...new Set([...src.matchAll(/\b[A-Za-z_]\w{2,}\b/g)].map(m => m[0]))], m = at(src, /\b[A-Za-z_]\w{2,}\b/g)
    return m && names.length > 1 ? splice(src, m.index, m[0].length, pick(names.filter(n => n !== m[0]))) : undefined
  },
}
const kinds = Object.keys(mutations)

// --- the source of an extraction -------------------------------------------------------------------------------------
const exts = /\.(py|rb|exs?|rs|swift|java|kt|go|c|h|cc|cpp|hpp|sol|[cm]?[jt]sx?)$/
const skip = new Set(['node_modules', 'target', '.build', 'build', '_build', 'deps', '.git', '__pycache__', '.lake'])
function sources(dir: string, depth = 0): string[] {
  if (depth > 4) return []
  return readdirSync(dir).flatMap(n => {
    const p = join(dir, n)
    if (skip.has(n)) return []
    try { return statSync(p).isDirectory() ? sources(p, depth + 1) : exts.test(n) ? [p] : [] } catch { return [] }
  })
}
let touched = 0
type Target = {code: string, write: (code: string) => unknown, restore: () => void, where: string}
// The text a call reads: a code string (TypeScript's code-first call, or {code}), else a file, or one file of a directory.
function target(arg: unknown): Target | undefined {
  if (typeof arg === 'object' && arg && 'code' in arg) { const o = arg as {code: string, file?: string}; return {code: o.code, where: o.file ?? '<code>', write: code => ({...o, code}), restore: () => {}} }
  if (typeof arg === 'string' && (arg.includes('\n') || !exts.test(arg)) && !existsSync(arg)) return {code: arg, where: '<code>', write: code => code, restore: () => {}}
  const p = typeof arg === 'string' ? arg : typeof arg === 'object' && arg && 'href' in arg ? new URL((arg as {href: string}).href).pathname : undefined
  if (!p || !existsSync(p)) return undefined
  const files = statSync(p).isDirectory() ? sources(p) : [p]
  if (!files.length) return undefined
  const f = pick(files), orig = readFileSync(f, 'utf8')
  // (restored with a later modification time each time: a cache keyed by the file's path and time reads it again)
  return {code: orig, where: f, write: code => { writeFileSync(f, code); return arg }, restore: () => { writeFileSync(f, orig); const t = Date.now() / 1000 + ++touched; utimesSync(f, t, t) }}
}

// --- the judge -------------------------------------------------------------------------------------------------------
type Out = {ok: boolean, refusals?: {where: string, what: string}[], evidence?: {mismatch?: string}}
// (a reader process's own crash given as the reason: a stack trace, a panic, an uncaught exception, the stack overflowed)
const crashLike = /Traceback \(most recent call last\)|panicked at|^panic:|goroutine \d+ \[|Exception in thread|\bat [\w.$]+\([\w]+\.(?:java|kt):\d+\)|Maximum call stack|SIGSEGV|stack overflow|Segmentation fault|reader failed on this source|\*\* \(\w+Error\) .*\n\s+\(/m
// (the check's own refusals: the code doesn't build or load, a difference on a request; what the code threw is the
// code's, not the reader's)
const CHECK = /^the rule and the code differ: /
const UNBUILT = /^the rule and the code differ: (the code doesn't load|the code doesn't compile|the (package|crate|file) doesn't build|the check's harness)/
export function judge(o: Out): {verdict: 'refused' | 'read' | 'crash' | 'no reason' | 'caught', why?: string} {
  if (o.ok) return o.evidence?.mismatch ? {verdict: 'no reason', why: `read, yet the check found ${o.evidence.mismatch}`} : {verdict: 'read'}
  const rs = o.refusals ?? []
  if (!rs.length || rs.some(r => !r.what?.trim())) return {verdict: 'no reason'}
  const crash = rs.find(r => !CHECK.test(r.what) && crashLike.test(r.what))
  if (crash) return {verdict: 'crash', why: crash.what}
  const caught = rs.find(r => CHECK.test(r.what) && !UNBUILT.test(r.what))
  return caught ? {verdict: 'caught', why: caught.what} : {verdict: 'refused'}
}

const tally: Record<string, number> = {}
let restoreNow: (() => void) | undefined
const short = (x: string, n = 400) => x.replace(/\s+/g, ' ').slice(0, n)
function fuzz(reader: string, call: (first: unknown) => unknown, first: unknown) {
  for (let i = 0; i < N; i++) {
    const t = target(first)
    if (!t) return
    const kind = pick(kinds), code = mutations[kind]!(t.code)
    if (code === undefined || code === t.code) { tally.unchanged = (tally.unchanged ?? 0) + 1; t.restore(); continue }
    const id = `${reader} ${t.where.split('/').slice(-2).join('/')} "${kind}" seed ${seed0} #${(tally.mutants ?? 0) + 1}`
    writeFileSync(now, id)
    const t0 = performance.now()
    let j: ReturnType<typeof judge>
    restoreNow = t.restore
    try { j = judge(call(t.write(code)) as Out) } catch (e) { j = {verdict: 'crash', why: `threw ${(e as Error)?.constructor?.name}: ${(e as Error)?.stack ?? String(e)}`} } finally { t.restore(); restoreNow = undefined }
    const ms = Math.round(performance.now() - t0)
    if (ms > SLOW && j.verdict !== 'crash') j = {verdict: 'crash', why: `slow: ${ms} ms`}
    tally.mutants = (tally.mutants ?? 0) + 1
    tally[j.verdict] = (tally[j.verdict] ?? 0) + 1
    if (j.verdict === 'crash' || j.verdict === 'no reason') console.log(`reader-fuzz: FAIL ${j.verdict} ${id} (${ms} ms): ${short(j.why ?? '')}`)
    if (j.verdict === 'caught') console.log(`reader-fuzz: CAUGHT ${id} (${ms} ms): ${short(j.why ?? '')}`)
  }
}
for (const sig of ['SIGINT', 'SIGTERM'] as const) process.on(sig, () => { restoreNow?.(); process.exit(130) })
process.on('exit', () => restoreNow?.())
const calls: {reader: string, call: (first: unknown) => unknown, first: unknown}[] = []
afterAll(() => {
  for (const c of calls) fuzz(c.reader, c.call, c.first)
  const f = (tally.crash ?? 0) + (tally['no reason'] ?? 0)
  console.log(`reader-fuzz: ${tally.mutants ?? 0} mutants (seed ${seed0}): ${tally.refused ?? 0} refused with a reason, ${tally.read ?? 0} read and checked, ${tally.caught ?? 0} caught by the check, ${f} failed (${tally.crash ?? 0} crash, ${tally['no reason'] ?? 0} no reason)`)
}, 24 * 3600_000)

// Each reader's entry points, wrapped: the call as made, recorded for its mutants after the tests.
const wrap = <F extends (...a: never[]) => unknown>(reader: string, f: F, argAt = 0): F => ((...a: Parameters<F>) => {
  calls.push({reader, call: x => f(...(a.map((y, i) => (i === argAt ? x : y)) as Parameters<F>)), first: a[argAt]})
  return f(...a)
}) as unknown as F
mock.module('./extract.ts', () => ({...ts, extract: wrap('typescript', ts.extract)}))
mock.module('./extract-py.ts', () => ({...py, extractPython: wrap('python', py.extractPython)}))
mock.module('./extract-rb.ts', () => ({...rb, extractRuby: wrap('ruby', rb.extractRuby)}))
mock.module('./extract-ex.ts', () => ({...ex, extractElixir: wrap('elixir', ex.extractElixir)}))
mock.module('./extract-rs.ts', () => ({...rs, extractRust: wrap('rust', rs.extractRust)}))
mock.module('./extract-swift.ts', () => ({...swift, extractSwift: wrap('swift', swift.extractSwift)}))
mock.module('./extract-jvm.ts', () => ({...jvm, extractJvm: wrap('jvm', jvm.extractJvm, 1), extractJava: wrap('java', jvm.extractJava), extractKotlin: wrap('kotlin', jvm.extractKotlin)}))
mock.module('./extract-go.ts', () => ({...go, extractGo: wrap('go', go.extractGo)}))
mock.module('./extract-c.ts', () => ({...c, extractC: wrap('c', c.extractC), extractCpp: wrap('cpp', c.extractCpp)}))
mock.module('./extract-sol.ts', () => ({...sol, extractSolidity: wrap('solidity', sol.extractSolidity)}))
