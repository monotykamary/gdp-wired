import {createHash} from 'node:crypto'
import { canonicalJobHash } from './full-gate-contract'

export type LeanSourceEvidence = {file: string; source: string}

export type FailureSignature = { failedTests: string[]; diagnostics: string[] }
export type KnownFailureEntry = { job: string; definitionSha256: string; exitCode: number; signature: FailureSignature }
export type KnownFailuresPolicy = { schema: 'gdp-known-failures/v1'; baselineCommit: string; evidence: { triageSha256: string; comparisonSha256: string }; entries: KnownFailureEntry[]; requiredPass: string[] }

const fail = (message: string): never => { throw Error(`known-failures: ${message}`) }
const record = (v: unknown): Record<string, unknown> => v !== null && typeof v === 'object' && !Array.isArray(v) ? v as Record<string, unknown> : fail('expected object')
const keys = (o: Record<string, unknown>, expected: string[]) => { if (Object.keys(o).sort().join('\0') !== expected.sort().join('\0')) fail('unexpected or missing keys') }
const strings = (v: unknown): string[] => Array.isArray(v) && v.every(x => typeof x === 'string' && x.length > 0) ? v as string[] : fail('expected nonempty strings')
const signature = (value: unknown): FailureSignature => {
  const o = record(value); keys(o, ['failedTests', 'diagnostics'])
  const failedTests = strings(o.failedTests), diagnostics = strings(o.diagnostics)
  if (!failedTests.length && !diagnostics.length) fail('empty signature')
  return {failedTests, diagnostics}
}
const same = (a: string[], b: string[]) => JSON.stringify([...a].sort()) === JSON.stringify([...b].sort())

export function validateKnownFailuresPolicy(policy: unknown, canonicalJobs: readonly {name: string; cmd: string; [key: string]: unknown}[]): KnownFailuresPolicy {
  const p = record(policy); keys(p, ['schema','baselineCommit','evidence','entries','requiredPass'])
  if (p.schema !== 'gdp-known-failures/v1' || typeof p.baselineCommit !== 'string' || !/^[0-9a-f]{40}$/.test(p.baselineCommit)) fail('invalid schema or baseline')
  const evidence = record(p.evidence); keys(evidence, ['triageSha256','comparisonSha256'])
  if (![evidence.triageSha256, evidence.comparisonSha256].every(x => typeof x === 'string' && /^[0-9a-f]{64}$/.test(x))) fail('invalid evidence hash')
  const required = strings(p.requiredPass)
  if (new Set(required).size !== required.length) fail('duplicate required-pass job')
  if (!Array.isArray(p.entries)) return fail('entries must be an array')
  const entries: unknown[] = p.entries
  const jobs = new Map<string, string>()
  for (const job of canonicalJobs) { if (jobs.has(job.name)) fail('duplicate canonical job'); jobs.set(job.name, canonicalJobHash(job)) }
  if (required.some(x => !jobs.has(x)) || (jobs.has('exists') && !required.includes('exists'))) fail('invalid required-pass jobs')
  const seen = new Set<string>()
  for (const raw of entries) {
    const e = record(raw); keys(e, ['job','definitionSha256','exitCode','signature'])
    if (typeof e.job !== 'string') return fail('invalid job')
    const job = e.job
    if (job === 'exists' || !jobs.has(job) || seen.has(job) || required.includes(job)) fail('unexpected or duplicate job')
    seen.add(job)
    if (!Number.isInteger(e.exitCode) || (e.exitCode as number) <= 0 || jobs.get(job) !== e.definitionSha256) fail('exit or definition mismatch')
    signature(e.signature)
  }
  return policy as KnownFailuresPolicy
}

function bindKeyedSection(diagnostics: string[], rawSources: unknown): string[] {
  if (!Array.isArray(rawSources)) return fail('invalid Lean sources')
  const sources = new Map<string, string>()
  for (const raw of rawSources) {
    const source = record(raw); keys(source, ['file', 'source'])
    if (typeof source.file !== 'string' || !/^[A-Za-z0-9_-]+\.lean$/.test(source.file) || typeof source.source !== 'string' || !source.source.length || sources.has(source.file)) return fail('invalid or duplicate Lean source')
    sources.set(source.file, source.source)
  }
  const source = sources.get('Keyed.lean')
  if (source === undefined) return diagnostics
  const anchors = [...source.matchAll(/^def outbox_machine(?:\s|:)/gm)]
  if (anchors.length !== 1) return fail('missing or ambiguous Keyed outbox section')
  const index = anchors[0]!.index!, startLine = source.slice(0, index).split('\n').length
  const section = source.slice(index), endLine = source.split('\n').length
  const sectionHash = createHash('sha256').update(section).digest('hex')
  return diagnostics.map(item => {
    const location = /^Keyed\.lean:(\d+):(\d+): (?:error|warning):/.exec(item)
    if (!location) return item
    const line = Number(location[1]), column = Number(location[2])
    if (!Number.isSafeInteger(line) || !Number.isSafeInteger(column) || line < 1 || column < 1 || line > endLine) return fail('invalid Keyed diagnostic location')
    if (line < startLine) return item
    return item.replace(/^Keyed\.lean:\d+:\d+:/, `Keyed.lean:section=outbox_machine@${sectionHash}:${line - startLine + 1}:${column}:`)
  })
}

/** Normalization v2: strip ANSI SGR and Bun marker timing; replace absolute
 * prefixes before a Lean basename. For a search JSON export-failure record only,
 * replace its search.ms integer with 0. Preserve every other byte of diagnostic
 * bodies, file-qualified titles, error lines, line/column and multiplicity.
 * Keyed outbox diagnostics bind the complete source section hash and one-based
 * section-relative line instead of an unrelated prefix's absolute line count.
 * Original absolute lines remain in the native logs and captured source.
 * Complete Lean compiler/gate reports are authoritative, one per invocation.
 * A filtered wrapper mirror must preserve the header and an ordered subset of
 * that report's body lines; each report can account for at most one mirror. */
export function extractFailureSignature(stdout: string, stderr: string, leanDiagnostics: readonly string[] = [], leanSources: unknown = []): FailureSignature {
  // ANSI SGR escape bytes are the precise protocol sequence being removed.
  // eslint-disable-next-line no-control-regex
  const clean = (s: string) => s.replace(/\x1b\[[0-9;]*m/g, '')
  const outputs = [clean(stdout), clean(stderr)]
  const failedTests: string[] = [], failedTitles: string[] = [], bunErrors: string[] = [], summaryTests: string[] = []
  let footer = 0, summaryCount: number | undefined, inSummary = false
  for (const output of outputs) {
    let file = ''
    for (const line of output.split('\n')) {
      const fileHeader = /^((?!error:|warning:)[^\s:][^:\r\n]*\.[cm]?[jt]sx?):$/.exec(line)
      if (fileHeader) { file = fileHeader[1]!; inSummary = false; continue }
      const summary = /^(\d+) tests? failed:$/.exec(line)
      if (summary) { if (summaryCount !== undefined) fail('multiple Bun summaries'); summaryCount = Number(summary[1]); inSummary = true; continue }
      const marker = /^\(fail\) (.+?)(?: \[[0-9.]+m?s\])?$/.exec(line)
      if (marker) {
        if (inSummary) summaryTests.push(marker[1]!)
        else { failedTitles.push(marker[1]!); failedTests.push(file ? `${file} :: ${marker[1]!}` : marker[1]!) }
        continue
      }
      if (/\(fail\)/i.test(line)) fail('unrecognized Bun failure marker')
      if (inSummary && line === '') inSummary = false
      const f = /^\s*(\d+) fail\s*$/.exec(line)
      if (f) { footer += Number(f[1]); continue }
      if (/^\s*\d+ fail\b/.test(line)) fail('unrecognized Bun footer')
      if (/^(?:Unhandled|FATAL|fatal:|panic:|uncaughtException|Segmentation fault)/i.test(line)) fail('unrecognized fatal failure')
      if (/^error: /.test(line)) bunErrors.push(line)
  }
  }
  if (failedTests.length && (footer !== failedTests.length || !bunErrors.length)) fail('incomplete Bun report')
  if (summaryCount !== undefined && (summaryCount !== summaryTests.length || !same(summaryTests, failedTitles))) fail('Bun summary mismatch')
  if (!failedTests.length && footer) fail('Bun footer without markers')
  const parseLean = (input: string): string[] => {
    const lines = clean(input).replace(/(^|\s)(?:\/[^\s/:]+)+\/([^/\s]+\.lean:\d+:\d+:)/gm, '$1$2').split('\n')
    const result: string[] = []
    let block: string[] | undefined
    const flush = () => { if (block) { while (block.length && block[block.length - 1] === '') block.pop(); result.push(block.join('\n')); block = undefined } }
    for (const line of lines) {
      const header = /^(?:[^\s:]+\.lean:\d+:\d+: (?:error|warning):|error:|warning:)/.test(line)
      const axiom = /^'[^']+' depends on axioms: \[(.*)\]$/.exec(line)
      const search = /^\{/.test(line) && /"verdict"\s*:\s*"unknown"/.test(line) && /"search"\s*:/.test(line)
      const gate = /^(?:axiom-gate:|not-exported\b)/.test(line)
      const terminal = /^lean-exit \d+/.test(line)
      const sorry = /declaration uses 'sorry'/.test(line)
      if (header || axiom || gate || terminal || search || sorry) {
        flush()
        if (sorry || header && /(?:^error:|: error:)/.test(line)) block = [line]
        else if (axiom && axiom[1]!.split(',').map(x => x.trim()).filter(Boolean).some(x => !['propext','Classical.choice','Quot.sound'].includes(x))) result.push(line)
        else if (gate) result.push(line)
        else if (search) result.push(line.replace(/("search"\s*:\s*\{[^}]*?"ms"\s*:\s*)\d+/, '$10'))
      } else if (block) block.push(line)
    }
    flush()
    return result
  }
  const reports = leanDiagnostics.flatMap(parseLean)
  const header = (s: string) => s.split('\n')[0]!
  const diagnostics = [...reports], usedMirrors = new Set<number>()
  const isMirror = (item: string, report: string): boolean => {
    if (header(item) !== header(report)) return false
    const lines = report.split('\n')
    let cursor = 0
    return item.split('\n').every(line => {
      const found = lines.indexOf(line, cursor)
      if (found < 0) return false
      cursor = found + 1
      return true
    })
  }
  // Canonical tail/grep may omit body lines, never add or alter them. Matching
  // only headers would hide changed bodies and unlimited extra diagnostics.
  for (const item of outputs.flatMap(parseLean)) {
    if (failedTests.length && item.startsWith('error: ') && bunErrors.includes(header(item))) continue
    const mirror = reports.findIndex((report, index) => !usedMirrors.has(index) && isMirror(item, report))
    if (mirror >= 0) usedMirrors.add(mirror)
    else diagnostics.push(item)
  }
  if (!leanDiagnostics.length && diagnostics.some(x => /\.lean:\d+:\d+:.*error:/.test(x))) fail('complete Lean diagnostics required')
  return {failedTests: failedTests.sort(), diagnostics: [...(failedTests.length ? bunErrors : []), ...bindKeyedSection(diagnostics, leanSources)].sort()}
}

export function matchKnownFailure(policy: KnownFailuresPolicy, jobName: string, definitionSha256: string, code: number, value: FailureSignature): KnownFailureEntry {
  if (jobName === 'exists' || policy.requiredPass.includes(jobName)) return fail('required-pass job failed')
  const observed = signature(value), entry = policy.entries.find(e => e.job === jobName)
  if (!entry || entry.definitionSha256 !== definitionSha256 || entry.exitCode !== code || !same(entry.signature.failedTests, observed.failedTests) || !same(entry.signature.diagnostics, observed.diagnostics)) return fail('failure signature mismatch')
  return entry
}
