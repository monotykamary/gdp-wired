// Metadata only: no imports from catalog entries, subprocesses, network, or target execution.
import {createHash} from 'node:crypto'
import {existsSync, lstatSync, mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import {basename, isAbsolute, join, relative, resolve, sep} from 'node:path'

export type Document = {path: string, text: string}
export type Snapshot = {catalogs: Document[], documents: Document[], sent?: Document, readerExports: string[]}
type Provenance = {path: string, sha256: string, row: number}
export type Source = {
  repo: string, commit: string, pin: 'immutable' | 'unresolved', paths: string[], entry: string,
  languages: string[], licenses: string[], readers: string[], provenance: Provenance[], problems: string[],
}
export type History = {label: string, key: string, datedEntries: number, negativeNote: boolean, sha256: string}
export type Legacy = {
  path: string, sha256: string, bytes: number, mentionedRepositories: string[], mentionedCommits: string[],
  historyKeys: string[], evidenceStatus: 'historical-unverified', currentStatus: 'not-assessed',
}
const hash = (s: string) => createHash('sha256').update(s).digest('hex')
const sorted = (xs: string[]) => [...new Set(xs)].sort()
const object = (x: unknown): Record<string, unknown> => {
  if (typeof x !== 'object' || x === null || Array.isArray(x)) throw new Error('expected metadata object')
  return x as Record<string, unknown>
}
const text = (x: unknown) => typeof x === 'string' ? x : ''
const strings = (x: unknown) => Array.isArray(x) ? x.map(text).filter(Boolean) : []
function hasControlCharacter(s: string): boolean {
  for (let i = 0; i < s.length; i++) {
    const code = s.charCodeAt(i)
    if (code < 32 || code === 127) return true
  }
  return false
}
function safePath(s: string): string {
  if (!s || isAbsolute(s) || s.includes('\\') || hasControlCharacter(s) || s.split('/').some(p => p === '..' || p === '.' || !p))
    throw new Error('expected a relative metadata path without traversal')
  return s
}
function document(x: unknown): Document {
  const d = object(x)
  if (typeof d.text !== 'string' || typeof d.path !== 'string') throw new Error('invalid metadata document')
  return {path: safePath(d.path), text: d.text}
}
export function parseSnapshot(x: unknown): Snapshot {
  const s = object(x)
  if (!Array.isArray(s.catalogs) || !Array.isArray(s.documents) || !Array.isArray(s.readerExports) ||
      s.readerExports.some(e => typeof e !== 'string')) throw new Error('invalid snapshot schema')
  const catalogs = s.catalogs.map(document), documents = s.documents.map(document)
  const sent = s.sent === undefined ? undefined : document(s.sent)
  const paths = [...catalogs, ...documents, ...(sent ? [sent] : [])].map(d => d.path)
  if (new Set(paths).size !== paths.length) throw new Error('duplicate input path')
  return {catalogs, documents, sent, readerExports: s.readerExports as string[]}
}
export function repository(value: string): string | undefined {
  const m = /^(?:https:\/\/github\.com\/)?([A-Za-z0-9_-]+)\/([A-Za-z0-9_.-]+?)(?:\.git)?\/?$/.exec(value)
  if (!m || m[2] === '.' || m[2] === '..') return undefined
  return `${m[1]}/${m[2]}`.toLowerCase()
}
const readerByExtension: Record<string, string> = {
  ts: './extract', tsx: './extract', js: './extract', jsx: './extract', mjs: './extract', cjs: './extract',
  py: './extract-py', rb: './extract-rb', ex: './extract-ex', exs: './extract-ex', java: './extract-java',
  kt: './extract-kotlin', kts: './extract-kotlin', go: './extract-go', rs: './extract-rs', swift: './extract-swift',
  c: './extract-c', h: './extract-c', cc: './extract-cpp', cpp: './extract-cpp', hpp: './extract-cpp', sol: './extract-sol',
}
const readerByLanguage: Record<string, string> = {
  typescript: './extract', javascript: './extract', python: './extract-py', ruby: './extract-rb', elixir: './extract-ex',
  java: './extract-java', kotlin: './extract-kotlin', go: './extract-go', rust: './extract-rs', swift: './extract-swift',
  c: './extract-c', 'c++': './extract-cpp', solidity: './extract-sol',
}
export function sourceInventory(catalogs: Document[], readerExports: string[]): {sources: Source[], rejected: Provenance[]} {
  const byKey = new Map<string, Source>(), rejected: Provenance[] = []
  for (const doc of [...catalogs].sort((a, b) => a.path.localeCompare(b.path))) {
    const decoded: unknown = JSON.parse(doc.text)
    const rows: unknown[] = Array.isArray(decoded) ? decoded : [decoded]
    rows.forEach((item, row) => {
      const r = object(item), prov = {path: doc.path, sha256: hash(doc.text), row: row + 1}
      const repo = repository(text(r.repo))
      if (!repo) { rejected.push(prov); return }
      const declaredCommit = text(r.commit).trim()
      const pin = /^(?:[a-fA-F0-9]{40}|[a-fA-F0-9]{64})$/.test(declaredCommit) ? 'immutable' : 'unresolved'
      const commit = pin === 'immutable' ? declaredCommit.toLowerCase() : declaredCommit
      const candidates = [text(r.path), text(r.target), ...strings(r.check), ...strings(r.files)].filter(Boolean)
      const paths: string[] = [], problems: string[] = []
      for (const path of candidates) {
        try { paths.push(safePath(path)) } catch { problems.push('invalid-source-path') }
      }
      const licenses = sorted([text(r.license), text(r.licence)].filter(Boolean))
      if (!licenses.length) problems.push('missing-declared-license')
      if (pin === 'unresolved') problems.push('missing-or-mutable-pin')
      if (!paths.length) problems.push('missing-source-path')
      const languages = sorted([text(r.language), text(r.lang)].filter(Boolean))
      const hints = [...paths, text(r.file)].map(p => readerByExtension[p.split('.').pop()?.toLowerCase() ?? '']).filter((x): x is string => !!x)
      hints.push(...languages.map(l => readerByLanguage[l.toLowerCase()]).filter((x): x is string => !!x))
      const readers = sorted(hints.filter(h => readerExports.includes(h)))
      if (!readers.length) problems.push('no-registered-reader-hint')
      const entry = text(r.entry) || text(r.export)
      const key = JSON.stringify([repo, commit, sorted(paths), entry])
      const previous = byKey.get(key)
      if (previous) {
        previous.licenses = sorted([...previous.licenses, ...licenses])
        previous.languages = sorted([...previous.languages, ...languages])
        previous.readers = sorted([...previous.readers, ...readers])
        previous.problems = sorted([...previous.problems, ...problems])
        previous.provenance.push(prov)
      } else {
        byKey.set(key, {repo, commit, pin, paths: sorted(paths), entry, languages, licenses, readers, provenance: [prov], problems: sorted(problems)})
      }
    })
  }
  return {sources: [...byKey.values()].sort((a, b) => JSON.stringify([a.repo, a.commit, a.paths, a.entry]).localeCompare(JSON.stringify([b.repo, b.commit, b.paths, b.entry]))), rejected}
}
const historyKey = (label: string) => label.replace(/\s*\([^)]*\)\s*$/, '').trim().toLowerCase()
export function sentHistory(doc?: Document): History[] {
  if (!doc) return []
  const parts = doc.text.split(/^##\s+(.+)\r?$/m), result: History[] = []
  for (let i = 1; i + 1 < parts.length; i += 2) {
    const label = parts[i]!.trim(), body = parts[i + 1]!
    result.push({label, key: historyKey(label), datedEntries: (body.match(/^\s*-\s+\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ(?=[:,\s]|$)/gm) ?? []).length,
      negativeNote: /\b(?:not sent|nothing was sent|no new issue|skipped by the user)\b/i.test(body), sha256: hash(body)})
  }
  return result
}
export function legacyInventory(docs: Document[], history: History[]): Legacy[] {
  return [...docs].sort((a, b) => a.path.localeCompare(b.path)).map(doc => {
    const mentionedRepositories = sorted([...doc.text.matchAll(/https:\/\/github\.com\/([\w-]+\/[\w.-]+)/g)]
      .map(m => repository(m[1]!) ?? '').filter(Boolean))
    const key = basename(doc.path, '.md').toLowerCase()
    return {path: doc.path, sha256: hash(doc.text), bytes: Buffer.byteLength(doc.text), mentionedRepositories,
      mentionedCommits: sorted((doc.text.match(/\b[a-fA-F0-9]{40}\b/g) ?? []).map(s => s.toLowerCase())),
      historyKeys: history.filter(h => h.key === key).map(h => h.key), evidenceStatus: 'historical-unverified', currentStatus: 'not-assessed'}
  })
}
// A spreadsheet import must not interpret catalog text as a formula.
export function csvCell(s: string): string {
  const safe = /^\s*[=+@-]/.test(s) || /^[\t\r\n]/.test(s) ? `'${s}` : s
  return `"${safe.replaceAll('"', '""')}"`
}
const csv = (rows: string[][]) => rows.map(row => row.map(csvCell).join(',')).join('\n') + '\n'
export const ledgerHeader = 'id,repo,commit,license,file_line,law,class,severity,reasoning,reproduction_path,status,notes\n'
export function buildInventory(snapshot: Snapshot) {
  const {sources, rejected} = sourceInventory(snapshot.catalogs, snapshot.readerExports)
  const history = sentHistory(snapshot.sent), legacy = legacyInventory(snapshot.documents, history)
  const repositories = sorted(sources.map(s => s.repo)).map(repo => {
    const rows = sources.filter(s => s.repo === repo)
    const pins = sorted(rows.map(s => s.commit).filter(Boolean))
    const licenseSets = pins.map(pin => sorted(rows.filter(r => r.commit === pin).flatMap(r => r.licenses)))
    return {repo, pins, licenses: sorted(rows.flatMap(r => r.licenses)), readerHints: sorted(rows.flatMap(r => r.readers)),
      sourceRecords: rows.length, licenseConflictAtPin: licenseSets.some(ls => ls.length > 1)}
  })
  const summary = {schemaVersion: 1, scope: 'metadata-only', catalogs: snapshot.catalogs.length,
    inputCatalogRows: sources.reduce((n, s) => n + s.provenance.length, 0) + rejected.length,
    sourceRecords: sources.length, repositories: repositories.length,
    immutableSourceRecords: sources.filter(s => s.pin === 'immutable').length,
    unresolvedSourceRecords: sources.filter(s => s.pin !== 'immutable').length,
    missingLicenseRecords: sources.filter(s => !s.licenses.length).length,
    readerHintRecords: sources.filter(s => s.readers.length).length,
    licenseConflictRepositories: repositories.filter(r => r.licenseConflictAtPin).length,
    rejectedCatalogRows: rejected.length, legacyDocuments: legacy.length, historySections: history.length,
    historyDatedEntries: history.reduce((n, h) => n + h.datedEntries, 0),
    unmatchedHistoryKeys: history.filter(h => !legacy.some(d => d.historyKeys.includes(h.key))).map(h => h.key),
    unmatchedLegacyDocuments: legacy.filter(d => !d.historyKeys.length).map(d => d.path),
    targetRepositories: 300, targetMet: repositories.length >= 300,
    newVerifiedFindings: 0, executedTargets: 0, networkCalls: 0, ledgerRows: 0}
  const inputs = [...snapshot.catalogs, ...snapshot.documents, ...(snapshot.sent ? [snapshot.sent] : [])]
    .map(d => ({path: d.path, bytes: Buffer.byteLength(d.text), sha256: hash(d.text)})).sort((a, b) => a.path.localeCompare(b.path))
  const artifact = {summary, repositories, sources, rejected, legacy, history, inputs, readerExports: sorted(snapshot.readerExports)}
  const files: Record<string, string> = {
    'inventory.json': JSON.stringify(artifact, null, 2) + '\n',
    'SOURCES.csv': csv([['repo', 'commit', 'pin_status', 'declared_licenses', 'paths', 'entry', 'reader_hints', 'problems', 'provenance'],
      ...sources.map(s => [s.repo, s.commit, s.pin, s.licenses.join('; '), s.paths.join('; '), s.entry, s.readers.join('; '), s.problems.join('; '), JSON.stringify(s.provenance)])]),
    'REPOSITORIES.csv': csv([['repo', 'pins', 'declared_licenses', 'reader_hints', 'source_records', 'license_conflict_at_pin'],
      ...repositories.map(r => [r.repo, r.pins.join('; '), r.licenses.join('; '), r.readerHints.join('; '), String(r.sourceRecords), String(r.licenseConflictAtPin)])]),
    'LEGACY-REPORTS.csv': csv([['path', 'sha256', 'bytes', 'evidence_status', 'current_status', 'exact_history_keys', 'mentioned_repositories', 'mentioned_commits'],
      ...legacy.map(d => [d.path, d.sha256, String(d.bytes), d.evidenceStatus, d.currentStatus, d.historyKeys.join('; '), d.mentionedRepositories.join('; '), d.mentionedCommits.join('; ')])]),
    'LEDGER.proposed.csv': ledgerHeader,
    'REPORT.md': `# Private metadata inventory\n\nScope: metadata only; no target execution, network calls, vulnerability checks or new verification.\n\n` +
      `- ${summary.repositories} distinct repositories, ${summary.sourceRecords} source records from ${summary.inputCatalogRows} catalog rows.\n` +
      `- ${summary.immutableSourceRecords} records declare a full immutable pin; ${summary.unresolvedSourceRecords} unresolved. Pins were not fetched or attested.\n` +
      `- ${summary.missingLicenseRecords} records lack a declared license; ${summary.licenseConflictRepositories} repositories have differing declarations at the same pin. Licenses are catalog assertions, not legal review or checked license files.\n` +
      `- ${summary.readerHintRecords} records have a registered reader hint. This does NOT establish successful extraction, conformance, or a proof.\n` +
      `- ${summary.legacyDocuments} legacy documents hashed; ${summary.historySections} historical send sections with ${summary.historyDatedEntries} dated entries. Dates are claims in SENT.md, not external confirmation. Negative notes and dated entries can coexist.\n` +
      `- ${summary.unmatchedLegacyDocuments.length} documents have no exact filename/history match; ${summary.unmatchedHistoryKeys.length} history sections have no document match. No fuzzy association or per-finding send status was inferred.\n` +
      `- Target: 300 repositories; ${summary.targetMet ? 'metadata count met' : 'NOT MET'}. This is an existing-catalog inventory, not a new repository census.\n\n` +
      `## Evidence boundaries\n\nEvery legacy document remains historical-unverified / not-assessed. Mentioned hashes and repositories are not source bindings. One document can cover multiple findings; no finding-level row is invented. LEDGER.proposed.csv is deliberately header-only. Historical sends never authorize another send. No current approvals, sent status, severity, law, reproduction, fix, or affected-version assertion is inferred.\n\n` +
      `Coordinator owns the canonical LEDGER.csv, approvals and Sheet. This directory is a private review packet, not a disclosure or an approval request. Follow-up: resolve missing metadata and exact report-to-finding mappings by review; do not execute legacy reproducers.\n`,
  }
  files['SHA256SUMS'] = Object.entries(files).sort(([a], [b]) => a.localeCompare(b)).map(([name, value]) => `${hash(value)}  ${name}`).join('\n') + '\n'
  return {summary, files}
}
export function writeInventory(snapshot: Snapshot, out: string, workspace = process.cwd()) {
  const root = resolve(workspace), target = resolve(root, out), rel = relative(root, target)
  if (!rel.startsWith(`runs${sep}`) || rel.split(sep).some(p => p === '..') || isAbsolute(rel)) throw new Error('output must be a new directory under runs/')
  let current = root
  for (const part of rel.split(sep)) {
    current = join(current, part)
    if (existsSync(current) && lstatSync(current).isSymbolicLink()) throw new Error('symlink output path refused')
  }
  if (existsSync(target)) throw new Error('output already exists; use a fresh run name')
  const result = buildInventory(snapshot)
  mkdirSync(join(target, '..'), {recursive: true, mode: 0o700})
  mkdirSync(target, {mode: 0o700})
  for (const [name, value] of Object.entries(result.files)) writeFileSync(join(target, name), value, {encoding: 'utf8', mode: 0o600, flag: 'wx'})
  return result.summary
}
if (import.meta.main) {
  const args = process.argv.slice(2)
  if (args.length !== 4 || args[0] !== '--snapshot' || args[2] !== '--out') {
    console.error('Usage: bun research/audit/inventory.ts --snapshot <metadata.json> --out runs/private/disclosure/<new-run>')
    process.exitCode = 1
  } else {
    try {
      const snapshot = parseSnapshot(JSON.parse(readFileSync(args[1]!, 'utf8')) as unknown)
      const summary = writeInventory(snapshot, args[3]!)
      console.log(JSON.stringify(summary))
    } catch (error) {
      console.error(error instanceof Error ? error.message : 'inventory failed')
      process.exitCode = 1
    }
  }
}
