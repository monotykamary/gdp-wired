// Fixed versions only: extraction/conformance, without law search or exploit replay.
import {createHash} from 'node:crypto'
import {spawnSync} from 'node:child_process'
import {mkdtempSync, readFileSync, rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {resolve} from 'node:path'
import {fileURLToPath} from 'node:url'
import {gzipSync} from 'node:zlib'
import {checkTarget} from '../../core/cli.ts'

const root = fileURLToPath(new URL('../../', import.meta.url))
const languages = {Go: 'go', Python: 'python', TypeScript: 'ts', Rust: 'rust'} as const
interface Case {id: string, repo: string, language: keyof typeof languages, fixed: {revision: string, sources: {path: string, sha256: string}[]}}
interface Target {id: string, revision: string, path: string, entry: string, methods?: string[]}
const catalog = JSON.parse(readFileSync(resolve(root, 'research/security/fixed-library-catalog.json'), 'utf8')) as {rows: Case[]}
const targets = (JSON.parse(readFileSync(resolve(root, 'research/security/fixed-library-policies.json'), 'utf8')) as {cases: Target[]}).cases
const c = catalog.rows.find(c => c.id === process.argv[2]), target = targets.find(t => t.id === process.argv[2])
if (!c || !target || !/^[a-f0-9]{40}$/.test(c.fixed.revision) || !/^[\w-]+\/[\w.-]+$/.test(c.repo)) throw Error('Choose a pinned fixed catalog entry')
if (target.revision !== c.fixed.revision || !c.fixed.sources.some(s => s.path === target.path)) throw Error('Target is outside the indexed fixed sources')
const dir = mkdtempSync(resolve(tmpdir(), 'gdp-fixed-reader-'))
const hash = (bytes: Uint8Array) => createHash('sha256').update(bytes).digest('hex')
const git = (...args: string[]) => {
  const p = spawnSync('git', ['-C', dir, ...args], {encoding: 'utf8', timeout: 120_000, maxBuffer: 4 << 20, env: {...process.env, GIT_TERMINAL_PROMPT: '0'}})
  if (p.status !== 0) throw Error(`git ${args[0]}: ${p.error?.message ?? p.stderr.slice(-1000)}`)
  return p.stdout.trim()
}
const start = performance.now()
let receipt: Record<string, unknown> = {id: c.id, version: 'fixed', revision: c.fixed.revision, target,
  mode: 'fixed-reader-only', policyProof: 'not-run', vulnerableReplay: 'not-run', strictRecall: null,
  options: {check: true, failures: 'kept', propose: false, security: false, lawFiles: []}}
try {
  git('init', '-q')
  git('fetch', '-q', '--depth=1', `https://github.com/${c.repo}.git`, c.fixed.revision)
  const fetched = git('rev-parse', 'FETCH_HEAD')
  if (fetched !== c.fixed.revision) throw Error('Fixed revision mismatch')
  const commit = git('rev-parse', 'FETCH_HEAD^{commit}')
  git('checkout', '-q', '--detach', commit)
  if (git('rev-parse', 'HEAD') !== commit) throw Error('Fixed commit mismatch')
  receipt = {...receipt, resolvedCommit: commit, revisionKind: fetched === commit ? 'commit' : 'annotated-tag'}
  const before = c.fixed.sources.map(s => ({path: s.path, sha256: hash(readFileSync(resolve(dir, s.path)))}))
  if (before.some((s, i) => s.sha256 !== c.fixed.sources[i]!.sha256)) throw Error('Fixed source hash mismatch before reading')
  receipt = {...receipt, sourceHashes: before, integrityBefore: true}
  const rules = await checkTarget({lang: languages[c.language], at: resolve(dir, target.path), files: []},
    {entry: target.entry, methods: target.methods, root: dir, check: true, failures: 'kept', propose: false, security: false, ms: 2000})
  if (!rules.length) throw Error('Reader returned no matching rule')
  if (rules.some(r => r.laws.length || r.proposed.length)) throw Error('Unexpected law search in reader-only run')
  if (before.some(s => hash(readFileSync(resolve(dir, s.path))) !== s.sha256) || git('status', '--porcelain', '--untracked-files=no')) throw Error('Tracked fixed source changed while reading')
  receipt = {...receipt, integrityAfter: true, status: rules.some(r => !r.ok) ? 'reader-refused' : rules.every(r => !!r.checked) ? 'read-and-conformance-checked' : 'read-without-conformance-evidence',
    rules: rules.map(r => ({file: target.path, entry: r.entry, ok: r.ok, checked: r.checked, refusals: r.refusals, notes: r.notes, names: r.names}))}
} catch (e) {
  receipt = {...receipt, status: 'evaluation-error', reason: String(e)}
} finally {
  rmSync(dir, {recursive: true, force: true})
}
receipt.wallMs = performance.now() - start
const data = gzipSync(JSON.stringify(receipt)).toString('base64')
if (data.length > 55000) throw Error('Receipt exceeds retained-output budget')
console.log(JSON.stringify({encoding: 'base64+gzip', data}))
if (receipt.status === 'evaluation-error') process.exitCode = 1
