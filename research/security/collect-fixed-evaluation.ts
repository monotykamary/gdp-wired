// Collect fixed-version reader evidence. This never scores paired security recall.
import {mkdirSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {basename, join} from 'node:path'
import {fileURLToPath} from 'node:url'
import {gunzipSync} from 'node:zlib'

type Refusal = {where: string, what: string}
type Rule = {entry?: string, ok: boolean, checked?: string, refusals: Refusal[], notes: string[]}
type Receipt = {target: {id: string, revision: string, path: string, entry: string, methods?: string[]}, id: string, mode: string, version: string, revision: string, resolvedCommit?: string, revisionKind?: string, status: string, reason?: string, integrityBefore?: boolean, integrityAfter?: boolean, sourceHashes?: {path: string, sha256: string}[], options: {check: boolean, failures: string, propose: boolean, security: boolean, lawFiles: unknown[]}, strictRecall: unknown, policyProof: string, vulnerableReplay: string, rules?: Rule[]}
type Plan = {id: string, revision: string, path: string, entry: string, methods?: string[], policy: {review: string, text: string, boundary: string, formalStatus: string, evidence: string[], lines: number[]}}
type Case = {id: string, fixed: {revision: string, sources: {path: string, sha256: string}[]}}
const args = process.argv.slice(2), dirs: string[] = []
let frontendBaseCommit = '', outDir = fileURLToPath(new URL('../../runs/fixed-reader/', import.meta.url))
for (let i = 0; i < args.length; i++) {
  const arg = args[i]!
  if (arg === '--frontend-revision') frontendBaseCommit = args[++i] ?? ''
  else if (arg === '--out') outDir = args[++i] ?? ''
  else if (arg.startsWith('--')) throw Error(`Unknown argument: ${arg}`)
  else dirs.push(arg)
}
if (!dirs.length || !outDir || !/^[a-f0-9]{40}$/.test(frontendBaseCommit)) throw Error('Usage: collect-fixed-evaluation.ts --frontend-revision <reader-git-commit> [--out <dir>] <receipt-dir> [...] (last attempt wins)')
const catalog = JSON.parse(readFileSync(new URL('./fixed-library-catalog.json', import.meta.url), 'utf8')) as {rows: Case[]}
const plan = JSON.parse(readFileSync(new URL('./fixed-library-policies.json', import.meta.url), 'utf8')) as {cases: Plan[]}
const attempts: (Receipt & {phase: string})[] = []
for (const dir of dirs) for (const file of readdirSync(dir).filter(f => f.endsWith('.log'))) {
  const line = readFileSync(join(dir, file), 'utf8').split('\n').find(l => l.startsWith('{') && l.includes('"encoding":"base64+gzip"'))
  if (!line) throw Error(`Missing receipt: ${dir}/${file}`)
  const r = JSON.parse(gunzipSync(Buffer.from(JSON.parse(line).data, 'base64')).toString('utf8')) as Receipt
  if (!catalog.rows.some(c => c.id === r.id) || r.mode !== 'fixed-reader-only' || r.version !== 'fixed' || r.strictRecall !== null || r.policyProof !== 'not-run' || r.vulnerableReplay !== 'not-run' || r.options.check !== true || r.options.failures !== 'kept' || r.options.propose || r.options.security || r.options.lawFiles.length) throw Error(`Unexpected evaluation protocol: ${r.id}`)
  if (attempts.some(a => a.id === r.id && a.phase === dir)) throw Error(`Duplicate case in one phase: ${r.id}`)
  attempts.push({...r, phase: dir})
}
const rows = catalog.rows.map(c => {
  const history = attempts.filter(r => r.id === c.id), r = history.at(-1), p = plan.cases.find(p => p.id === c.id)
  if (!r || !p || r.revision !== c.fixed.revision || p.revision !== c.fixed.revision) throw Error(`Missing or mismatched case: ${c.id}`)
  if (!r.target || r.target.id !== c.id || r.target.revision !== p.revision || r.target.path !== p.path || r.target.entry !== p.entry || JSON.stringify(r.target.methods) !== JSON.stringify(p.methods)) throw Error(`Mismatched reader target: ${c.id}`)
  if (!['reader-refused', 'read-and-conformance-checked', 'read-without-conformance-evidence', 'evaluation-error'].includes(r.status)) throw Error(`Invalid reader status: ${c.id}`)
  if (r.status !== 'evaluation-error') {
    if (!r.integrityBefore || !r.integrityAfter || r.sourceHashes?.length !== c.fixed.sources.length || c.fixed.sources.some(s => !r.sourceHashes?.some(t => t.path === s.path && t.sha256 === s.sha256))) throw Error(`Unverified source integrity: ${c.id}`)
    if (!r.rules?.length || (r.status === 'read-without-conformance-evidence' && (r.rules.some(x => !x.ok) || r.rules.every(x => !!x.checked))) || (r.status === 'reader-refused' && !r.rules.some(x => !x.ok && x.refusals.length)) || (r.status === 'read-and-conformance-checked' && r.rules.some(x => !x.ok || !x.checked))) throw Error(`Reader status has no evidence: ${c.id}`)
  }
  return {id: c.id, revision: r.revision, resolvedCommit: r.resolvedCommit ?? r.revision, revisionKind: r.revisionKind ?? 'commit', target: {path: p.path, entry: p.entry, methods: p.methods}, policy: p.policy,
    reader: {status: r.status, reason: r.reason, integrityBefore: !!r.integrityBefore, integrityAfter: !!r.integrityAfter, sourceHashes: r.sourceHashes ?? [], rules: r.rules ?? []},
    attempts: history.map(h => ({phase: basename(h.phase), status: h.status, reason: h.reason, refusals: h.rules?.flatMap(x => x.refusals) ?? []})),
    fixedPolicyProof: 'not-run', vulnerableReplay: 'not-run'}
})
const summary = {cases: rows.length, readAndChecked: rows.filter(r => r.reader.status === 'read-and-conformance-checked').length, readWithoutConformance: rows.filter(r => r.reader.status === 'read-without-conformance-evidence').length, refused: rows.filter(r => r.reader.status === 'reader-refused').length, errors: rows.filter(r => r.reader.status === 'evaluation-error').length, sourceEntriesVerified: rows.filter(r => r.reader.integrityBefore && r.reader.integrityAfter).reduce((n, r) => n + r.reader.sourceHashes.length, 0), strictRecall: null}
const report = {schema: 1, kind: 'fixed-library-reader-evaluation', frontendBaseCommit, frontendRevisionSource: 'collection-argument', scope: 'Fixed-version reader and conformance attempts only. Source-intent policy review is not a formal proof. No vulnerable revision was evaluated or replayed.', summary, rows}
mkdirSync(outDir, {recursive: true})
writeFileSync(join(outDir, 'fixed-library-reader-results.json'), JSON.stringify(report, null, 2) + '\n')
const text = (s: string) => s.replaceAll('|', '\\|').replaceAll('\n', ' ')
const table = rows.map(r => `| ${r.id} | ${r.reader.status} | ${text(r.reader.reason ?? r.reader.rules.flatMap(x => x.refusals).map(f => `${f.where}: ${f.what}`).join('; '))} |`).join('\n')
const details = rows.map(r => `## ${r.id}\n\n- Entry: \`${r.target.path}\`, \`${r.target.entry}${r.target.methods ? '.' + r.target.methods.join(', ') : ''}\`.\n- Reviewed intent: ${r.policy.text}\n- Boundary: ${r.policy.boundary}\n- Fixed policy proof: **not run**. Vulnerable-side replay: **not run**.\n` + (r.attempts.some(a => a.status === 'evaluation-error') ? `- Earlier evaluation errors retained: ${r.attempts.filter(a => a.status === 'evaluation-error').map(a => `${a.phase}: ${a.reason}`).join('; ')}.\n` : '')).join('\n')
writeFileSync(join(outDir, 'FIXED-READER-RESULTS.md'), `# Fixed-library reader evaluation\n\nThis is **not a strict paired-recall measurement**. All ${summary.cases} pinned fixed entries\nwere attempted with proposals and security-law search disabled. The result is\n**${summary.readAndChecked}/${summary.cases} read and conformance-checked, ${summary.refused} reader refusals, ${summary.errors} evaluation errors**,\nwith ${summary.sourceEntriesVerified} indexed source entries hash-verified before and after the final attempts.\nStrict recall is **not measured**, not 0/${summary.cases}; no vulnerable revision was run or\nreplayed, and no fixed policy proof is claimed. Source-intent notes are not formal laws.\n\nNo upstream source was edited. No dependency stubs, synthetic replacements or environment\nskips were added. The standard boat image was used, without installing upstream package\ndependencies. Every final refusal and any earlier evaluation error are retained below and\nin \`fixed-library-reader-results.json\`. Annotated Git tags are pinned as objects and\npeeled to a commit before checkout; both identifiers are retained in the result.\n\n| Advisory | Fixed reader result | Refusal or evaluation error |\n| --- | --- | --- |\n${table}\n\n${details}\n## Reproduction\n\nOn boat, install this repository's dependencies and run\n\`bun research/security/evaluate-fixed.ts <GHSA-id>\` for a selected fixed entry.\nThe output is a size-bounded base64/gzip receipt, not an exploit or a proof. Save logs,\nthen collect them with \`bun research/security/collect-fixed-evaluation.ts --frontend-revision <reader-git-commit> [--out <dir>] <log-dir> [...]\`;\nlater directories supersede earlier attempts while retaining their history.\n`)
console.log(JSON.stringify(summary))
if (summary.errors || summary.readWithoutConformance) process.exitCode = 1
