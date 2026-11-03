// Original-revision Solidity harness audit, on boat. No original source is rewritten.
// bun research/security/solidity-harness.ts <case-id>
import {createHash} from 'node:crypto'
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import {resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {extractSolidity} from '../../core/extract-sol.ts'
import {check} from '../../core/cli.ts'

type Case = {id: string, repo: string, before: string, after: string, path: string, entry: string, methods?: string[], policy: string, advisory: string}
const cases = JSON.parse(readFileSync(new URL('./cases.json', import.meta.url), 'utf8')) as Case[]
const c = cases.find(c => c.id === process.argv[2] && c.id.startsWith('oz-'))
if (!c) throw new Error('Choose an OpenZeppelin case in cases.json')
const flag = (name: string): string | undefined => { const i = process.argv.indexOf(name); return i < 0 ? undefined : process.argv[i + 1] }
const harnessFile = flag('--harness-file'), harnessEntry = flag('--harness-entry')
if (harnessEntry && !harnessFile) throw new Error('--harness-entry requires --harness-file')
const harness = harnessFile ? {file: harnessFile, ...(harnessEntry ? {entry: harnessEntry} : {})} : undefined
const baseline = JSON.parse(readFileSync(new URL('./measurement.json', import.meta.url), 'utf8')) as {rows: {id: string, sides: {version: string, sourceSha256: string}[]}[]}
const expected = baseline.rows.find(r => r.id === c.id)
const root = resolve('runs/security-solidity-harness', c.id)
mkdirSync(root, {recursive: true})
const sides: Record<string, unknown>[] = []
for (const [version, sha] of [['vulnerable', c.before], ['fixed', c.after]]) {
  const dir = resolve(root, version!)
  mkdirSync(dir, {recursive: true})
  const git = (...args: string[]): string => {
    const p = spawnSync('git', ['-C', dir, ...args], {encoding: 'utf8', timeout: 180_000, maxBuffer: 4 << 20, env: {...process.env, GIT_TERMINAL_PROMPT: '0'}})
    if (p.status !== 0) throw new Error(`git ${args[0]}: ${p.error?.message ?? p.stderr.slice(-600)}`)
    return p.stdout.trim()
  }
  try {
    if (!/^[a-f0-9]{40}$/.test(sha!) || !/^[\w-]+\/[\w.-]+$/.test(c.repo)) throw new Error('Expected a pinned public source')
    git('init', '-q'); git('fetch', '-q', '--depth=1', `https://github.com/${c.repo}.git`, sha!); git('checkout', '-q', '--detach', 'FETCH_HEAD')
    if (git('rev-parse', 'HEAD') !== sha) throw new Error('Checkout is not the pinned revision')
    const path = resolve(dir, c.path), bytes = readFileSync(path), sourceSha256 = createHash('sha256').update(bytes).digest('hex')
    const prior = expected?.sides.find(s => s.version === version)
    if (!prior || prior.sourceSha256 !== sourceSha256) throw new Error('Original source hash does not match the prior measurement')
    const options = {entry: c.entry, methods: c.methods, root: dir, ...(harness ? {harness} : {})}
    const start = performance.now(), x = extractSolidity(path, options)
    // No reviewed law is invented by this audit. A readable target still needs the policy, replay and fixed check.
    const result = x.ok ? await check([path], {...options, propose: false, security: true, ms: 5000}) : undefined
    if (git('status', '--porcelain', '--untracked-files=all')) throw new Error('A harness modified the original checkout')
    sides.push({version, sha, sourceSha256, originalUnchanged: true, elapsedMs: performance.now() - start,
      status: x.ok ? 'needs-reviewed-policy-and-original-replay' : 'refused', harness: x.harness ?? null,
      notes: x.notes, refusals: x.refusals, evidence: x.evidence, result})
  } catch (error) { sides.push({version, sha, status: 'error', why: String(error)}) }
}
const report = {id: c.id, advisory: c.advisory, policy: c.policy, options: {entry: c.entry, methods: c.methods, harness}, found: false, sides}
writeFileSync(resolve(root, 'result.json'), JSON.stringify(report, null, 2))
console.log(JSON.stringify(report))
if (sides.some(s => s.status === 'error')) process.exitCode = 1
