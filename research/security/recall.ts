// Pinned, published/fixed vulnerabilities and deliberately vulnerable training code only.
// Run on boat: bun research/security/recall.ts <id>. Original checkout stays under runs/.
// A reader refusal is an outcome, not a detection. No synthetic stand-in is substituted.
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {check} from '../../core/cli.ts'
import {scoreRecall} from './score.ts'

type Case = {id: string, set: string, advisory: string, repo: string, before: string, after?: string, path: string, entry: string, methods?: string[], policy: string}
const cases = JSON.parse(readFileSync(new URL('./cases.json', import.meta.url), 'utf8')) as Case[]
const c = cases.find(c => c.id === process.argv[2])
if (!c) throw new Error('Choose a pinned case in cases.json')
const root = resolve('runs/security-recall', c.id)
mkdirSync(root, {recursive: true})
const results: {version: string, status: string, result?: Awaited<ReturnType<typeof check>>, [key: string]: unknown}[] = []
const versions: [string, string][] = [['vulnerable', c.before], ...(c.after ? [['fixed', c.after] as [string, string]] : [])]
for (const [version, sha] of versions) {
  const dir = resolve(root, version!)
  mkdirSync(dir, {recursive: true})
  const git = (args: string[]) => {
    const p = spawnSync('git', ['-C', dir, ...args], {encoding: 'utf8', timeout: 180_000, maxBuffer: 4 << 20, env: {...process.env, GIT_TERMINAL_PROMPT: '0'}})
    if (p.status !== 0) throw new Error(`git ${args[0]} failed: ${p.error?.message ?? p.stderr.slice(-600)}`)
  }
  const start = performance.now()
  try {
    if (!/^[a-f0-9]{40}$/.test(sha!) || !/^[\w-]+\/[\w.-]+$/.test(c.repo)) throw new Error('Not a pinned public revision')
    git(['init', '-q'])
    git(['fetch', '-q', '--depth=1', `https://github.com/${c.repo}.git`, sha!])
    git(['checkout', '-q', '--detach', 'FETCH_HEAD'])
    const path = resolve(dir, c.path), bytes = readFileSync(path)
    const sourceSha256 = createHash('sha256').update(bytes).digest('hex')
    const begin = performance.now()
    const result = await check([path], {entry: c.entry, methods: c.methods, root: dir, propose: false, security: true, ms: 5000})
    // Candidate intent is not known. Even a broken candidate is not counted as recall without an accepted
    // policy and its concrete run replayed against this revision, and a corresponding fixed-side result.
    results.push({version, sha, sourceSha256, source: bytes.toString('utf8'), checkMs: performance.now() - begin, wallMs: performance.now() - start,
      status: result.rules.some(r => !r.ok) ? 'refused' : 'needs-reviewed-policy-and-original-replay', result})
  } catch (e) { results.push({version, sha, status: 'error', why: String(e), wallMs: performance.now() - start}) }
}
const receipt = {id: c.id, set: c.set, advisory: c.advisory, policy: c.policy, ...scoreRecall(results, c.set === 'training'), results}
writeFileSync(resolve(root, 'result.json'), JSON.stringify(receipt, null, 2))
console.log(JSON.stringify(receipt))
