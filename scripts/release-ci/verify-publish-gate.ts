import {createHash} from 'node:crypto'
import {execFileSync} from 'node:child_process'
import {verifyReleaseReceipt} from './full-gate-contract'

const sha256 = (bytes: Uint8Array) => createHash('sha256').update(bytes).digest('hex')
const git = (...args: string[]): Buffer => execFileSync('git', args, {encoding: 'buffer', maxBuffer: 16 * 1024 * 1024})
const gitText = (...args: string[]) => git(...args).toString('utf8').trim()

/** Validate the combined-status HTTP response without trusting its overall state. */
export function validateReleaseGateStatus(httpStatus: number, body: unknown, commit: string, receiptSha256: string): void {
  if (httpStatus !== 200) throw new Error(`GitHub combined status HTTP ${httpStatus}`)
  if (!/^[0-9a-f]{40}$/.test(commit) || !/^[0-9a-f]{64}$/.test(receiptSha256)) throw new Error('invalid expected commit or receipt digest')
  if (!body || typeof body !== 'object') throw new Error('invalid combined status response')
  const response = body as {sha?: unknown, total_count?: unknown, statuses?: unknown}
  if (response.sha !== commit || !Array.isArray(response.statuses) || !Number.isSafeInteger(response.total_count) || response.total_count !== response.statuses.length) {
    throw new Error('wrong commit or incomplete combined status response')
  }
  const matches = response.statuses.filter((s: unknown) => s !== null && typeof s === 'object' && (s as {context?: unknown}).context === 'release-full-gate')
  if (matches.length !== 1) throw new Error('missing or ambiguous release-full-gate status')
  const status = matches[0] as {state?: unknown, description?: unknown}
  if (status.state !== 'success' || status.description !== `receipt-sha256:${receiptSha256}`) throw new Error('release-full-gate status is not a success for these receipt bytes')
}

async function main() {
  const repo = process.env.RELEASE_GATE_REPOSITORY ?? process.env.GITHUB_REPOSITORY ?? 'monotykamary/gdp-wired'
  const ref = process.env.RELEASE_GATE_REGISTRY_REF ?? 'refs/remotes/origin/release-receipts'
  const token = process.env.GITHUB_TOKEN
  if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repo)) throw new Error('invalid repository')
  if (!/^refs\/(?:remotes|heads)\/[A-Za-z0-9_./-]+$/.test(ref) || ref.includes('..') || ref.endsWith('/') || ref.includes('//')) throw new Error('invalid registry ref')
  if (!token) throw new Error('GITHUB_TOKEN is required')
  const commit = gitText('rev-parse', '--verify', 'HEAD^{commit}')
  const tree = gitText('rev-parse', '--verify', `${commit}^{tree}`)
  const registry = gitText('rev-parse', '--verify', `${ref}^{commit}`)
  if (!/^[0-9a-f]{40}$/.test(commit) || !/^[0-9a-f]{40}$/.test(tree) || registry === commit) throw new Error('invalid source identity or registry is source commit')
  const suite = git('show', `${commit}:supercomputer/suite.json`)
  const canonicalJobs: unknown = JSON.parse(suite.toString('utf8'))
  if (!Array.isArray(canonicalJobs) || canonicalJobs.length === 0) throw new Error('canonical suite is empty or invalid')
  const vendorPins: Record<string, string> = {}
  for (const entry of git('ls-tree', '-rz', commit).toString('utf8').split('\0').filter(Boolean)) {
    const match = /^(\d+) (\w+) ([0-9a-f]{40})\t(.+)$/.exec(entry)
    if (!match) throw new Error('invalid git tree entry')
    if (match[1] === '160000') vendorPins[match[4]!] = match[3]!
  }
  if (Object.keys(vendorPins).length === 0) throw new Error('source tree has no gitlinks')
  const receiptPath = `full-gate/${commit}.json`
  const entry = gitText('ls-tree', registry, '--', receiptPath)
  if (!/^100644 blob [0-9a-f]{40}\t/.test(entry) || !entry.endsWith(`\t${receiptPath}`)) throw new Error('receipt is not a regular committed registry blob')
  const receiptBytes = git('show', `${registry}:${receiptPath}`)
  const receipt = JSON.parse(receiptBytes.toString('utf8'))
  const verified = verifyReleaseReceipt(receipt, {commit, tree, suiteSha256: sha256(suite), canonicalJobs, vendorPins})
  const response = await fetch(`https://api.github.com/repos/${repo}/commits/${commit}/status?per_page=100`, {
    headers: {Accept: 'application/vnd.github+json', Authorization: `Bearer ${token}`, 'X-GitHub-Api-Version': '2022-11-28'},
    signal: AbortSignal.timeout(30_000),
  })
  let body: unknown
  try { body = await response.json() } catch { throw new Error(`invalid GitHub status response (HTTP ${response.status})`) }
  validateReleaseGateStatus(response.status, body, commit, sha256(receiptBytes))
  console.log(JSON.stringify({commit, receiptSha256: sha256(receiptBytes), cleanupComplete: verified.cleanupComplete, openCustody: verified.openCustody}))
  console.log(`Full gate outcomes verified for ${commit}; receipt-sha256:${sha256(receiptBytes)}`)
}

if (import.meta.main) main().catch(error => { console.error('Full gate verification failed:', error); process.exitCode = 1 })
