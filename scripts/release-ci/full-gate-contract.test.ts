import { describe, expect, test } from 'bun:test'
import { canonicalJobHash, verifyLostReproduction, verifyReleaseReceipt } from './full-gate-contract'

const commit = 'a'.repeat(40), tree = 'b'.repeat(40), vendor = 'c'.repeat(40)
const suite = 'd'.repeat(64), provisioning = 'e'.repeat(64), hash = 'f'.repeat(64)
const canonicalJobs = [{ name: 'first', cmd: 'bun test', cwd: 'pkg', env: { B: '2', A: '1' } }, { name: 'second', cmd: 'bun run build' }]
const expected = { commit, tree, suiteSha256: suite, canonicalJobs, vendorPins: { 'vendor/lib': vendor } }
const outputHashes = { stdoutSha256: hash, stderrSha256: hash, nativeReceiptSha256: hash }
function fixture(): any {
  return {
    schema: 'gdp-release-full-gate/v1', commit, tree, suiteSha256: suite, provisioningSha256: provisioning,
    submodules: { 'vendor/lib': vendor }, imagePins: [{ imageId: 'img-1', pinReceiptSha256: hash, protected: true, reference: 'gate-1' }],
    jobs: canonicalJobs.map((job, i) => ({
      name: job.name, nativeName: job.name, batchId: 'batch-1', definitionSha256: canonicalJobHash(job), commit, tree,
      provisioningSha256: provisioning, submodules: { 'vendor/lib': vendor }, imageId: 'img-1', status: 'SUCCEEDED', code: 0,
      attempts: 1, launchIdentity: `launch-${i}`, cleanupComplete: true, outputHashes: { ...outputHashes },
    })),
  }
}
function reproduced(): any {
  const r = fixture(), job = r.jobs[0]
  const originalLost = { ...job, status: 'LOST', code: -1, outputHashes: { stdoutSha256: null, stderrSha256: null, nativeReceiptSha256: hash } }
  r.jobs[0] = { ...job, batchId: 'batch-2', nativeName: 'first-repro-1', reproductionLabel: 'first-repro-1', provenance: 'independent-reproduction', launchIdentity: 'repro-launch', originalLost }
  return r
}

function policyFixture(): {receipt: any; trusted: any} {
  const jobs = [{name:'inherited',cmd:'bun test inherited'}, {name:'exists',cmd:'bun test exists'}]
  const policy = {schema:'gdp-known-failures/v1',baselineCommit:commit,evidence:{triageSha256:hash,comparisonSha256:hash},entries:[{job:'inherited',definitionSha256:canonicalJobHash(jobs[0]!),exitCode:1,signature:{failedTests:['known test'],diagnostics:['error: known assertion']}}],requiredPass:['exists']}
  const receipt = fixture()
  receipt.knownFailuresSha256 = hash
  receipt.jobs = jobs.map((job: any, i: number) => ({...receipt.jobs[0], name: job.name, nativeName: job.name, definitionSha256: canonicalJobHash(job), launchIdentity: `launch-${i}`}))
  const entry = policy.entries[0]!, execution = receipt.jobs.find((j: any) => j.name === entry.job)
  Object.assign(execution, {status: 'FAILED', code: 1, outcome: 'KNOWN_FAILURE', signature: structuredClone(entry.signature)})
  return {receipt, trusted: {...expected, canonicalJobs: jobs, trustedKnownFailuresPolicy: policy, knownFailuresSha256: hash}}
}

describe('full gate contract', () => {
  test('accepts exact policy failure and rejects policy hash or signature changes', () => {
    const {receipt, trusted} = policyFixture()
    const result = verifyReleaseReceipt(receipt, trusted)
    expect(result.knownFailures).toHaveLength(1)
    expect(result.counts.knownFailures).toBe(1)
    expect(() => verifyReleaseReceipt(receipt, {...trusted, knownFailuresSha256: '0'.repeat(64)})).toThrow()
    const altered = structuredClone(receipt)
    altered.jobs.find((j: any) => j.outcome === 'KNOWN_FAILURE').signature.diagnostics.push('unexpected failure')
    expect(() => verifyReleaseReceipt(altered, trusted)).toThrow()
    expect(() => verifyReleaseReceipt(receipt, {...expected, canonicalJobs: trusted.canonicalJobs})).toThrow()
  })
  test('required exists cannot fail or be removed from requiredPass', () => {
    const {receipt, trusted} = policyFixture()
    const exists = receipt.jobs.find((j: any) => j.name === 'exists')
    expect(exists).toBeDefined()
    Object.assign(exists, {status: 'FAILED', code: 1, outcome: 'KNOWN_FAILURE', signature: {failedTests: [], diagnostics: []}})
    expect(() => verifyReleaseReceipt(receipt, trusted)).toThrow()
    const policy = structuredClone(trusted.trustedKnownFailuresPolicy)
    policy.requiredPass = policy.requiredPass.filter((s: string) => s !== 'exists')
    expect(() => verifyReleaseReceipt(receipt, {...trusted, trustedKnownFailuresPolicy: policy})).toThrow()
  })
  test('hashes complete definitions with recursively stable key order', () => {
    const a = canonicalJobs[0]!
    expect(canonicalJobHash(a)).toBe(canonicalJobHash({ env: { A: '1', B: '2' }, cwd: 'pkg', cmd: 'bun test', name: 'first' }))
    expect(canonicalJobHash({ ...a, cmd: 'bun test --changed' })).not.toBe(canonicalJobHash(a))
    expect(() => canonicalJobHash({ name: 'x', cmd: 'x', bad: undefined })).toThrow()
  })
  test('accepts exactly covered successes and returns the receipt', () => {
    const r = fixture()
    expect(verifyReleaseReceipt(r, expected)).toEqual({ receipt: r, cleanupComplete: true, openCustody: [], knownFailures: [], counts: {succeeded: 2, knownFailures: 0, total: 2} })
  })
  test('preserves LOST and accepts a separately labelled independent success', () => {
    const r = reproduced()
    expect(() => verifyLostReproduction(r.jobs[0].originalLost, r.jobs[0])).not.toThrow()
    expect((verifyReleaseReceipt(r, expected).receipt.jobs[0]! as any).originalLost!.status).toBe('LOST')
  })
  test('reports original LOST open custody while preserving the independently superseded outcome', () => {
    const r = reproduced(); r.jobs[0].originalLost.cleanupComplete = false
    const result = verifyReleaseReceipt(r, expected)
    expect(result.cleanupComplete).toBe(false)
    expect((result.receipt.jobs[0]! as any).originalLost!.cleanupComplete).toBe(false)
    expect(result.openCustody).toEqual([{ name: 'first', batchId: 'batch-1', launchIdentity: 'launch-0', statement: 'LOST, custody open, superseded by passing labelled repro of same job/commit' }])
  })
  const negatives: [string, (r: any) => void][] = [
    ['skipped', r => r.jobs.pop()],
    ['duplicate', r => { r.jobs[1] = structuredClone(r.jobs[0]) }],
    ['extra', r => r.jobs.push(structuredClone(r.jobs[0]))],
    ['failed', r => { r.jobs[0].status = 'FAILED'; r.jobs[0].code = 1 }],
    ['wrong receipt SHA', r => { r.commit = '1'.repeat(40) }],
    ['wrong job SHA', r => { r.jobs[0].commit = '1'.repeat(40) }],
    ['wrong receipt tree', r => { r.tree = '1'.repeat(40) }],
    ['wrong job tree', r => { r.jobs[0].tree = '1'.repeat(40) }],
    ['wrong suite digest', r => { r.suiteSha256 = '1'.repeat(64) }],
    ['changed definition', r => { r.jobs[0].definitionSha256 = canonicalJobHash({ ...canonicalJobs[0]!, cmd: 'other' }) }],
    ['mixed vendor pins', r => { r.jobs[0].submodules['vendor/lib'] = '1'.repeat(40) }],
    ['missing vendor pin', r => { delete r.submodules['vendor/lib'] }],
    ['mixed provisioning', r => { r.jobs[0].provisioningSha256 = '1'.repeat(64) }],
    ['missing cleanup', r => { delete r.jobs[0].cleanupComplete }],
    ['unsafe cleanup', r => { r.jobs[0].cleanupComplete = false }],
    ['missing native evidence', r => { delete r.jobs[0].outputHashes.nativeReceiptSha256 }],
    ['attempts', r => { r.jobs[0].attempts = 2 }],
    ['unprotected image', r => { r.imagePins[0].protected = false }],
    ['unreferenced image', r => { r.imagePins[0].reference = '' }],
    ['unknown image', r => { r.jobs[0].imageId = 'other' }],
    ['normal native label differs', r => { r.jobs[0].nativeName = 'first-repro-1' }],
    ['duplicate launches', r => { r.jobs[1].launchIdentity = r.jobs[0].launchIdentity }],
  ]
  for (const [name, mutate] of negatives) test(`rejects ${name}`, () => {
    const r = fixture(); mutate(r); expect(() => verifyReleaseReceipt(r, expected)).toThrow()
  })
  const lostNegatives: [string, (r: any) => void][] = [
    ['FAILED disguised as LOST', r => { r.jobs[0].originalLost.status = 'FAILED' }],
    ['wrong native LOST code', r => { r.jobs[0].originalLost.code = 1 }],
    ['failed reproduction', r => { r.jobs[0].status = 'FAILED'; r.jobs[0].code = 1 }],
    ['unlabelled reproduction', r => { delete r.jobs[0].reproductionLabel }],
    ['missing independent provenance', r => { delete r.jobs[0].provenance }],
    ['wrong native label', r => { r.jobs[0].nativeName = 'second-repro-1' }],
    ['zero reproduction number', r => { r.jobs[0].nativeName = r.jobs[0].reproductionLabel = 'first-repro-0' }],
    ['wrong original job', r => { r.jobs[0].originalLost.name = 'second' }],
    ['wrong original definition', r => { r.jobs[0].originalLost.definitionSha256 = '1'.repeat(64) }],
    ['wrong original SHA', r => { r.jobs[0].originalLost.commit = '1'.repeat(40) }],
    ['wrong original tree', r => { r.jobs[0].originalLost.tree = '1'.repeat(40) }],
    ['wrong original provisioning', r => { r.jobs[0].originalLost.provisioningSha256 = '1'.repeat(64) }],
    ['same batch', r => { r.jobs[0].batchId = r.jobs[0].originalLost.batchId }],
    ['same launch', r => { r.jobs[0].launchIdentity = r.jobs[0].originalLost.launchIdentity }],
    ['missing original custody state', r => { delete r.jobs[0].originalLost.cleanupComplete }],
    ['unsafe reproduction cleanup', r => { r.jobs[0].cleanupComplete = false }],
    ['missing LOST native receipt', r => { delete r.jobs[0].originalLost.outputHashes.nativeReceiptSha256 }],
    ['missing original history', r => { delete r.jobs[0].originalLost }],
  ]
  for (const [name, mutate] of lostNegatives) test(`rejects ${name}`, () => {
    const r = reproduced(); mutate(r); expect(() => verifyReleaseReceipt(r, expected)).toThrow()
  })
  test('rejects a changed canonical definition and duplicate canonical names', () => {
    expect(() => verifyReleaseReceipt(fixture(), { ...expected, canonicalJobs: [{ ...canonicalJobs[0]!, cmd: 'changed' }, canonicalJobs[1]!] })).toThrow()
    expect(() => verifyReleaseReceipt(fixture(), { ...expected, canonicalJobs: [canonicalJobs[0]!, canonicalJobs[0]!] })).toThrow()
  })
})
