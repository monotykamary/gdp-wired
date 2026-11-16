import { createHash } from 'node:crypto'
import {matchKnownFailure, validateKnownFailuresPolicy, type FailureSignature, type KnownFailuresPolicy} from './known-failures'

// These checks validate a receipt's internal consistency, not the authenticity of
// its claims. The caller must obtain and verify source, native evidence, output
// bytes, image-retention receipts and provisioning from trusted custody.
export type CanonicalJob = { name: string; cmd: string; [key: string]: unknown }
export type OutputHashes = { stdoutSha256: string; stderrSha256: string; nativeReceiptSha256: string }
export type LostOutputHashes = { stdoutSha256: string | null; stderrSha256: string | null; nativeReceiptSha256: string }
export type ExecutionIdentity = {
  name: string; nativeName: string; batchId: string; definitionSha256: string; commit: string; tree: string
  provisioningSha256: string; submodules: Record<string, string>; imageId: string
  attempts: 1; launchIdentity: string
}
export type LostExecution = ExecutionIdentity & { status: 'LOST'; code: -1; cleanupComplete: boolean; outputHashes: LostOutputHashes }
export type SuccessfulExecution = ExecutionIdentity & {
  status: 'SUCCEEDED'; code: 0; cleanupComplete: true; outputHashes: OutputHashes
  reproductionLabel?: string; provenance?: 'independent-reproduction'; originalLost?: LostExecution
}
export type KnownFailureExecution = ExecutionIdentity & {
  status: 'FAILED'; code: 1; outcome: 'KNOWN_FAILURE'; signature: FailureSignature; cleanupComplete: true; outputHashes: OutputHashes
}
export type ReleaseReceipt = {
  schema: 'gdp-release-full-gate/v1'; commit: string; tree: string; suiteSha256: string
  provisioningSha256: string; submodules: Record<string, string>
  imagePins: { imageId: string; pinReceiptSha256: string; protected: true; reference: string }[]; jobs: (SuccessfulExecution | KnownFailureExecution)[]
  knownFailuresSha256?: string
}
export type ReleaseExpected = {
  commit: string; tree: string; suiteSha256: string
  canonicalJobs: readonly CanonicalJob[]; vendorPins: Record<string, string>
  trustedKnownFailuresPolicy?: KnownFailuresPolicy; knownFailuresSha256?: string
}

const fail = (message: string): never => { throw new Error(`full-gate: ${message}`) }
const object = (v: unknown, label: string): Record<string, unknown> => {
  if (v === null || typeof v !== 'object' || Array.isArray(v) || ![Object.prototype, null].includes(Object.getPrototypeOf(v))) return fail(`${label} must be an object`)
  return v as Record<string, unknown>
}
const text = (v: unknown, label: string): string => {
  if (typeof v !== 'string' || !v.trim() || v !== v.trim()) return fail(`${label} must be a nonempty trimmed string`)
  return v
}
const hex = (v: unknown, length: number, label: string): string => {
  if (typeof v !== 'string' || !(length === 40 ? /^[0-9a-f]{40}$/ : /^[0-9a-f]{64}$/).test(v)) return fail(`${label} must be lowercase ${length}-hex`)
  return v
}

// Stable JSON: recursively sorted object keys, original array order, no lossy
// JSON coercions. Hashes the entire definition, not just its command/name.
function stableJson(v: unknown, ancestors = new Set<object>()): string {
  if (v === null || typeof v === 'string' || typeof v === 'boolean') return JSON.stringify(v)
  if (typeof v === 'number' && Number.isFinite(v)) return JSON.stringify(v)
  if (typeof v !== 'object' || v === null || ancestors.has(v)) return fail('canonical job is not JSON data')
  ancestors.add(v)
  let result: string
  if (Array.isArray(v)) {
    if (Object.keys(v).length !== v.length) return fail('canonical job contains a sparse or decorated array')
    result = '[' + v.map(x => stableJson(x, ancestors)).join(',') + ']'
  } else {
    const o = object(v, 'canonical job value')
    if (Object.getOwnPropertySymbols(o).length) return fail('canonical job has symbol keys')
    result = '{' + Object.keys(o).sort().map(k => JSON.stringify(k) + ':' + stableJson(o[k], ancestors)).join(',') + '}'
  }
  ancestors.delete(v)
  return result
}
export function canonicalJobHash(job: CanonicalJob): string {
  object(job, 'canonical job')
  text(job.name, 'canonical job name'); text(job.cmd, 'canonical job cmd')
  return createHash('sha256').update(stableJson(job), 'utf8').digest('hex')
}
function pins(v: unknown, label: string): Record<string, string> {
  const o = object(v, label)
  for (const [path, sha] of Object.entries(o)) {
    text(path, `${label} path`)
    if (path.startsWith('/') || path.split('/').some(p => !p || p === '.' || p === '..') || path.includes('\\')) fail(`${label} invalid path`)
    hex(sha, 40, `${label}[${path}]`)
  }
  return o as Record<string, string>
}
function samePins(a: unknown, b: unknown, label: string): void {
  if (stableJson(pins(a, label)) !== stableJson(pins(b, 'expected vendor pins'))) fail(`${label} mismatch`)
}
function outputHashes(v: unknown, lost: boolean): void {
  const o = object(v, 'outputHashes')
  for (const key of ['stdoutSha256', 'stderrSha256', 'nativeReceiptSha256']) {
    if (lost && key !== 'nativeReceiptSha256' && o[key] === null) continue
    hex(o[key], 64, `outputHashes.${key}`)
  }
}
function execution(v: unknown, allowOpenLost = false): Record<string, unknown> {
  const e = object(v, 'execution')
  text(e.name, 'execution name'); text(e.nativeName, 'nativeName'); text(e.batchId, 'batchId'); hex(e.definitionSha256, 64, 'definitionSha256')
  hex(e.commit, 40, 'execution commit'); hex(e.tree, 40, 'execution tree')
  hex(e.provisioningSha256, 64, 'execution provisioningSha256')
  pins(e.submodules, 'execution submodules'); text(e.imageId, 'execution imageId')
  text(e.launchIdentity, 'launchIdentity')
  if (e.attempts !== 1 || (e.cleanupComplete !== true && !(allowOpenLost && e.status === 'LOST' && e.cleanupComplete === false))) fail('execution requires one attempt and explicit safe custody status')
  outputHashes(e.outputHashes, e.status === 'LOST')
  return e
}

/** Validate an original terminal loss and a separately labelled successful run. */
export function verifyLostReproduction(original: unknown, reproduction: unknown): void {
  const lost = execution(original, true), success = execution(reproduction)
  if (lost.status !== 'LOST' || lost.code !== -1 || lost.nativeName !== lost.name) fail('original must remain terminal LOST with native code -1 and canonical native name')
  const prefix = `${text(lost.name, 'lost name')}-repro-`
  const label = text(success.reproductionLabel, 'reproductionLabel')
  if (!label.startsWith(prefix) || !/^[1-9][0-9]*$/.test(label.slice(prefix.length)) || success.nativeName !== label || success.provenance !== 'independent-reproduction' || success.status !== 'SUCCEEDED' || success.code !== 0) fail('reproduction must have a matching native label, independent provenance and success')
  for (const key of ['name', 'definitionSha256', 'commit', 'tree', 'provisioningSha256']) {
    if (lost[key] !== success[key]) fail(`reproduction ${key} mismatch`)
  }
  samePins(lost.submodules, success.submodules, 'reproduction submodules')
  if (lost.launchIdentity === success.launchIdentity || lost.batchId === success.batchId) fail('reproduction batch and launch must be independent')
  if ('originalLost' in lost || 'reproductionLabel' in lost || 'provenance' in lost) fail('original LOST must not contain reproduction history')
}

export type ReceiptSummary = {
  receipt: ReleaseReceipt; cleanupComplete: boolean
  openCustody: { name: string; batchId: string; launchIdentity: string; statement: string }[]
  knownFailures: KnownFailureExecution[]; counts: { succeeded: number; knownFailures: number; total: number }
}
export function verifyReleaseReceipt(receipt: unknown, expected: ReleaseExpected): ReceiptSummary {
  const x = object(expected, 'expected')
  const commit = hex(x.commit, 40, 'expected commit'), tree = hex(x.tree, 40, 'expected tree')
  const suite = hex(x.suiteSha256, 64, 'expected suiteSha256')
  pins(x.vendorPins, 'expected vendor pins')
  if (!Array.isArray(x.canonicalJobs) || !x.canonicalJobs.length) fail('expected canonical jobs must be nonempty')
  const definitions = new Map<string, string>()
  for (const value of x.canonicalJobs as CanonicalJob[]) {
    const hash = canonicalJobHash(value)
    if (definitions.has(value.name)) fail(`duplicate canonical job ${value.name}`)
    definitions.set(value.name, hash)
  }
  if ((expected.trustedKnownFailuresPolicy === undefined) !== (expected.knownFailuresSha256 === undefined)) fail('trusted policy and hash must be supplied together')
  if (expected.trustedKnownFailuresPolicy) {
    hex(expected.knownFailuresSha256, 64, 'expected knownFailuresSha256')
    validateKnownFailuresPolicy(expected.trustedKnownFailuresPolicy, expected.canonicalJobs)
    if (!expected.trustedKnownFailuresPolicy.requiredPass.includes('exists')) fail('exists must be required to pass')
  }
  const r = object(receipt, 'receipt')
  if (expected.trustedKnownFailuresPolicy ? r.knownFailuresSha256 !== expected.knownFailuresSha256 : 'knownFailuresSha256' in r) fail('known failures policy hash mismatch')
  if (r.schema !== 'gdp-release-full-gate/v1' || r.commit !== commit || r.tree !== tree || r.suiteSha256 !== suite) fail('receipt schema or source mismatch')
  hex(r.provisioningSha256, 64, 'receipt provisioningSha256')
  samePins(r.submodules, x.vendorPins, 'receipt submodules')
  if (!Array.isArray(r.imagePins) || !r.imagePins.length) fail('protected image pins required')
  const images = new Set<string>()
  for (const p of r.imagePins as unknown[]) {
    const pin = object(p, 'image pin'), id = text(pin.imageId, 'imageId')
    hex(pin.pinReceiptSha256, 64, 'pinReceiptSha256')
    text(pin.reference, 'image pin reference')
    if (pin.protected !== true) fail('image pin must be protected')
    if (images.has(id)) fail('duplicate image pin')
    images.add(id)
  }
  if (!Array.isArray(r.jobs) || r.jobs.length !== definitions.size) fail('job count mismatch')
  const seen = new Set<string>(), launches = new Set<string>()
  const openCustody: ReceiptSummary['openCustody'] = []
  const knownFailures: KnownFailureExecution[] = []
  for (const value of r.jobs as unknown[]) {
    const e = execution(value), name = e.name as string
    if (seen.has(name) || !definitions.has(name) || definitions.get(name) !== e.definitionSha256) fail(`duplicate, unexpected or changed job ${name}`)
    seen.add(name)
    if (e.commit !== commit || e.tree !== tree || e.provisioningSha256 !== r.provisioningSha256) fail(`job source or provisioning mismatch ${name}`)
    samePins(e.submodules, x.vendorPins, 'job submodules')
    if (!images.has(e.imageId as string)) fail(`unprotected job image ${name}`)
    if (e.status === 'FAILED' && e.code === 1 && e.outcome === 'KNOWN_FAILURE' && expected.trustedKnownFailuresPolicy) {
      if (name === 'exists' || expected.trustedKnownFailuresPolicy.requiredPass.includes(name)) fail(`required job did not succeed ${name}`)
      matchKnownFailure(expected.trustedKnownFailuresPolicy, name, e.definitionSha256 as string, 1, e.signature as FailureSignature)
      knownFailures.push(value as KnownFailureExecution)
    } else if (e.status !== 'SUCCEEDED' || e.code !== 0 || 'outcome' in e || 'signature' in e) fail(`job did not succeed ${name}`)
    if ('originalLost' in e) {
      verifyLostReproduction(e.originalLost, e)
      const lost = execution(e.originalLost, true)
      if (lost.cleanupComplete === false) openCustody.push({ name, batchId: lost.batchId as string, launchIdentity: lost.launchIdentity as string, statement: `LOST, custody open, superseded by passing labelled repro of same job/commit` })
      if (!images.has(lost.imageId as string)) fail(`unprotected LOST image ${name}`)
      if (launches.has(lost.launchIdentity as string)) fail('duplicate launch identity')
      launches.add(lost.launchIdentity as string)
    } else if ('reproductionLabel' in e || 'provenance' in e || e.nativeName !== name) fail('ordinary execution requires canonical native name and no reproduction fields')
    if (launches.has(e.launchIdentity as string)) fail('duplicate launch identity')
    launches.add(e.launchIdentity as string)
  }
  return { receipt: receipt as ReleaseReceipt, cleanupComplete: openCustody.length === 0, openCustody, knownFailures, counts: {succeeded: definitions.size - knownFailures.length, knownFailures: knownFailures.length, total: definitions.size} }
}
