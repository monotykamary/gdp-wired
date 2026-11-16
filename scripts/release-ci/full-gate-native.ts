import {createHash} from 'node:crypto'
import {lstatSync, readFileSync, writeFileSync} from 'node:fs'
import {dirname, isAbsolute, join, relative, resolve, sep} from 'node:path'
import {canonicalJobHash, verifyReleaseReceipt, type ReleaseReceipt, type ReceiptSummary} from './full-gate-contract'
import {canonicalJobs} from './full-gate-runner'

const hash = (v: Buffer | string) => createHash('sha256').update(v).digest('hex')
const fail = (s: string): never => { throw Error(`native finalizer: ${s}`) }
const obj = (v: any, s: string): Record<string, any> => v && typeof v === 'object' && !Array.isArray(v) ? v : fail(`invalid ${s}`)
const text = (v: any, s: string): string => typeof v === 'string' && !!v.trim() && v === v.trim() ? v : fail(`invalid ${s}`)
const same = (a: any, b: any) => JSON.stringify(Object.entries(obj(a, 'pins')).sort(([a], [b]) => a.localeCompare(b))) === JSON.stringify(Object.entries(obj(b, 'pins')).sort(([a], [b]) => a.localeCompare(b)))
const safeRelative = (s: unknown): s is string => typeof s === 'string' && !!s && !isAbsolute(s) && !s.includes('\\') && !s.includes('\0') && s.split('/').every(x => x && x !== '.' && x !== '..')
// Reject symlinks in every component, including the supplied root itself.
function noLinks(path: string): string {
  const absolute = resolve(path), parts = absolute.split(sep).filter(Boolean)
  let current: string = sep
  for (const part of parts) { current = join(current, part); if (lstatSync(current).isSymbolicLink()) fail('symlink in evidence path') }
  return absolute
}
function contained(root: string, path: unknown, directory = false): string {
  const r = noLinks(root)
  if (typeof path !== 'string' || !path || path.includes('\0') || path.includes('\\')) fail('invalid evidence path')
  const target = resolve(r, path as string), rel = relative(r, target)
  if (!rel || rel === '..' || rel.startsWith('..' + sep) || isAbsolute(rel)) fail('evidence outside root')
  noLinks(target)
  const stat = lstatSync(target)
  if (directory ? !stat.isDirectory() : !stat.isFile()) fail('wrong evidence file type')
  return target
}
const readJson = (b: Buffer) => JSON.parse(b.toString('utf8'))

/** Synchronous. Native paths must be contained in the results.json directory. */
export function finalize(inputDir: string, resultsPath: string, pinPath: string, receiptPath: string): ReceiptSummary {
  const input = noLinks(inputDir), resultsFile = noLinks(resultsPath), pinFile = noLinks(pinPath)
  const root = dirname(resultsFile)
  const manifestBytes = readFileSync(contained(input, 'manifest.json')), manifest = obj(readJson(manifestBytes), 'manifest')
  const manifestHash = hash(manifestBytes), suiteBytes = readFileSync(contained(input, 'canonical-suite.json'))
  if (hash(suiteBytes) !== manifest.suiteSha256) fail('suite hash mismatch')
  const suite = canonicalJobs(readJson(suiteBytes)), definitions = obj(manifest.definitions, 'definitions')
  if (Object.keys(definitions).length !== suite.length) fail('definition coverage mismatch')
  for (const job of suite) if (definitions[job.name] !== canonicalJobHash(job)) fail('definition mismatch')
  if (!Array.isArray(manifest.repositories) || !manifest.repositories.length) fail('missing repositories')
  const vendorPins: Record<string, string> = Object.create(null), repoPaths = new Set<string>()
  for (const [i, raw] of manifest.repositories.entries()) {
    const r = obj(raw, 'repository')
    if ((i === 0 ? r.path !== '.' || r.commit !== manifest.commit || r.tree !== manifest.tree : !safeRelative(r.path)) || repoPaths.has(r.path) || !/^[a-f0-9]{40}$/.test(r.commit) || !/^[a-f0-9]{40}$/.test(r.tree) || !safeRelative(r.archive) || r.archive.includes('/') || !/^[a-f0-9]{64}$/.test(r.archiveSha256)) fail('invalid repository')
    if (hash(readFileSync(contained(input, r.archive))) !== r.archiveSha256) fail('archive mismatch')
    repoPaths.add(r.path)
    if (i) vendorPins[r.path] = r.commit
  }
  const results = obj(readJson(readFileSync(resultsFile)), 'results'), rows = obj(results.rows, 'rows'), cleanup = obj(results.cleanup, 'cleanup')
  if (Object.keys(rows).length !== suite.length || cleanup.cleanup_complete !== true) fail('incomplete results')
  const validation = obj(cleanup.cleanup_validation, 'cleanup validation'), batches = obj(cleanup.batches, 'cleanup batches')
  if (!Object.keys(validation).length || Object.values(validation).some(v => v !== true)) fail('cleanup validation failed')
  const image = text(cleanup.image, 'cleanup image'), pinBytes = readFileSync(pinFile), pinReceipt = obj(readJson(pinBytes), 'pin receipt'), pin = obj(pinReceipt.pin, 'pin')
  const reference = text(pin.ref, 'pin reference')
  if (pinReceipt.ok !== true || pin.protected !== true || !Array.isArray(pin.images) || !pin.images.includes(image) || typeof pin.protected_until !== 'number' || !Number.isFinite(pin.protected_until) || pin.protected_until <= Date.now() / 1000) fail('invalid image pin')
  const launches = new Set<string>(), usedBatches = new Set<string>(), matchedAttempts = new Set<unknown>()
  const jobs: ReleaseReceipt['jobs'] = []
  for (const job of suite) {
    const row = obj(rows[job.name], `row ${job.name}`)
    if (row.name !== job.name || row.run_name !== job.name || row.status !== 'SUCCEEDED' || row.code !== 0 || row.terminal !== true || row.strict_once !== true || row.max_attempts !== 1 || row.attempts !== 1 || row.attempt !== 1 || ('image' in row && row.image !== image) || ('runtime_verification' in row && (row.runtime_verified !== true || obj(row.runtime_verification, 'runtime verification').ok !== true)) || ('runtime_verified' in row && row.runtime_verified !== true)) fail(`invalid row ${job.name}`)
    if (job.runtime !== undefined) {
      const verification = obj(row.runtime_verification, 'required runtime verification')
      if (row.runtime_verified !== true || verification.ok !== true || canonicalJobHash({name: job.name, cmd: job.cmd, runtime: verification.required}) !== canonicalJobHash({name: job.name, cmd: job.cmd, runtime: job.runtime})) fail('required runtime binding mismatch')
    }
    const batch = text(row.batch, 'batch'), vm = text(row.vm, 'vm'), boot = text(row.boot_id, 'boot'), launch = text(row.launch_identity, 'launch identity')
    if (launches.has(launch)) fail('duplicate launch identity')
    launches.add(launch)
    const b = obj(batches[batch], 'batch cleanup')
    if (validation[batch] !== true || ['ok','complete','cleanup_complete','admission_closed','journals_retained','strict_once'].some(k => b[k] !== true) || b.max_attempts !== 1 || !Array.isArray(b.attempts)) fail('invalid batch cleanup')
    const matches = b.attempts.filter((a: any) => a && a.name === job.name && a.run_name === row.run_name && a.vm === vm && a.boot_id === boot && a.attempt === 1 && a.launch_identity === launch)
    if (matches.length !== 1 || matches[0].cleanup_complete !== true) fail('cleanup identity mismatch')
    usedBatches.add(batch); matchedAttempts.add(matches[0])
    const ref = obj(row.output_files_ref, 'output ref')
    if (ref.version !== 1 || ref.format !== 'json' || !Number.isSafeInteger(ref.bytes) || ref.bytes < 0 || !/^[a-f0-9]{64}$/.test(ref.sha256)) fail('invalid output ref')
    const payload = readFileSync(contained(root, row.output_files_manifest))
    if (payload.length !== ref.bytes || hash(payload) !== ref.sha256) fail('output manifest mismatch')
    const entries = readJson(payload)
    if (!Array.isArray(entries)) fail('invalid output manifest')
    const dir = contained(root, row.output_files_dir, true), artifacts = new Map<string, Buffer>()
    for (const raw of entries) {
      const e = obj(raw, 'artifact')
      if (!safeRelative(e.path) || artifacts.has(e.path) || e.version !== 1 || e.format !== 'file' || !Number.isSafeInteger(e.bytes) || e.bytes < 0 || !/^[a-f0-9]{64}$/.test(e.sha256)) fail('invalid artifact entry')
      const bytes = readFileSync(contained(dir, e.path))
      if (bytes.length !== e.bytes || hash(bytes) !== e.sha256) fail('artifact mismatch')
      artifacts.set(e.path, bytes)
    }
    const artifact = (name: string): Buffer => artifacts.get(name) ?? fail(`missing ${name}`)
    const provision = obj(readJson(artifact('PROVISIONED.json')), 'provisioning'), command = obj(readJson(artifact('COMMAND-RESULT.json')), 'command result')
    if (provision.commit !== manifest.commit || provision.tree !== manifest.tree || provision.suiteSha256 !== manifest.suiteSha256 || provision.provisioningSha256 !== manifestHash || provision.definitionSha256 !== definitions[job.name] || !same(provision.vendorPins, vendorPins)) fail('provisioning mismatch')
    if (command.name !== job.name || command.command !== job.cmd || command.cwd !== (job.cwd ?? '.') || command.code !== 0 || command.signal !== null || command.error !== null) fail('command result mismatch')
    jobs.push({name: job.name, nativeName: row.name, batchId: batch, definitionSha256: definitions[job.name], commit: manifest.commit, tree: manifest.tree, provisioningSha256: manifestHash, submodules: vendorPins, imageId: image, attempts: 1, launchIdentity: launch, status: 'SUCCEEDED', code: 0, cleanupComplete: true, outputHashes: {stdoutSha256: hash(artifact('stdout.log')), stderrSha256: hash(artifact('stderr.log')), nativeReceiptSha256: hash(JSON.stringify(row))}})
  }
  if (Object.keys(batches).length !== usedBatches.size || Object.keys(validation).length !== usedBatches.size) fail('unexpected cleanup batch')
  for (const [id, raw] of Object.entries(batches)) {
    const batch = obj(raw, 'closed batch')
    if (!usedBatches.has(id) || batch.batch !== id || !Array.isArray(batch.pending) || batch.pending.length || !Array.isArray(batch.unlaunched) || batch.unlaunched.length || !Array.isArray(batch.attempts) || batch.attempts.some((attempt: unknown) => !matchedAttempts.has(attempt))) fail('unexpected or pending cleanup attempt')
  }
  const receipt: ReleaseReceipt = {schema: 'gdp-release-full-gate/v1', commit: manifest.commit, tree: manifest.tree, suiteSha256: manifest.suiteSha256, provisioningSha256: manifestHash, submodules: vendorPins, imagePins: [{imageId: image, pinReceiptSha256: hash(pinBytes), protected: true, reference}], jobs}
  const summary = verifyReleaseReceipt(receipt, {commit: manifest.commit, tree: manifest.tree, suiteSha256: manifest.suiteSha256, canonicalJobs: suite, vendorPins})
  writeFileSync(receiptPath, JSON.stringify(receipt, null, 2) + '\n', {flag: 'wx'})
  return summary
}
