// Pack the complete pinned Git source, run every canonical job on Boat once,
// and emit a receipt only after authenticating native results and custody.

type Json = null | boolean | number | string | Json[] | {[key: string]: Json}
export type CanonicalJob = {[key: string]: Json} & {name: string, cmd: string}
export type JobHash = (job: CanonicalJob) => string

const SHA256 = /^[0-9a-f]{64}$/
const NAME = /^[A-Za-z0-9][A-Za-z0-9._-]*$/

/** Validate the complete suite without selecting a subset or modifying definitions. */
export function canonicalJobs(value: unknown): CanonicalJob[] {
  if (!Array.isArray(value) || value.length === 0) throw Error('canonical suite must be a nonempty array')
  const names = new Set<string>()
  return value.map((entry, index) => {
    if (!entry || typeof entry !== 'object' || Array.isArray(entry)) throw Error(`invalid job at ${index}`)
    const job = entry as CanonicalJob
    if (typeof job.name !== 'string' || !NAME.test(job.name) || job.name === '.' || job.name === '..') throw Error(`unsafe job name at ${index}`)
    if (names.has(job.name)) throw Error(`duplicate job: ${job.name}`)
    names.add(job.name)
    if (typeof job.cmd !== 'string' || !job.cmd.trim() || job.cmd.includes('\0')) throw Error(`invalid command: ${job.name}`)
    if (job.cwd !== undefined && (typeof job.cwd !== 'string' || !job.cwd || job.cwd.startsWith('/') || job.cwd.split('/').some(part => part === '..') || job.cwd.includes('\0'))) throw Error(`unsafe cwd: ${job.name}`)
    if (job.backend !== undefined && job.backend !== 'boat') throw Error(`non-boat job: ${job.name}`)
    if (job.gpu !== undefined && job.gpu !== null && job.gpu !== false) throw Error(`GPU job cannot use strict boat gate: ${job.name}`)
    if (job.timeout !== undefined && (typeof job.timeout !== 'number' || !Number.isFinite(job.timeout) || job.timeout <= 0)) throw Error(`invalid timeout: ${job.name}`)
    return job
  })
}

export type Definition = {name: string, definitionSha256: string}
/** Bind every canonical definition to its actual contract hash. */
export function canonicalDefinitions(suite: unknown, hash: JobHash): Definition[] {
  return canonicalJobs(suite).map(job => {
    const definitionSha256 = hash(job)
    if (!SHA256.test(definitionSha256)) throw Error(`invalid definition hash: ${job.name}`)
    return {name: job.name, definitionSha256}
  })
}

/** Exact set equality, not a count-only or subset test. Does not verify custody. */
export function assertExactCoverage(expected: Definition[], observed: Definition[]): void {
  const wanted = new Map<string, string>()
  for (const row of expected) {
    if (!NAME.test(row.name) || !SHA256.test(row.definitionSha256) || wanted.has(row.name)) throw Error('invalid or duplicate expected definition')
    wanted.set(row.name, row.definitionSha256)
  }
  if (!wanted.size) throw Error('empty expected coverage')
  const seen = new Set<string>()
  for (const row of observed) {
    if (seen.has(row.name)) throw Error(`duplicate observed job: ${row.name}`)
    seen.add(row.name)
    if (!wanted.has(row.name)) throw Error(`unexpected observed job: ${row.name}`)
    if (wanted.get(row.name) !== row.definitionSha256) throw Error(`definition mismatch: ${row.name}`)
  }
  const missing = [...wanted.keys()].filter(name => !seen.has(name))
  if (missing.length) throw Error(`missing observed jobs: ${missing.join(', ')}`)
}

// A prepared input is only a plan; it is never release evidence.
import {execFileSync, spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {existsSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync} from 'node:fs'
import {basename, dirname, isAbsolute, join, resolve, sep} from 'node:path'
import {pathToFileURL} from 'node:url'

const sha256 = (data: Buffer) => createHash('sha256').update(data).digest('hex')
const within = (path: string, parent: string) => path === parent || path.startsWith(parent + sep)

/** Build opaque per-repository archives directly from Git objects. */
export async function prepare(rootArg: string, inputArg: string): Promise<void> {
  const root = realpathSync(rootArg)
  const input = resolve(inputArg)
  const inputParent = realpathSync(dirname(input))
  if (within(inputParent, root) || within(root, input)) throw Error('input must be outside the source checkout')
  const env: NodeJS.ProcessEnv = {...process.env, GIT_TERMINAL_PROMPT: '0', GIT_CONFIG_NOSYSTEM: '1', GIT_CONFIG_GLOBAL: '/dev/null'}
  for (const key of Object.keys(env)) if (/^GIT_(DIR|WORK_TREE|INDEX_FILE|OBJECT_DIRECTORY|ALTERNATE_OBJECT_DIRECTORIES|COMMON_DIR|CONFIG_COUNT)$/.test(key)) delete env[key]
  const git = (cwd: string, args: string[], stdin?: Buffer): Buffer => execFileSync('git', ['-c', 'core.hooksPath=/dev/null', '-c', 'core.autocrlf=false', ...args], {cwd, env, input: stdin, maxBuffer: 512 * 1024 * 1024})
  const text = (cwd: string, ...args: string[]) => git(cwd, args).toString('utf8').trim()
  if (realpathSync(text(root, 'rev-parse', '--show-toplevel')) !== root) throw Error('root is not the checkout root')
  if (text(root, 'status', '--porcelain=v1', '--untracked-files=all', '--ignore-submodules=none')) throw Error('dirty source')
  const commit = text(root, 'rev-parse', 'HEAD^{commit}'), tree = text(root, 'rev-parse', 'HEAD^{tree}')
  if (!/^[0-9a-f]{40}$/.test(commit) || !/^[0-9a-f]{40}$/.test(tree)) throw Error('only SHA-1 Git repositories are supported')
  git(root, ['submodule', 'update', '--init', '--recursive', '--jobs', '1'])
  if (text(root, 'status', '--porcelain=v1', '--untracked-files=all', '--ignore-submodules=none')) throw Error('dirty source after submodule initialization')
  const suiteBytes = readFileSync(join(root, 'supercomputer/suite.json'))
  const suite = canonicalJobs(JSON.parse(suiteBytes.toString('utf8')))
  const policyBytes = git(root, ['show', `${commit}:scripts/release-ci/known-failures.json`])
  const {validateKnownFailuresPolicy} = await import('./known-failures')
  const policy = JSON.parse(policyBytes.toString('utf8'))
  validateKnownFailuresPolicy(policy, suite)
  if (!policy.requiredPass.includes('exists')) throw Error('exists must be required to pass')
  const contract = await import(pathToFileURL(join(root, 'scripts/release-ci/full-gate-contract.ts')).href)
  const definitions = Object.fromEntries(canonicalDefinitions(suite, contract.canonicalJobHash).map(d => [d.name, d.definitionSha256]))
  // mkdir without recursive refuses an existing path, preserving prior evidence.
  mkdirSync(input)
  const repositories: Array<{path: string, commit: string, tree: string, archive: string, archiveSha256: string}> = []
  const visit = (path: string, expected: string) => {
    const cwd = path === '.' ? root : join(root, path)
    if (!within(realpathSync(cwd), root)) throw Error('submodule escapes checkout')
    const actual = text(cwd, 'rev-parse', 'HEAD^{commit}')
    if (actual !== expected || text(cwd, 'status', '--porcelain=v1', '--untracked-files=all', '--ignore-submodules=none')) throw Error(`dirty or mismatched repository: ${path}`)
    const repoTree = text(cwd, 'rev-parse', 'HEAD^{tree}')
    const rows = git(cwd, ['ls-tree', '-r', '-t', '-z', '--full-tree', actual]).toString('utf8').split('\0').filter(Boolean)
    const objects = new Set([actual, repoTree]); const links: Array<[string, string]> = []
    for (const row of rows) {
      const match = /^(\d{6}) (blob|tree|commit) ([0-9a-f]{40})\t(.+)$/.exec(row)
      if (!match) throw Error('unsupported Git tree entry')
      if (match[1] === '160000') {
        const child = path === '.' ? match[4]! : `${path}/${match[4]!}`
        if (isAbsolute(child) || child.includes('\\') || child.split('/').some(part => !part || part === '.' || part === '..' || part === '.git')) throw Error('unsafe gitlink path')
        links.push([child, match[3]!])
      } else objects.add(match[3]!)
    }
    const archive = `repo-${repositories.length}.tar`
    const pack = git(cwd, ['pack-objects', '--stdout'], Buffer.from([...objects].join('\n') + '\n'))
    const staging = join(input, `.pack-${repositories.length}`)
    mkdirSync(staging)
    try {
      writeFileSync(join(staging, 'objects.pack'), pack, {flag: 'wx'})
      execFileSync('tar', ['--format=ustar', '--owner=0', '--group=0', '--numeric-owner', '--mtime=@0', '-cf', join(input, archive), '-C', staging, 'objects.pack'], {env})
    } finally { rmSync(staging, {recursive: true, force: true}) }
    repositories.push({path, commit: actual, tree: repoTree, archive, archiveSha256: sha256(readFileSync(join(input, archive)))})
    for (const [child, pin] of links) visit(child, pin)
  }
  visit('.', commit)
  if (text(root, 'rev-parse', 'HEAD^{commit}') !== commit || text(root, 'status', '--porcelain=v1', '--untracked-files=all', '--ignore-submodules=none')) throw Error('source changed while packing')
  const manifest = {commit, tree, suiteSha256: sha256(suiteBytes), knownFailuresSha256: sha256(policyBytes), repositories, definitions}
  const manifestBytes = Buffer.from(JSON.stringify(manifest) + '\n')
  writeFileSync(join(input, 'manifest.json'), manifestBytes, {flag: 'wx'})
  writeFileSync(join(input, 'canonical-suite.json'), suiteBytes, {flag: 'wx'})
  writeFileSync(join(input, 'known-failures.json'), policyBytes, {flag: 'wx'})
  const manifestHash = sha256(manifestBytes)
  const jobs = suite.map(job => {
    const required = job.required_agent_capabilities
    if (required !== undefined && (!required || typeof required !== 'object' || Array.isArray(required))) throw Error(`invalid capabilities: ${job.name}`)
    const caps = {...(required as {[key: string]: Json} | undefined)}
    for (const name of ['output_files_protocol', 'result_files_protocol']) {
      if (caps[name] !== undefined && caps[name] !== 1) throw Error(`incompatible capability: ${job.name}`)
      caps[name] = 1
    }
    const native: CanonicalJob = {...job, cmd: `bun scripts/release-ci/full-gate-worker.ts full-gate-input ${manifestHash} ${job.name}`, required_agent_capabilities: caps}
    delete native.cwd
    // Worker enforces the original timeout; allow separate provisioning time.
    if (typeof job.timeout === 'number') native.timeout = job.timeout + 600
    return native
  })
  writeFileSync(join(input, 'jobs.json'), JSON.stringify(jobs, null, 2) + '\n', {flag: 'wx'})
}

/** One explicit native admission. This never retries or substitutes failed jobs. */
export async function run(root: string, inputArg: string, outputArg: string, schedulerClass = 'gate'): Promise<void> {
  if (!/^[a-z][a-z0-9-]*$/.test(schedulerClass)) throw Error('invalid scheduler class')
  const input = resolve(inputArg), output = resolve(outputArg)
  if (existsSync(output) || within(input, output) || within(output, input)) throw Error('fresh, separate output directory required')
  await prepare(root, input)
  const cli = process.env.SUPERCOMPUTER_BIN ?? 'supercomputer'
  const environment = {...process.env, SUPERCOMPUTER_NO_BUILD: '1'}
  const invocation = [
    'run', '--jobs', join(input, 'jobs.json'), '--out', output,
    '--backend', 'boat', '--class', schedulerClass, '--strict-once', '--max-attempts', '1',
    '--data', `${input}:full-gate-input`,
  ]
  writeFileSync(join(input, 'invocation.json'), JSON.stringify({commit: JSON.parse(readFileSync(join(input, 'manifest.json'), 'utf8')).commit, arguments: invocation}, null, 2) + '\n', {flag: 'wx'})
  const native = spawnSync(cli, invocation, {cwd: root, env: environment, stdio: 'inherit', timeout: 21_600_000, killSignal: 'SIGTERM'})
  const resultsPath = join(output, 'results.json')
  // Protect the exact executed image even when a completed run failed. An absent
  // native result is unresolved custody, not permission to resubmit the batch.
  if (!existsSync(resultsPath)) throw Error('native results missing; inspect custody, do not retry')
  const results = JSON.parse(readFileSync(resultsPath, 'utf8')) as {cleanup?: {image?: unknown}}
  const image = results.cleanup?.image
  if (typeof image !== 'string' || !/^sc-[a-zA-Z0-9._~-]+$/.test(image)) throw Error('native image identity missing')
  const manifest = JSON.parse(readFileSync(join(input, 'manifest.json'), 'utf8')) as {commit: string}
  const pin = execFileSync(cli, ['image', 'pin', image, '--kind', 'packet', '--reference', `full-gate-${manifest.commit}-${basename(output)}`], {cwd: root, env: environment, timeout: 120_000, maxBuffer: 1024 * 1024})
  const pinPath = join(output, 'image-pin.json')
  writeFileSync(pinPath, pin, {flag: 'wx'})
  if (native.error || native.signal || ![0, 3].includes(native.status ?? -1)) throw Error('native run did not pass; receipts retained, no retry or release receipt emitted')
  const {finalize} = await import('./full-gate-native.ts')
  const receiptPath = join(output, 'receipt.json')
  const summary = finalize(input, resultsPath, pinPath, receiptPath)
  if (!summary.cleanupComplete || summary.openCustody.length) throw Error('fresh canonical run has unresolved custody')
  writeStatusPayload(receiptPath, join(output, 'status-payload.json'))
  console.log(JSON.stringify({gate: summary.knownFailures.length ? 'ACCEPTED_WITH_KNOWN_FAILURES' : 'ACCEPTED', commit: manifest.commit, counts: summary.counts, knownFailures: summary.knownFailures, openCustody: summary.openCustody}))
  console.log('Main must review, commit the receipt and post the status.')
}

export function writeStatusPayload(receiptPath: string, outputPath: string): void {
  const digest = sha256(readFileSync(receiptPath))
  writeFileSync(outputPath, JSON.stringify({state: 'success', context: 'release-full-gate', description: `receipt-sha256:${digest}`}, null, 2) + '\n', {flag: 'wx'})
}

async function main(): Promise<void> {
  const args = process.argv.slice(2)
  const [command, input, output, pin, receipt] = args
  if (command === 'prepare' && args.length === 2 && input) return prepare(process.cwd(), input)
  if (command === 'run' && (args.length === 3 || args.length === 4) && input && output) return run(process.cwd(), input, output, pin ?? 'gate')
  if (command === 'finalize' && args.length === 5 && input && output && pin && receipt) {
    const {finalize} = await import('./full-gate-native.ts')
    const summary = finalize(input, output, pin, receipt)
    console.log(JSON.stringify({gate: summary.knownFailures.length ? 'ACCEPTED_WITH_KNOWN_FAILURES' : 'ACCEPTED', cleanupComplete: summary.cleanupComplete, openCustody: summary.openCustody, counts: summary.counts, knownFailures: summary.knownFailures}))
    return
  }
  throw Error('usage: release:full-gate prepare INPUT | run INPUT OUTPUT [CLASS] | finalize INPUT RESULTS_JSON PIN_JSON RECEIPT_JSON')
}
if (import.meta.main) main().catch(error => { console.error(error); process.exitCode = 1 })
