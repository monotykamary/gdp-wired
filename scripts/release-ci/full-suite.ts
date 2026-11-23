// The release's full gate (publish.yml, FULL-GATE.md): every job of supercomputer/suite.json run once, at the exact
// commit being published, as one supercomputer batch on instabox (strict-once: one attempt, no retry), and a release
// only when each job answered 0 or failed exactly as known-failures.json records (the same job definition, exit
// code and failure signature).
//
//   bun scripts/release-ci/full-suite.ts source               the checkout is the run's commit, every submodule at its
//                                                             gitlink, nothing changed (refused otherwise)
//   bun scripts/release-ci/full-suite.ts jobs FILE            the batch's jobs file: each suite job, run through `box`
//   bun scripts/release-ci/full-suite.ts tree SUPERCOMPUTER   the hash supercomputer gives this checkout's tree
//   bun scripts/release-ci/full-suite.ts box NAME             (on its box) one suite job: the pinned dependencies, then
//                                                             its command, its complete Lean diagnostics and RESULT.json
//                                                             in $SUPERCOMPUTER_OUTPUT_DIR/.gate
//   bun scripts/release-ci/full-suite.ts verdict OUT SUPERCOMPUTER TREE
//                                                             the batch in OUT (batch.json's log replayed through
//                                                             supercomputer's batch rule) and every job's result: the verdict
//
// On its box a job runs as supercomputer runs it (`[run] pre`, its image's PATH and env, its env), inside `box`, which
// first installs the pinned dependencies at the tree's root (bun install --frozen-lockfile), as the release gate
// always has, then runs the job's command in its cwd under its timeout and records the selected `lean`'s complete
// output. SUPERCOMPUTER is the installed supercomputer (the folder holding its src/).

import {spawnSync} from 'node:child_process'
import {closeSync, existsSync, lstatSync, mkdirSync, mkdtempSync, openSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {delimiter, isAbsolute, join, resolve} from 'node:path'
import {pathToFileURL} from 'node:url'
import {canonicalJobHash, type CanonicalJob} from './job-hash'
import {extractFailureSignature, matchKnownFailure, validateKnownFailuresPolicy, type FailureSignature} from './known-failures'

const ROOT = resolve(import.meta.dir, '../..')
const fail = (message: string): never => { throw new Error(`full-suite: ${message}`) }
// (a job's batch timeout: its own, plus the dependency install before it)
const INSTALL_SECONDS = 600

type Job = CanonicalJob & {cwd?: string; timeout?: number; env?: Record<string, string>; image?: string; cpu?: number; memory?: number}
export type Result = {
  schema: 'gdp-full-suite-result/v1'; name: string; definitionSha256: string; batch: string
  code: number; signal: string | null; seconds: number; installed: boolean
  signature?: FailureSignature; signatureError?: string
}

export function suite(root = ROOT): Job[] {
  const jobs = JSON.parse(readFileSync(join(root, 'supercomputer/suite.json'), 'utf8')) as Job[]
  if (!Array.isArray(jobs) || !jobs.length) fail('supercomputer/suite.json is not a list of jobs')
  const names = new Set<string>()
  for (const j of jobs) {
    if (typeof j.name !== 'string' || !/^[A-Za-z0-9][A-Za-z0-9._-]*$/.test(j.name) || names.has(j.name)) fail(`a job name missing, unsafe or repeated: ${j.name}`)
    names.add(j.name)
  }
  return jobs
}

// The batch's job for a suite job: the same resources, image and env, its command run through `box`.
export const boxCommand = (name: string) => `bun scripts/release-ci/full-suite.ts box ${name}`
export function wrapped(job: Job): Record<string, unknown> {
  const w: Record<string, unknown> = {name: job.name, cmd: boxCommand(job.name), cwd: '.', timeout: Number(job.timeout ?? 3600) + INSTALL_SECONDS}
  for (const k of ['cpu', 'memory', 'image', 'env'] as const) if (job[k] !== undefined) w[k] = job[k]
  return w
}

const git = (args: string[]) => {
  const r = spawnSync('git', args, {cwd: ROOT, encoding: 'utf8'})
  if (r.status !== 0) fail(`git ${args.join(' ')}: ${r.stderr}`)
  return r.stdout.trim()
}

// The checkout is the commit being released, with every submodule at its gitlink, and nothing changed in it.
export function checkSource(): string {
  const commit = git(['rev-parse', 'HEAD'])
  if (process.env.GITHUB_SHA && process.env.GITHUB_SHA !== commit) fail(`checkout is ${commit}, not the run's commit ${process.env.GITHUB_SHA}`)
  const off = git(['submodule', 'status', '--recursive']).split('\n').filter(l => /^[-+U]/.test(l))
  if (off.length) fail(`submodules not at their gitlinks: ${off.join('; ')}`)
  const dirty = git(['status', '--porcelain=v1', '--untracked-files=all', '--ignore-submodules=none'])
  if (dirty) fail(`the checkout has changes or untracked files: ${dirty.split('\n').slice(0, 5).join('; ')}`)
  return commit
}

// The selected real `lean`, recorded before the canonical command's own tail/grep cuts its output (a known failure's
// signature is over complete Lean reports). The repo's scripts/lean-gate wrapper keeps working unchanged: its
// downstream compiler is this transparent recorder, which calls the original executable by absolute path.
export function diagnosticEnvironment(root: string, cwd: string, env: NodeJS.ProcessEnv): {env: NodeJS.ProcessEnv; readLogs: () => string[]} {
  const directory = join(root, 'lean-diagnostics'), bin = join(root, 'diagnostic-bin')
  mkdirSync(directory); mkdirSync(bin)
  const selected = spawnSync('bash', ['-c', 'type -P lean'], {cwd, env, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe']})
  const executable = selected.status === 0 ? selected.stdout.trim() : ''
  const readLogs = () => readdirSync(directory).sort().map(name => {
    const path = join(directory, name)
    if (!/^(?:lean|gate)\.[A-Za-z0-9]+\.log$/.test(name) || !lstatSync(path).isFile() || lstatSync(path).isSymbolicLink()) fail('unsafe compiler diagnostic record')
    return readFileSync(path, 'utf8')
  })
  if (!executable) return {env, readLogs}
  writeFileSync(join(bin, 'lean'), [
    '#!/bin/bash',
    'log=$(mktemp "$GDP_RELEASE_LEAN_LOGS/lean.XXXXXXXX.log") || exit 125',
    '"$GDP_RELEASE_REAL_LEAN" "$@" 2>&1 | tee "$log"',
    'statuses=("${PIPESTATUS[@]}")',
    '[ "${statuses[1]}" -eq 0 ] || exit 125',
    'exit "${statuses[0]}"',
    '',
  ].join('\n'), {mode: 0o700, flag: 'wx'})
  return {env: {...env, PATH: bin + delimiter + (env.PATH ?? ''), GDP_RELEASE_REAL_LEAN: isAbsolute(executable) ? executable : resolve(cwd, executable), GDP_RELEASE_LEAN_LOGS: directory}, readLogs}
}

// Lake calls its compiler by absolute path, outside the recorder: these are the full files the canonical commands
// write. And the keyed job's freshly generated source, not a stale checkout file.
const SUPPLEMENTARY: Record<string, string[]> = {'lean-package-0': ['/tmp/leanpkg/lake.out'], 'lean-protocols-sync': ['/tmp/e.log'], 'lean-protocols-wo': ['/tmp/e.log']}
function keyedSources(jobName: string, cwd: string, started: number): {file: string; source: string}[] {
  if (jobName !== 'lean-keyed') return []
  const path = join(cwd, 'Keyed.lean')
  if (!existsSync(path)) return []
  const stat = lstatSync(path)
  if (!stat.isFile() || stat.isSymbolicLink()) fail('unsafe Keyed source file')
  return stat.mtimeMs >= started ? [{file: 'Keyed.lean', source: readFileSync(path, 'utf8')}] : []
}

// One suite job on its box. supercomputer already set its image's PATH and env, `[run] pre` and the batch's
// $SUPERCOMPUTER_OUTPUT_DIR for this wrapper; the job's own command runs in its cwd under its own timeout.
export function box(name: string): number {
  const matches = suite().filter(j => j.name === name)
  if (matches.length !== 1) fail(`no single suite job named ${name}`)
  const job = matches[0]!
  const output = process.env.SUPERCOMPUTER_OUTPUT_DIR ?? ''
  if (!isAbsolute(output)) fail('no $SUPERCOMPUTER_OUTPUT_DIR')
  const gate = join(output, '.gate')
  mkdirSync(gate)
  const cwd = resolve(ROOT, job.cwd ?? '.')
  if (!cwd.startsWith(ROOT)) fail(`${name}: cwd escapes the tree`)
  const timeout = Number(job.timeout ?? 3600)
  if (!Number.isFinite(timeout) || timeout <= 0) fail(`${name}: invalid timeout`)
  const result: Result = {
    schema: 'gdp-full-suite-result/v1', name, definitionSha256: canonicalJobHash(job), batch: process.env.SUPERCOMPUTER_BATCH ?? '',
    code: 125, signal: null, seconds: 0, installed: false,
  }
  const finish = () => writeFileSync(join(gate, 'RESULT.json'), JSON.stringify(result, null, 1) + '\n')
  // The pinned dependencies, at the tree's root, before the job (its command may install again)
  const installLog = openSync(join(gate, 'dependency-install.log'), 'wx')
  try {
    const install = spawnSync('bun', ['install', '--frozen-lockfile'], {cwd: ROOT, env: process.env, stdio: ['ignore', installLog, installLog], timeout: INSTALL_SECONDS * 1000})
    result.installed = install.status === 0 && !install.signal && !install.error
  } finally { closeSync(installLog) }
  if (!result.installed) {
    console.error(`${name}: the pinned dependencies did not install (.gate/dependency-install.log)`)
    finish()
    return 125
  }
  const scratch = mkdtempSync(join(tmpdir(), 'full-suite-'))
  const diagnostics = diagnosticEnvironment(scratch, cwd, process.env)
  const stdout = openSync(join(gate, 'stdout.log'), 'wx'), stderr = openSync(join(gate, 'stderr.log'), 'wx')
  const started = Date.now()
  let r: ReturnType<typeof spawnSync>
  try {
    r = spawnSync('timeout', ['--signal=KILL', `${timeout}s`, 'bash', '-c', job.cmd], {cwd, env: diagnostics.env, stdio: ['ignore', stdout, stderr]})
  } finally { closeSync(stdout); closeSync(stderr) }
  result.code = r.status ?? 128
  result.signal = r.signal ?? null
  result.seconds = Math.round((Date.now() - started) / 1000)
  const logs = diagnostics.readLogs()
  for (const p of SUPPLEMENTARY[name] ?? []) {
    if (!existsSync(p)) continue
    const stat = lstatSync(p)
    if (!stat.isFile() || stat.isSymbolicLink()) fail('unsafe full diagnostic file')
    if (stat.mtimeMs >= started) logs.push(readFileSync(p, 'utf8'))
  }
  const sources = keyedSources(name, cwd, started)
  writeFileSync(join(gate, 'LEAN-DIAGNOSTICS.json'), JSON.stringify({schema: 'gdp-lean-diagnostics/v1', logs, ...(sources.length ? {sources} : {})}) + '\n')
  const out = readFileSync(join(gate, 'stdout.log'), 'utf8'), err = readFileSync(join(gate, 'stderr.log'), 'utf8')
  if (result.code !== 0) {
    try { result.signature = extractFailureSignature(out, err, logs, sources) }
    catch (e) { result.signatureError = e instanceof Error ? e.message : String(e) }
  }
  finish()
  // (the job's whole output in its supercomputer log too)
  process.stdout.write(out)
  process.stderr.write(err)
  return result.code
}

// A batch's state for one job, from batch.json's log replayed through supercomputer's batch rule.
export type JobState = {st: string; exit: number; attempts: number}
export type Batch = {id: string; tree: string; limits: {strictOnce: boolean; maxAttempts: number}; jobs: Record<string, unknown>[]}
export type Verdict = {passed: string[]; known: string[]; failed: {name: string; why: string}[]}

// Every suite job of this batch: passed, failed as known, or failed. `states` are the rule's, by the batch's job
// index; `results` reads a job's .gate/RESULT.json (undefined: none fetched).
export function judge(o: {jobs: Job[]; batch: Batch; tree: string; attempt: string; states: (i: number) => JobState | undefined; results: (name: string) => Result | undefined; policy: unknown}): Verdict {
  const v: Verdict = {passed: [], known: [], failed: []}
  const refuse = (why: string): Verdict => ({...v, failed: [{name: '(the batch)', why}]})
  // (a run attempt after the first could have re-run a failed job into a pass: never a release)
  if (o.attempt !== '1') return refuse(`attempt ${o.attempt}: the full gate counts only a run's first attempt`)
  if (o.batch.tree !== o.tree) return refuse(`the batch ran tree ${o.batch.tree}, not this checkout's ${o.tree}`)
  if (o.batch.limits.strictOnce !== true || o.batch.limits.maxAttempts !== 1) return refuse('the batch was not strict-once (one attempt, no retry)')
  const policy = validateKnownFailuresPolicy(o.policy, o.jobs)
  if (o.batch.jobs.length !== o.jobs.length) return refuse(`the batch has ${o.batch.jobs.length} jobs, the suite ${o.jobs.length}`)
  for (const [i, job] of o.jobs.entries()) {
    const ran = o.batch.jobs[i]!, want = wrapped(job)
    // (the batch's job i is this suite job through `box`, with its cwd, timeout and image; supercomputer fills
    // defaults for the rest)
    if ((['name', 'cmd', 'cwd', 'timeout', 'image'] as const).some(k => JSON.stringify(ran[k]) !== JSON.stringify(want[k]))) { v.failed.push({name: job.name, why: 'the batch ran another job in its place'}); continue }
    const s = o.states(i)
    if (!s) { v.failed.push({name: job.name, why: 'not in the batch'}); continue }
    if (s.attempts > 1) { v.failed.push({name: job.name, why: `${s.attempts} attempts (strict-once is one)`}); continue }
    if (s.st !== 'done') { v.failed.push({name: job.name, why: s.st === 'lost' ? 'lost with its box (strict-once: not tried again)' : `not answered (${s.st})`}); continue }
    const r = o.results(job.name)
    if (!r) { v.failed.push({name: job.name, why: `exit ${s.exit}, and no result of its own`}); continue }
    const why = r.schema !== 'gdp-full-suite-result/v1' ? 'not a full-suite result'
      : r.name !== job.name ? `the result of ${r.name}`
      : r.batch !== o.batch.id ? `from batch ${r.batch}`
      : r.definitionSha256 !== canonicalJobHash(job) ? 'run from another definition of the job'
      : r.code !== s.exit ? `its result says ${r.code}, the batch ${s.exit}` : ''
    if (why) { v.failed.push({name: job.name, why}); continue }
    if (s.exit === 0) { v.passed.push(job.name); continue }
    if (!r.installed) { v.failed.push({name: job.name, why: 'its pinned dependencies did not install'}); continue }
    if (!r.signature) { v.failed.push({name: job.name, why: `exit ${s.exit}${r.signatureError ? `; its failure has no signature: ${r.signatureError}` : ''}`}); continue }
    try {
      matchKnownFailure(policy, job.name, r.definitionSha256, s.exit, r.signature)
      v.known.push(job.name)
    } catch (e) {
      v.failed.push({name: job.name, why: `exit ${s.exit}: ${e instanceof Error ? e.message : String(e)}`})
    }
  }
  return v
}

// The verdict over a batch in OUT: batch.json's log replayed through the installed supercomputer's batch rule.
export async function verdict(out: string, supercomputer: string, tree: string, attempt = process.env.GITHUB_RUN_ATTEMPT ?? '1'): Promise<Verdict> {
  const batch = JSON.parse(readFileSync(join(out, 'batch.json'), 'utf8')) as Batch & {log: unknown[]}
  const {Engine} = await import(pathToFileURL(join(supercomputer, 'src/engine.ts')).href) as {Engine: new (limits: unknown, log: unknown[]) => {job: (i: number) => JobState | undefined}}
  const engine = new Engine(batch.limits, batch.log) // (refuses a log the rule would not take)
  const results = (name: string) => {
    const f = join(out, `${name}.files`, '.gate', 'RESULT.json')
    return existsSync(f) ? (JSON.parse(readFileSync(f, 'utf8')) as Result) : undefined
  }
  return judge({jobs: suite(), batch, tree, attempt, states: i => engine.job(i), results, policy: JSON.parse(readFileSync(join(ROOT, 'scripts/release-ci/known-failures.json'), 'utf8'))})
}

// The tree hash supercomputer gives this checkout (what batch.json's `tree` must be).
export async function treeHash(supercomputer: string): Promise<string> {
  const {pack} = await import(pathToFileURL(join(supercomputer, 'src/tree.ts')).href) as {pack: (root: string, ignore: string[]) => Promise<{hash: string}>}
  const {readConfig} = await import(pathToFileURL(join(supercomputer, 'src/jobs.ts')).href) as {readConfig: (root: string) => {ignore: string[]}}
  return (await pack(ROOT, readConfig(ROOT).ignore)).hash
}

if (import.meta.main) {
  const [mode, a, b, c] = process.argv.slice(2)
  const main = async (): Promise<number> => {
    if (mode === 'source') { console.log(checkSource()); return 0 }
    if (mode === 'jobs' && a) { writeFileSync(a, JSON.stringify(suite().map(wrapped), null, 1) + '\n'); console.log(`${suite().length} jobs: ${a}`); return 0 }
    if (mode === 'tree' && a) { console.log(await treeHash(resolve(a))); return 0 }
    if (mode === 'box' && a) return box(a)
    if (mode === 'verdict' && a && b && c) {
      const v = await verdict(resolve(a), resolve(b), c)
      const lines = [
        `## Full gate: ${v.failed.length ? 'refused' : 'passed'}`,
        `${v.passed.length} passed, ${v.known.length} known failures, ${v.failed.length} failed, of ${suite().length} suite jobs`,
        ...(v.known.length ? ['', `Known failures (known-failures.json): ${v.known.join(', ')}`] : []),
        ...(v.failed.length ? ['', 'Failed:', ...v.failed.map(f => `- ${f.name}: ${f.why}`)] : []),
      ]
      console.log(lines.join('\n'))
      if (process.env.GITHUB_STEP_SUMMARY) writeFileSync(process.env.GITHUB_STEP_SUMMARY, lines.join('\n') + '\n', {flag: 'a'})
      return v.failed.length ? 1 : 0
    }
    console.error('usage: full-suite.ts source | jobs FILE | tree SUPERCOMPUTER | box NAME | verdict OUT SUPERCOMPUTER TREE')
    return 2
  }
  main().then(code => { process.exitCode = code }, (e: unknown) => { console.error(e instanceof Error ? e.message : String(e)); process.exitCode = 1 })
}
