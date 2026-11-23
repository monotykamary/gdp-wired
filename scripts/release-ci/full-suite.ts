// The release's full gate, inside GitHub Actions (publish.yml): every job of supercomputer/suite.json run once, on a
// fresh instabox box, at the exact commit being published, and a release only when each passed or failed exactly as
// known-failures.json records (the same job definition, exit code and failure signature).
//
//   bun scripts/release-ci/full-suite.ts matrix          the GitHub matrix: one entry per suite job, with its runs-on
//   bun scripts/release-ci/full-suite.ts run NAME OUT    one job, as supercomputer runs it; OUT gets RESULT.json, its
//                                                        logs, its Lean diagnostics and files/ ($SUPERCOMPUTER_OUTPUT_DIR)
//   bun scripts/release-ci/full-suite.ts gate DIR        every job's RESULT.json (DIR/<name>/RESULT.json): the verdict
//
// A job runs as supercomputer would run it on its box: `bash -c "<[run] pre><cmd>"` in its cwd, under its timeout
// (default 3600 s), with its image's PATH entries first and its image's and its own env. Its box is the instabox CI
// box `instabox-large-snapshot-<snapshot>`: the snapshot its image names in supercomputer.toml (an image with no
// setup of its own, like `runner`, is the repo's snapshot with its own PATH and env). The olean [[cache]] is not kept
// between CI boxes: each Lean job builds what it needs.

import {spawnSync} from 'node:child_process'
import {closeSync, existsSync, lstatSync, mkdirSync, mkdtempSync, openSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {homedir, tmpdir} from 'node:os'
import {delimiter, isAbsolute, join, resolve} from 'node:path'
import {canonicalJobHash, type CanonicalJob} from './job-hash'
import {extractFailureSignature, matchKnownFailure, validateKnownFailuresPolicy, type FailureSignature} from './known-failures'

const ROOT = resolve(import.meta.dir, '../..')
const fail = (message: string): never => { throw new Error(`full-suite: ${message}`) }

type Job = CanonicalJob & {cwd?: string; timeout?: number; env?: Record<string, string>; image?: string}
type Image = {snapshot?: string; path: string[]; env: Record<string, string>; setup?: string}
export type Result = {
  schema: 'gdp-full-suite-result/v1'; name: string; definitionSha256: string; commit: string
  runId: string; runAttempt: string; code: number; signal: string | null; seconds: number
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

// supercomputer.toml's images, as supercomputer reads them (src/jobs.ts): a named image adds its PATH entries before
// the repo's and its env over the repo's; one with no setup of its own runs on the repo's snapshot.
export function images(root = ROOT): {pre: string; base: Image; named: Record<string, Image>} {
  const t = Bun.TOML.parse(readFileSync(join(root, 'supercomputer.toml'), 'utf8')) as Record<string, any>
  const ib = t.instabox ?? {}
  const base: Image = {snapshot: ib.snapshot, path: ib.path ?? [], env: ib.env ?? {}}
  const named: Record<string, Image> = {}
  for (const [k, v] of Object.entries((ib.images ?? {}) as Record<string, any>))
    named[k] = {snapshot: v.snapshot ?? (v.setup ? undefined : base.snapshot), path: [...(v.path ?? []), ...base.path], env: {...base.env, ...(v.env ?? {})}, setup: v.setup}
  return {pre: t.run?.pre ?? '', base, named}
}

const imageOf = (job: Job, im: ReturnType<typeof images>): Image => {
  if (!job.image) return im.base
  return im.named[job.image] ?? fail(`${job.name}: no image ${job.image} in supercomputer.toml`)
}

export function matrix(root = ROOT): {include: {name: string; runsOn: string}[]} {
  const im = images(root)
  const include = suite(root).map(job => {
    const img = imageOf(job, im)
    if (!img.snapshot) fail(`${job.name}: its image has no snapshot (supercomputer image build${job.image ? ` ${job.image}` : ''})`)
    return {name: job.name, runsOn: `instabox-large-snapshot-${img.snapshot}`}
  })
  // (GitHub runs at most 256 jobs of one matrix)
  if (include.length > 256) fail(`${include.length} suite jobs: more than one matrix (256) holds`)
  return {include}
}

const git = (args: string[]) => {
  const r = spawnSync('git', args, {cwd: ROOT, encoding: 'utf8'})
  if (r.status !== 0) fail(`git ${args.join(' ')}: ${r.stderr}`)
  return r.stdout.trim()
}

// The checkout is the commit being released, with every submodule at its gitlink, and nothing changed in it.
function checkSource(): string {
  const commit = git(['rev-parse', 'HEAD'])
  if (process.env.GITHUB_SHA && process.env.GITHUB_SHA !== commit) fail(`checkout is ${commit}, not the run's commit ${process.env.GITHUB_SHA}`)
  const subs = git(['submodule', 'status', '--recursive']).split('\n').filter(Boolean)
  const off = subs.filter(l => /^[-+U]/.test(l))
  if (off.length) fail(`submodules not at their gitlinks: ${off.join('; ')}`)
  const dirty = git(['status', '--porcelain=v1', '--untracked-files=no', '--ignore-submodules=none'])
  if (dirty) fail(`the checkout has changes: ${dirty.split('\n').slice(0, 5).join('; ')}`)
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

export function run(name: string, out: string): number {
  const matches = suite().filter(j => j.name === name)
  if (matches.length !== 1) fail(`no single suite job named ${name}`)
  const job = matches[0]!
  const commit = checkSource()
  const im = images(), img = imageOf(job, im)
  const cwd = resolve(ROOT, job.cwd ?? '.')
  if (!cwd.startsWith(ROOT)) fail(`${name}: cwd escapes the checkout`)
  const timeout = Number(job.timeout ?? 3600)
  if (!Number.isFinite(timeout) || timeout <= 0) fail(`${name}: invalid timeout`)
  mkdirSync(out, {recursive: true})
  const files = join(out, 'files')
  mkdirSync(files)
  const home = process.env.HOME ?? homedir()
  const path = img.path.map(p => p.replace(/^~(?=\/|$)/, home)).join(delimiter)
  const env: NodeJS.ProcessEnv = {
    ...process.env, ...img.env, ...(job.env ?? {}),
    PATH: path ? path + delimiter + (process.env.PATH ?? '') : process.env.PATH,
    SUPERCOMPUTER_OUTPUT_DIR: files, SUPERCOMPUTER_JOB: name, SUPERCOMPUTER_BATCH: `gh-${process.env.GITHUB_RUN_ID ?? 'local'}`,
  }
  const scratch = mkdtempSync(join(tmpdir(), 'full-suite-'))
  const diagnostics = diagnosticEnvironment(scratch, cwd, env)
  const stdout = openSync(join(out, 'stdout.log'), 'wx'), stderr = openSync(join(out, 'stderr.log'), 'wx')
  const started = Date.now()
  let r: ReturnType<typeof spawnSync>
  try {
    r = spawnSync('timeout', ['--signal=KILL', `${timeout}s`, 'bash', '-c', im.pre + job.cmd], {cwd, env: diagnostics.env, stdio: ['ignore', stdout, stderr]})
  } finally { closeSync(stdout); closeSync(stderr) }
  const code = r.status ?? 128
  const logs = diagnostics.readLogs()
  for (const p of SUPPLEMENTARY[name] ?? []) {
    if (!existsSync(p)) continue
    const stat = lstatSync(p)
    if (!stat.isFile() || stat.isSymbolicLink()) fail('unsafe full diagnostic file')
    if (stat.mtimeMs >= started) logs.push(readFileSync(p, 'utf8'))
  }
  const sources = keyedSources(name, cwd, started)
  writeFileSync(join(out, 'LEAN-DIAGNOSTICS.json'), JSON.stringify({schema: 'gdp-lean-diagnostics/v1', logs, ...(sources.length ? {sources} : {})}) + '\n')
  const result: Result = {
    schema: 'gdp-full-suite-result/v1', name, definitionSha256: canonicalJobHash(job), commit,
    runId: process.env.GITHUB_RUN_ID ?? 'local', runAttempt: process.env.GITHUB_RUN_ATTEMPT ?? '1',
    code, signal: r.signal ?? null, seconds: Math.round((Date.now() - started) / 1000),
  }
  if (code !== 0) {
    try { result.signature = extractFailureSignature(readFileSync(join(out, 'stdout.log'), 'utf8'), readFileSync(join(out, 'stderr.log'), 'utf8'), logs, sources) }
    catch (e) { result.signatureError = e instanceof Error ? e.message : String(e) }
  }
  writeFileSync(join(out, 'RESULT.json'), JSON.stringify(result, null, 1) + '\n')
  // (the end of its output in the job's log; all of it is in the artifact)
  for (const f of ['stdout.log', 'stderr.log']) {
    const lines = readFileSync(join(out, f), 'utf8').split('\n')
    console.log(`--- ${f} (last ${Math.min(lines.length, 150)} of ${lines.length} lines)`)
    console.log(lines.slice(-150).join('\n'))
  }
  console.log(`${name}: exit ${code}${r.signal ? ` (${r.signal})` : ''} in ${result.seconds} s`)
  return code
}

export type Verdict = {passed: string[]; known: string[]; failed: {name: string; why: string}[]}

// Every suite job's result, at this commit, from this run's first attempt: passed, failed as known, or failed.
export function gate(dir: string, commit = process.env.GITHUB_SHA ?? git(['rev-parse', 'HEAD']), attempt = process.env.GITHUB_RUN_ATTEMPT ?? '1', root = ROOT): Verdict {
  const jobs = suite(root)
  const policy = validateKnownFailuresPolicy(JSON.parse(readFileSync(join(root, 'scripts/release-ci/known-failures.json'), 'utf8')), jobs)
  const v: Verdict = {passed: [], known: [], failed: []}
  // (a run attempt after the first could have re-run a failed job into a pass: never a release)
  if (attempt !== '1') return {...v, failed: [{name: '(the run)', why: `attempt ${attempt}: the full gate counts only a run's first attempt`}]}
  for (const job of jobs) {
    // (each job's artifact, full-suite-<name>, as download-artifact lays them out; or a plain <name> folder)
    const file = [join(dir, `full-suite-${job.name}`, 'RESULT.json'), join(dir, job.name, 'RESULT.json')].find(f => existsSync(f)) ?? ''
    if (!file) { v.failed.push({name: job.name, why: 'no result (its job did not finish)'}); continue }
    const r = JSON.parse(readFileSync(file, 'utf8')) as Result
    const why = r.schema !== 'gdp-full-suite-result/v1' ? 'not a full-suite result'
      : r.name !== job.name ? `the result of ${r.name}`
      : r.commit !== commit ? `run at ${r.commit}, not ${commit}`
      : r.runAttempt !== '1' ? `from attempt ${r.runAttempt}`
      : r.definitionSha256 !== canonicalJobHash(job) ? 'run from another definition of the job' : ''
    if (why) { v.failed.push({name: job.name, why}); continue }
    if (r.code === 0) { v.passed.push(job.name); continue }
    if (!r.signature) { v.failed.push({name: job.name, why: `exit ${r.code}${r.signatureError ? `; its failure has no signature: ${r.signatureError}` : ''}`}); continue }
    try {
      matchKnownFailure(policy, job.name, r.definitionSha256, r.code, r.signature)
      v.known.push(job.name)
    } catch (e) {
      v.failed.push({name: job.name, why: `exit ${r.code}: ${e instanceof Error ? e.message : String(e)}`})
    }
  }
  return v
}

if (import.meta.main) {
  const [mode, a, b] = process.argv.slice(2)
  try {
    if (mode === 'matrix') console.log(JSON.stringify(matrix()))
    else if (mode === 'run' && a && b) process.exitCode = run(a, resolve(b))
    else if (mode === 'gate' && a) {
      const v = gate(resolve(a))
      const lines = [
        `## Full gate: ${v.failed.length ? 'refused' : 'passed'}`,
        `${v.passed.length} passed, ${v.known.length} known failures, ${v.failed.length} failed, of ${suite().length} suite jobs`,
        ...(v.known.length ? ['', `Known failures (known-failures.json): ${v.known.join(', ')}`] : []),
        ...(v.failed.length ? ['', 'Failed:', ...v.failed.map(f => `- ${f.name}: ${f.why}`)] : []),
      ]
      console.log(lines.join('\n'))
      if (process.env.GITHUB_STEP_SUMMARY) writeFileSync(process.env.GITHUB_STEP_SUMMARY, lines.join('\n') + '\n', {flag: 'a'})
      process.exitCode = v.failed.length ? 1 : 0
    } else {
      console.error('usage: full-suite.ts matrix | run NAME OUT | gate DIR'); process.exitCode = 2
    }
  } catch (e) {
    console.error(e instanceof Error ? e.message : e); process.exitCode = 1
  }
}
