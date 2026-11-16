// Development-only wrapper: execute an unchanged canonical job and retain its
// complete Lean diagnostics, including output hidden by its original tail/grep.
import {spawnSync} from 'node:child_process'
import {closeSync, copyFileSync, existsSync, mkdirSync, mkdtempSync, openSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'
import {diagnosticEnvironment} from '../../scripts/release-ci/full-gate-worker.ts'

type Job = {name: string, cmd: string, cwd?: string, timeout?: number}
const [input, name] = process.argv.slice(2)
if (!input || !name) throw Error('usage: 0502-lean-command JOBS_JSON JOB_NAME')
const jobs = JSON.parse(readFileSync(input, 'utf8')) as Job[]
const selected = jobs.filter(j => j.name === name)
if (selected.length !== 1) throw Error('expected one canonical job')
const job = selected[0]!, output = process.env.SUPERCOMPUTER_OUTPUT_DIR
if (!output) throw Error('native output directory required')
const root = mkdtempSync(join(tmpdir(), 'gdp-0502-lean-')), cwd = resolve(job.cwd ?? '.')
try {
  const diag = diagnosticEnvironment(root, cwd, process.env)
  // Retain the exact generated Proofs source before its temporary workdir is
  // removed. The real compiler command, arguments and exit status are unchanged.
  const wrapper = join(root, 'diagnostic-bin', 'lean')
  if (existsSync(wrapper)) {
    const original = readFileSync(wrapper, 'utf8')
    const anchor = '"$GDP_RELEASE_REAL_LEAN" "$@" 2>&1 | tee "$log"'
    if (!original.includes(anchor)) throw Error('diagnostic wrapper contract changed')
    const capture = 'for arg in "$@"; do case "$arg" in */Proofs.lean|Proofs.lean|Keyed.lean|P_*.lean) if [ -f "$arg" ]; then cp "$arg" "$SUPERCOMPUTER_OUTPUT_DIR/$(basename "$arg")" || exit 125; fi;; esac; done\n'
    writeFileSync(wrapper, original.replace(anchor, capture + anchor), {mode: 0o700})
  }
  mkdirSync(output, {recursive: true})
  const stdout = openSync(join(output, 'stdout.log'), 'w'), stderr = openSync(join(output, 'stderr.log'), 'w')
  let result: ReturnType<typeof spawnSync>
  try {
    const args = job.timeout === undefined ? ['-c', job.cmd] : ['--signal=KILL', `${job.timeout}s`, 'bash', '-c', job.cmd]
    result = spawnSync(job.timeout === undefined ? 'bash' : 'timeout', args, {cwd, env: diag.env, stdio: ['ignore', stdout, stderr]})
  } finally { closeSync(stdout); closeSync(stderr) }
  const logs = diag.readLogs()
  if (name === 'lean-package-0' && existsSync('/tmp/leanpkg/lake.out')) {
    logs.push(readFileSync('/tmp/leanpkg/lake.out', 'utf8'))
    if (existsSync('/tmp/leanpkg/Proofs.lean')) copyFileSync('/tmp/leanpkg/Proofs.lean', join(output, 'Proofs.lean'))
  }
  writeFileSync(join(output, 'LEAN-DIAGNOSTICS.json'), JSON.stringify({schema: 'gdp-lean-development-diagnostics/v1', logs}) + '\n')
  writeFileSync(join(output, 'COMMAND-RESULT.json'), JSON.stringify({name, command: job.cmd, cwd: job.cwd ?? '.', code: result.status, signal: result.signal, error: result.error?.message ?? null}) + '\n')
  console.log(JSON.stringify({name, code: result.status, signal: result.signal, diagnosticLogs: logs.length}))
  console.log(readFileSync(join(output, 'stdout.log'), 'utf8').slice(-5000))
  console.error(readFileSync(join(output, 'stderr.log'), 'utf8').slice(-2000))
  process.exitCode = result.status ?? 128
} finally { rmSync(root, {recursive: true, force: true}) }
