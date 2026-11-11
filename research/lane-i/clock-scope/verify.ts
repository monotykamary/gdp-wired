import {createHash} from 'node:crypto'
import {copyFileSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {resolve, join} from 'node:path'
import {spawnSync} from 'node:child_process'
const input = resolve('clock-input'), mode = process.argv[2]!, root = mkdtempSync(join(tmpdir(), 'lane-i-clock-'))
const env = {...process.env, GDP_WORK_FULL: mode === 'legacy' ? '0' : '1', GDP_WORK_STEPS: '0'}
function command(cmd: string, args: string[], failure = false): void {
  const result = spawnSync(cmd, args, {cwd: root, env, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024, timeout: 1_100_000})
  process.stdout.write(result.stdout ?? ''); process.stderr.write(result.stderr ?? '')
  if (result.error) throw result.error
  if (failure) {
    if (result.status === 0 || !`${result.stdout}${result.stderr}`.includes('Expected: 0')) throw new Error('baseline must fail specifically on a nonzero wall telemetry value')
  } else if (result.status !== 0) throw new Error(`${cmd} ${args.join(' ')} failed: ${result.status}`)
}
const identities = readFileSync(join(input, 'trusted-tree.txt'), 'utf8').trim().split('\n').map(line => {
  const match = /^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line)
  if (!match) throw new Error(`invalid source identity ${line}`)
  return {hash: match[1]!, path: match[2]!}
})
function checkTrusted(skipClock: boolean): void {
  for (const entry of identities) {
    if (skipClock && entry.path === 'kernel/prove.ts') continue
    const bytes = readFileSync(join(root, entry.path))
    const actual = createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex')
    if (actual !== entry.hash) throw new Error(`trusted source changed: ${entry.path}`)
  }
  console.log(JSON.stringify({kind: 'TRUSTED_IDENTITY', source: '5aa7681815e41a939fed137783b656abeeacc1e6', skipClock, checkedFiles: identities.length - Number(skipClock), checker: '5a5973def379a20065a6fab401cf089b4f21a159'}))
}
try {
  command('tar', ['-xf', join(input, 'source.tar'), '-C', root])
  for (const module of ['gdp-ts', 'handwired']) command('tar', ['-xf', join(input, `${module}.tar`), '-C', root])
  checkTrusted(false)
  const proveBefore = readFileSync(join(root, 'kernel/prove.ts'), 'utf8')
  const searchTail = proveBefore.slice(proveBefore.indexOf('export function grow('))
  if (!searchTail.startsWith('export function grow(')) throw new Error('missing prover boundary')
  if (mode === 'baseline') {
    writeFileSync(join(root, 'core/clock-baseline.test.ts'), `import {expect,test} from 'bun:test'\nimport {counted,fullRate} from '../kernel/prove.ts'\nimport {traceNow} from './trace-clock.ts'\ntest('counted telemetry must not read the wall',()=>counted(fullRate,()=>expect(traceNow()).toBe(0),true))\n`)
    command('bun', ['test', 'core/clock-baseline.test.ts'], true)
    console.log('CLOCK_BASELINE_REJECTED expected nonzero wall telemetry')
  } else {
    command('git', ['apply', '--check', join(input, 'clock-only.patch')])
    command('git', ['apply', join(input, 'clock-only.patch')])
    checkTrusted(true)
    const proveAfter = readFileSync(join(root, 'kernel/prove.ts'), 'utf8')
    if (proveAfter.slice(proveAfter.indexOf('export function grow(')) !== searchTail) throw new Error('non-clock prover/search implementation changed')
    copyFileSync(join(input, 'clock-tripwire.test.source'), join(root, 'core/clock-tripwire.test.ts'))
    copyFileSync(join(input, 'clock-tripwire-preload.source'), join(root, 'core/clock-tripwire-preload.ts'))
    command('bun', ['install', '--frozen-lockfile'])
    const tests = ['core/clock-tripwire.test.ts', 'core/count-work.test.ts', 'core/count-generation-budget.test.ts', 'core/count-tier-budget.test.ts', 'core/work-clock.test.ts', ...(mode === 'legacy' ? ['kernel/work-budget.test.ts', 'core/step-work.test.ts'] : [])]
    for (const path of tests) readFileSync(join(root, path))
    command('bun', ['test', '--preload', './core/clock-tripwire-preload.ts', ...tests])
    if (mode === 'full') {
      command('bun', ['run', 'check'])
      command('bun', ['add', '--dev', '@commitlint/cli', '@commitlint/config-conventional'])
      writeFileSync(join(root, 'commitlint.config.cjs'), "module.exports={extends:['@commitlint/config-conventional']};")
      command('git', ['init', '-q'])
      command('bunx', ['--bun', 'commitlint', '--config', 'commitlint.config.cjs', '--edit', join(input, 'COMMIT.txt')])
    }
    checkTrusted(true)
    console.log(JSON.stringify({kind: 'CLOCK_SCOPE_PASS', mode, source: '5aa7681815e41a939fed137783b656abeeacc1e6', trustedUnchanged: true}))
  }
} finally { rmSync(root, {recursive: true, force: true}) }
