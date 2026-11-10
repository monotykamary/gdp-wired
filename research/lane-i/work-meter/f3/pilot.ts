import {strict as assert} from 'node:assert'
import {readFileSync, copyFileSync, mkdirSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
const {restore, command} = await import(resolve('recovery-input/final-gate-common.ts'))
const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
if (process.argv.includes('--canonical')) {
  assert.equal(config.composition.mode, 'canonical')
  assert.equal(config.composition.patchSha256, 'f59720c766a68a2647cb150c6f3e0793363aa36804eb6bc3185430488f0eebe0')
}
const temp = mkdtempSync('/tmp/lane-i-f3-'), root = join(temp, 'source')
try {
  restore(resolve('recovery-input'), root, config.integrationBase)
  command('git', ['apply', resolve('validation-input/candidate.patch')], root)
  for (const [path, blob] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  command('bun', ['install', '--frozen-lockfile'], root, 180000)
  const tooling = join(root, 'research/lane-i/f3'), output = join(root, 'f3-output')
  mkdirSync(tooling, {recursive: true}); mkdirSync(output)
  copyFileSync('f3-input/facade.source', join(tooling, 'facade.ts'))
  for (const file of ['solver-observer.mjs', 'observer-worker.mjs', 'profile-window.mjs']) copyFileSync(join('f3-input', file), join(output, file))
  command('bun', ['build', './research/lane-i/f3/facade.ts', '--target=node', '--format=esm', '--outfile=./f3-output/facade.mjs', '--sourcemap=inline'], root, 180000)
  const results: Record<string, {id: string, result: object, raw: object}> = {}
  for (const mode of ['off', 'on']) {
    const process = spawnSync('node', ['f3-output/solver-observer.mjs', mode], {cwd: root, encoding: 'utf8', timeout: 600000, maxBuffer: 16 * 1024 * 1024})
    console.log('F3_PILOT_PROCESS ' + JSON.stringify({mode, exit: process.status, signal: process.signal, error: String(process.error ?? ''), stdoutSha256: createHash('sha256').update(process.stdout ?? '').digest('hex')}))
    console.log(process.stdout); if (process.stderr) console.error(process.stderr.slice(-12000))
    assert.equal(process.status, 0, 'external crash guard is an infrastructure failure, not unknown')
    const lines = process.stdout.split('\n').filter(line => line.startsWith('F3_SOLVER_RESULT '))
    assert.equal(lines.length, 1)
    results[mode] = JSON.parse(lines[0]!.slice('F3_SOLVER_RESULT '.length))
  }
  const same = JSON.stringify(results.off!.raw) === JSON.stringify(results.on!.raw) && JSON.stringify(results.off!.result) === JSON.stringify(results.on!.result)
  for (const [path, blob] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob, 'source unchanged after observation')
  console.log('F3_PILOT_COMPARISON ' + JSON.stringify({sameRawAndVerdict: same, source: config.candidate, patchSha256: config.composition.patchSha256, sourceUnchanged: true, scope: 'Node raw-progress pilot only; no Bun F3, no calibrated W, no full census'}))
  assert(same, 'observer must not change raw counts or verdict')
} finally { rmSync(temp, {recursive: true, force: true}) }
