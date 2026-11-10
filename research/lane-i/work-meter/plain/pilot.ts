import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync, copyFileSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {spawnSync, type SpawnSyncReturns} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
const {restore, command} = await import(resolve('recovery-input/final-gate-common.ts'))
const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
assert.equal(config.composition.patchSha256, 'f59720c766a68a2647cb150c6f3e0793363aa36804eb6bc3185430488f0eebe0')
const temp = mkdtempSync('/tmp/lane-i-plain-clock-'), root = join(temp, 'source')
const changed: string[] = []
function update(path: string, mutate: (text: string) => string) {
  const before = readFileSync(join(root, path), 'utf8'), after = mutate(before)
  assert.notEqual(before, after, path + ' changed')
  writeFileSync(join(root, path), after); changed.push(path)
}
function one(text: string, from: string, to: string) { assert.equal(text.split(from).length, 2, 'unique anchor ' + from); return text.replace(from, to) }
function clocks(text: string) { assert(text.includes('performance.now()')); return text.replaceAll('performance.now()', 'searchNow()') }
function run(args: string[], label: string, timeout = 180000) {
  const child: SpawnSyncReturns<string> = spawnSync('bun', args, {cwd: root, encoding: 'utf8', timeout, maxBuffer: 16 * 1024 * 1024})
  console.log('PLAIN_CLOCK_CHECK ' + JSON.stringify({label, exit: child.status, signal: child.signal, error: String(child.error ?? '')}))
  console.log(child.stdout); if (child.stderr) console.error(child.stderr)
  assert.equal(child.status, 0, label)
}
try {
  restore(resolve('recovery-input'), root, config.integrationBase)
  command('git', ['apply', resolve('validation-input/candidate.patch')], root)
  for (const [path, blob] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  command('git', ['add', '-A'], root)
  const parentTree = command('git', ['write-tree'], root)
  update('core/dsl.ts', text => {
    text = one(text, "import {traceNow, searchNow, WallExpired, checkWall, searchWall, withBudget, checkBudget, BudgetExpired} from './wall.ts'", "import {traceNow, searchNow, WallExpired, checkWall, searchWall, withBudget, checkBudget, BudgetExpired} from './wall.ts'\nimport {completeWorkWeights, extraWorkKeys} from './work-meter.ts'")
    text = one(text, "      if (work !== undefined && !Object.keys(r.machine.counts ?? {}).length) return {proven: false, checked: false, stuck: 'unknown', why: 'work mode: plain-path migration pending'}", "      if (work !== undefined && !Object.keys(r.machine.counts ?? {}).length) {\n        const weights = completeWorkWeights()\n        if (!weights) return {proven: false, checked: false, stuck: 'unknown', why: 'work mode: plain-path migration pending'}\n        if (extraWorkKeys.some(key => weights[key] <= 0)) return {proven: false, checked: false, stuck: 'unknown', why: 'work mode: plain-path requires positive complete weights'}\n      }")
    return clocks(text)
  })
  update('core/bmc.ts', text => clocks(one(text, "import {clock, counted, fullRate} from '../kernel/prove.ts'", "import {clock, counted, fullRate, searchNow} from '../kernel/prove.ts'")))
  update('core/kind.ts', text => clocks(one(text, "import {clock, counted, grow, proveLaws, type Outcome} from '../kernel/prove.ts'", "import {clock, counted, grow, proveLaws, searchNow, type Outcome} from '../kernel/prove.ts'")))
  update('core/tpa.ts', text => clocks(one(text, "import {clock} from '../kernel/prove.ts'", "import {clock, searchNow} from '../kernel/prove.ts'")))
  update('kernel/prove.ts', text => {
    text = one(text, "import {fullWork} from '../core/work-meter.ts'", "import {completeWorkWeights, fullWork} from '../core/work-meter.ts'")
    return one(text, 'const eprTimeSince = (start: number): number => rate ? (eprMeter.n - start) / rate : 0', 'const eprTimeSince = (start: number): number => rate && !(inBudget() && (completeWorkWeights()?.epr ?? 0) > 0) ? (eprMeter.n - start) / rate : 0')
  })
  const expected = {...config.expectedCandidateBlobs}
  for (const path of changed) expected[path] = command('git', ['hash-object', path], root)
  const delta = command('git', ['diff', '--binary'], root) + '\n'
  const patchSha256 = createHash('sha256').update(delta).digest('hex')
  console.log('PLAIN_CLOCK_SOURCE ' + JSON.stringify({parentPatch: config.composition.patchSha256, parentTree, patchSha256, changed, expectedCandidateBlobs: expected, scope: 'experimental complete-positive test weights only; no production weights or W'}))
  copyFileSync('plain-input/plain-work.test.source', join(root, 'core/plain-work.test.ts'))
  run(['install', '--frozen-lockfile'], 'dependencies')
  run(['test', './core/plain-work.test.ts', './core/wall.test.ts', './kernel/work-budget.test.ts', './core/work-clock.test.ts', './core/work-entry.test.ts'], 'ordinary-clock-controls')
  run(['run', 'check'], 'type-lint')
  for (const [path, blob] of Object.entries(expected)) assert.equal(command('git', ['hash-object', path], root), blob, 'source unchanged after prototype tests')
  console.log('PLAIN_CLOCK_PATCH ' + JSON.stringify({encoding: 'gzip-base64', patchSha256, bytes: Buffer.byteLength(delta), data: gzipSync(delta).toString('base64'), admitted: false}))
} finally { rmSync(temp, {recursive: true, force: true}) }
