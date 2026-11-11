import {strict as assert} from 'node:assert'
import {readFileSync, copyFileSync, mkdirSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {createHash} from 'node:crypto'
const {restore, command} = await import(resolve('recovery-input/final-gate-common.ts'))
const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
const patch = '8df0cf2ac466465a45683a639124d5f774e1b85b72d7f36c1b42b682c4e46fbd'
assert.equal(config.composition.patchSha256, patch)
const log = readFileSync('pilot-input/f3-timed-numeric-mldr.log', 'utf8')
const rows = (tag: string) => log.split('\n').filter(line => line.startsWith(tag + ' ')).map(line => JSON.parse(line.slice(tag.length + 1)))
const comparison = rows('F3_PILOT_COMPARISON'), audits = rows('F3_RAW_PILOT_AUDIT'), stable = rows('F3_RAW_SILENCE')
assert.equal(comparison.length, 1); assert.equal(comparison[0].patchSha256, patch)
assert.equal(comparison[0].sourceUnchanged, true)
assert.equal(audits.length, 1); assert.equal(audits[0].passed, true); assert.equal(audits[0].timedWindowChecks, true)
assert.equal(stable.length, 3)
assert(stable.every(row => row.stable && row.whileRunning && row.heartbeatBefore === row.heartbeatAfter && row.profileWindow.valid && row.profileWindow.samplesInWindow > 0))
const temp = mkdtempSync('/tmp/lane-i-timed-map-'), root = join(temp, 'source')
try {
  restore(resolve('recovery-input'), root, config.integrationBase)
  command('git', ['apply', resolve('validation-input/candidate.patch')], root)
  for (const [path, blob] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  command('bun', ['install', '--frozen-lockfile'], root, 180000)
  const tooling = join(root, 'research/lane-i/f3'); mkdirSync(tooling, {recursive: true}); mkdirSync(join(root, 'f3-output'))
  copyFileSync('f3-input/facade.source', join(tooling, 'facade.ts'))
  command('bun', ['build', './research/lane-i/f3/facade.ts', '--target=node', '--format=esm', '--outfile=./f3-output/facade.mjs', '--sourcemap=inline'], root, 180000)
  const bundle = readFileSync(join(root, 'f3-output/facade.mjs'), 'utf8'), lines = bundle.split('\n')
  const mapped = stable.map(window => {
    const frames = window.stack.filter((frame: any) => frame.url.endsWith('/facade.mjs')).slice(0, 4).map((frame: any) => {
      assert(Number.isInteger(frame.lineNumber) && frame.lineNumber >= 0 && frame.lineNumber < lines.length)
      const context = lines.slice(Math.max(0, frame.lineNumber - 3), frame.lineNumber + 4)
      const modules = lines.slice(0, frame.lineNumber + 1).filter(line => /^\/\/ .*\.ts$/.test(line))
      return {functionName: frame.functionName, lineNumber: frame.lineNumber, columnNumber: frame.columnNumber, sourceModule: modules.at(-1), context}
    })
    assert(frames.length > 0)
    const anchor = frames[0]
    assert(['canon2', 'canonFlip'].includes(anchor.functionName))
    assert(anchor.context.join('\n').includes(anchor.functionName), 'named line anchor must match regenerated bundle')
    return {report: window.reports, profileWindow: window.profileWindow, frames}
  })
  for (const [path, blob] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  console.log('F3_TIMED_STACK_RECONSTRUCTION ' + JSON.stringify({sourcePatch: patch, sourceUnchanged: true, bun: process.versions.bun,
    regeneratedBundleSha256: createHash('sha256').update(bundle).digest('hex'), stableWindows: stable.length, mapped,
    scope: 'same-source named-frame reconstruction, not exact native instructions, Bun F3, or a new solver run'}))
} finally { rmSync(temp, {recursive: true, force: true}) }
