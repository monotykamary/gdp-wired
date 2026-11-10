import {strict as assert} from 'node:assert'
import {readFileSync, copyFileSync, mkdirSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {createHash} from 'node:crypto'
const {restore, command} = await import(resolve('recovery-input/final-gate-common.ts'))
const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
assert.equal(config.composition.patchSha256, '2c98e5dc8d92da3b1f6833c1e1a331de24b559349c30cc44f52ec5c2a6c53ac2')
const log = readFileSync('node-result/f3-request-mldr-pilot.log', 'utf8')
const stable = log.split('\n').filter(line => line.startsWith('F3_RAW_SILENCE ')).map(line => JSON.parse(line.slice('F3_RAW_SILENCE '.length)))
assert.equal(stable.length, 2)
assert(stable.every(row => row.stable && row.whileRunning && row.heartbeatBefore === row.heartbeatAfter))
const app = stable.filter(row => row.stack.some((frame: any) => frame.functionName === 'canon2'))
assert.equal(app.length, 1)
const frames = app[0].stack.filter((frame: any) => frame.url.endsWith('/facade.mjs')).slice(0, 3)
const temp = mkdtempSync('/tmp/lane-i-stack-map-'), root = join(temp, 'source')
try {
  restore(resolve('recovery-input'), root, config.integrationBase)
  command('git', ['apply', resolve('validation-input/candidate.patch')], root)
  for (const [path, blob] of Object.entries(config.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  command('bun', ['install','--frozen-lockfile'], root, 180000)
  const tooling = join(root, 'research/lane-i/f3'); mkdirSync(tooling, {recursive: true}); mkdirSync(join(root, 'f3-output'))
  copyFileSync('f3-input/facade.source', join(tooling, 'facade.ts'))
  command('bun', ['build','./research/lane-i/f3/facade.ts','--target=node','--format=esm','--outfile=./f3-output/facade.mjs','--sourcemap=inline'], root, 180000)
  const bundle = readFileSync(join(root, 'f3-output/facade.mjs'), 'utf8'), lines = bundle.split('\n')
  const mapped = frames.map((frame: any) => {
    assert(Number.isInteger(frame.lineNumber) && frame.lineNumber >= 0 && frame.lineNumber < lines.length)
    const context = lines.slice(Math.max(0, frame.lineNumber - 3), frame.lineNumber + 4)
    const modules = lines.slice(0, frame.lineNumber + 1).filter(line => /^\/\/ .*\.ts$/.test(line))
    return {functionName: frame.functionName, lineNumber: frame.lineNumber, columnNumber: frame.columnNumber, sourceModule: modules.at(-1), context}
  })
  const anchor = mapped.find((frame: any) => frame.functionName === 'canon2')
  assert(anchor && anchor.context.join('\n').includes('canon2'), 'named line anchor must match regenerated bundle')
  console.log('F3_STABLE_STACK_RECONSTRUCTION ' + JSON.stringify({sourcePatch: config.composition.patchSha256, bun: process.versions.bun, regeneratedBundleSha256: createHash('sha256').update(bundle).digest('hex'), stableApplicationWindows: app.length, stableGcWindows: stable.length - app.length, mapped, scope: 'same-source generated-line reconstruction; no additional solver run and no Bun F3 claim'}))
} finally { rmSync(temp, {recursive: true, force: true}) }
