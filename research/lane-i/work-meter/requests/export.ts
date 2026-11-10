import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {execFileSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
import {verifyRequestReceipts} from './verify.ts'
const verified = verifyRequestReceipts()
const {restore, command} = await import(resolve('recovery-input/final-gate-common.ts'))
const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
assert.equal(config.composition.patchSha256, verified.patchSha256)
assert.deepEqual(config.expectedCandidateBlobs, verified.expectedCandidateBlobs)
const temp = mkdtempSync('/tmp/lane-i-request-export-'), root = join(temp, 'source')
try {
  restore(resolve('recovery-input'), root, config.integrationBase)
  command('git', ['apply', resolve('validation-input/candidate.patch')], root)
  for (const [path, blob] of Object.entries(verified.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  command('git', ['add','-A'], root)
  const tree = command('git', ['write-tree'], root)
  const paths = ['core/infer.ts','core/request-materialization.test.ts','scripts/test-shards.ts']
  const saved = Object.fromEntries(paths.map(path => [path, readFileSync(join(root, path), 'utf8')]))
  const replace = (path: string, before: string, after: string) => { assert.equal(saved[path]!.split(before).length, 2); writeFileSync(join(root, path), saved[path]!.replace(before, after)) }
  replace(paths[0]!, '(coreMeter.tableCells += Object.keys(c).length + 1, {...c, [i]: v2})', '({...c, [i]: v2})')
  rmSync(join(root, paths[1]!))
  replace(paths[2]!, 'meter-complete.test.ts request-materialization.test.ts', 'meter-complete.test.ts')
  command('git', ['add','-A'], root)
  const parentTree = command('git', ['write-tree'], root)
  assert.equal(parentTree, '1938f7d70a7ed5fb0369a0e76e2e0c2b5a113131', 'reversing only the three intended changes must reproduce exact 41d39043')
  for (const path of paths) writeFileSync(join(root, path), saved[path]!)
  command('git', ['add','-A'], root); assert.equal(command('git', ['write-tree'], root), tree)
  assert.deepEqual(command('git', ['diff','--cached','--name-only',parentTree], root).split('\n').sort(), paths)
  const delta = execFileSync('git', ['diff','--cached','--binary',parentTree], {cwd: root, encoding: 'utf8'})
  const patchSha256 = createHash('sha256').update(delta).digest('hex')
  console.log('REQUEST_SOURCE_EXPORT ' + JSON.stringify({passed: true, parentSource: '41d39043', parentTree, tree, fullPatchSha256: verified.patchSha256, patchSha256, bytes: Buffer.byteLength(delta), encoding: 'gzip-base64', data: gzipSync(delta).toString('base64'), expectedCandidateBlobs: verified.expectedCandidateBlobs, admitted: false}))
} finally { rmSync(temp, {recursive: true, force: true}) }
