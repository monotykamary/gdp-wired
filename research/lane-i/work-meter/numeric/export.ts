import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync, mkdtempSync, rmSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {execFileSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
import {verifyNumericReceipts} from './verify.ts'
const verified = verifyNumericReceipts()
const {restore, command} = await import(resolve('recovery-input/final-gate-common.ts'))
const config = JSON.parse(readFileSync('validation-input/identity.json', 'utf8'))
assert.equal(config.composition.patchSha256, verified.patchSha256)
assert.deepEqual(config.expectedCandidateBlobs, verified.expectedCandidateBlobs)
const temp = mkdtempSync('/tmp/lane-i-numeric-export-'), root = join(temp, 'source')
try {
  restore(resolve('recovery-input'), root, config.integrationBase)
  command('git', ['apply', resolve('validation-input/candidate.patch')], root)
  for (const [path, blob] of Object.entries(verified.expectedCandidateBlobs)) assert.equal(command('git', ['hash-object', path], root), blob)
  command('git', ['add','-A'], root)
  const tree = command('git', ['write-tree'], root)
  const paths = ['core/work-finiteness.test.ts','kernel/prove.ts','scripts/test-shards.ts']
  const saved = Object.fromEntries(paths.map(path => [path, readFileSync(join(root, path), 'utf8')])), current = {...saved}
  const replace = (path: string, before: string, after: string) => { assert.equal(current[path]!.split(before).length, 2); current[path] = current[path]!.replace(before, after); writeFileSync(join(root, path), current[path]!) }
  replace(paths[1]!, '  if (budgetUnitsEnd !== undefined) {\n    const used = fullWork()\n    if (!Number.isFinite(used) || used > budgetUnitsEnd) throw new BudgetExpired(phase)\n  }', '  if (budgetUnitsEnd !== undefined && fullWork() > budgetUnitsEnd) throw new BudgetExpired(phase)')
  replace(paths[1]!, '    const previous = budgetUnitsEnd, used = fullWork()\n    const end = Math.min(previous ?? Infinity, workCap, used + units)\n    if (!Number.isFinite(used) || !Number.isFinite(end)) throw new BudgetExpired(\'entry\')\n    budgetUnitsEnd = end', '    const previous = budgetUnitsEnd\n    budgetUnitsEnd = Math.min(previous ?? Infinity, workCap, fullWork() + units)')
  rmSync(join(root, paths[0]!))
  replace(paths[2]!, 'request-materialization.test.ts work-finiteness.test.ts', 'request-materialization.test.ts')
  command('git', ['add','-A'], root)
  const parentTree = command('git', ['write-tree'], root)
  assert.equal(parentTree, '1fe9fc742ebe0c4fa25fcf60916f37c54e7ccc37', 'reversing only the three intended changes must reproduce exact 94b65671')
  for (const path of paths) writeFileSync(join(root, path), saved[path]!)
  command('git', ['add','-A'], root); assert.equal(command('git', ['write-tree'], root), tree)
  assert.deepEqual(command('git', ['diff','--cached','--name-only',parentTree], root).split('\n').sort(), paths)
  const delta = execFileSync('git', ['diff','--cached','--binary',parentTree], {cwd: root, encoding: 'utf8'})
  const patchSha256 = createHash('sha256').update(delta).digest('hex')
  console.log('NUMERIC_SOURCE_EXPORT ' + JSON.stringify({passed: true, parentSource: '94b65671', parentTree, tree, fullPatchSha256: verified.patchSha256, patchSha256, bytes: Buffer.byteLength(delta), encoding: 'gzip-base64', data: gzipSync(delta).toString('base64'), expectedCandidateBlobs: verified.expectedCandidateBlobs, admitted: false}))
} finally { rmSync(temp, {recursive: true, force: true}) }
