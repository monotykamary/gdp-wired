// Validate the complete historical bootstrap before submitting any measured cohorts.
import {readFileSync, mkdtempSync, rmSync} from 'node:fs'
import {resolve, join} from 'node:path'
import {tmpdir} from 'node:os'
import {createHash} from 'node:crypto'

const expected: Record<string, string> = JSON.parse(readFileSync('frozen-bisect/checksums.json', 'utf8'))
for (const [path, hash] of Object.entries(expected)) {
  const actual = createHash('sha256').update(readFileSync(path)).digest('hex')
  if (actual !== hash) throw new Error('bootstrap hash mismatch: ' + path)
}
const {restore, command, harnessHashes} = await import(resolve('research/verify-all/final-gate-common.ts'))
const input = resolve('bisect-input')
const {baseline} = JSON.parse(readFileSync(join(input, 'gate.json'), 'utf8'))
const revisions: string[] = JSON.parse(readFileSync('regression-driver/cohort-points-wave2.json', 'utf8'))
const manifest = JSON.parse(readFileSync(join(input, 'manifest.json'), 'utf8'))
for (const revision of [baseline, ...revisions]) {
  if (!manifest.revisions[revision]) throw new Error('missing frozen revision: ' + revision)
}
const build = await Bun.build({entrypoints: [resolve('regression-driver/merge-bisect-cohort.ts')], target: 'bun'})
if (!build.success) throw new Error('cohort import graph does not build: ' + String(build.logs))
const temp = mkdtempSync(join(tmpdir(), 'lane-i-bootstrap-check-'))
try {
  for (const [index, revision] of [baseline, revisions.at(-1)!].entries()) {
    const dest = join(temp, String(index))
    const meta = restore(input, dest, revision)
    command('bun', ['install', '--frozen-lockfile'], dest)
    const source = readFileSync(join(dest, 'core/counts.ts'), 'utf8')
    if (source.split('return {traced, get counted()').length !== 2) throw new Error('trace anchor mismatch')
    console.log('BOOTSTRAP_RESTORE ' + JSON.stringify({meta, hashes: harnessHashes(dest)}))
  }
} finally {
  rmSync(temp, {recursive: true, force: true})
}
console.log('BOOTSTRAP_CHECK_PASS ' + JSON.stringify({hashedFiles: Object.keys(expected).length, revisions: revisions.length + 1, restored: 2, measuredPairs: 0}))
