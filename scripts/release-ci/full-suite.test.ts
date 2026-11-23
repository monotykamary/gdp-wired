// The in-CI full gate (publish.yml, full-suite.ts): a matrix of every suite job, and a verdict that passes only
// when each one passed at this commit in the run's first attempt, or failed exactly as known-failures.json records.
import {expect, test} from 'bun:test'
import {mkdirSync, mkdtempSync, readFileSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'
import {gate, matrix, suite, type Result} from './full-suite'
import {canonicalJobHash} from './job-hash'

const ROOT = resolve(import.meta.dir, '../..')
const COMMIT = 'a'.repeat(40)
const jobs = suite()
const policy = JSON.parse(readFileSync(join(ROOT, 'scripts/release-ci/known-failures.json'), 'utf8')) as {entries: {job: string; exitCode: number; signature: Result['signature']}[]}

function results(edit: (name: string, r: Result) => Result | undefined = (_, r) => r) {
  const dir = mkdtempSync(join(tmpdir(), 'full-suite-'))
  for (const job of jobs) {
    const r = edit(job.name, {schema: 'gdp-full-suite-result/v1', name: job.name, definitionSha256: canonicalJobHash(job), commit: COMMIT, runId: '1', runAttempt: '1', code: 0, signal: null, seconds: 1})
    if (!r) continue
    mkdirSync(join(dir, job.name))
    writeFileSync(join(dir, job.name, 'RESULT.json'), JSON.stringify(r))
  }
  return dir
}

test('the matrix has every suite job once, each on a box of its image', () => {
  const m = matrix()
  expect(m.include.map(e => e.name)).toEqual(jobs.map(j => j.name))
  for (const e of m.include) expect(e.runsOn).toMatch(/^instabox-large-snapshot-sc-[a-z0-9-]+$/)
})

test('every job passed: the gate passes', () => {
  const v = gate(results(), COMMIT, '1')
  expect(v.failed).toEqual([])
  expect(v.passed.length).toBe(jobs.length)
})

test('a known failure, exactly as recorded, is let through; the same job failing otherwise is not', () => {
  const known = policy.entries[0]!
  const asKnown = gate(results((n, r) => (n === known.job ? {...r, code: known.exitCode, signature: known.signature} : r)), COMMIT, '1')
  expect(asKnown.failed).toEqual([])
  expect(asKnown.known).toEqual([known.job])
  const otherwise = gate(results((n, r) => (n === known.job ? {...r, code: known.exitCode, signature: {failedTests: ['some.test.ts :: another test'], diagnostics: ['error: x']}} : r)), COMMIT, '1')
  expect(otherwise.failed.map(f => f.name)).toEqual([known.job])
})

test('a missing result, another commit, a retried attempt or a changed job definition: refused', () => {
  const [a, b, c, d] = jobs.map(j => j.name)
  const v = gate(results((n, r) => (n === a ? undefined : n === b ? {...r, commit: 'b'.repeat(40)} : n === c ? {...r, runAttempt: '2'} : n === d ? {...r, definitionSha256: '0'.repeat(64)} : r)), COMMIT, '1')
  expect(v.failed.map(f => f.name).sort()).toEqual([a, b, c, d].sort())
  expect(gate(results(), COMMIT, '2').failed[0]!.why).toMatch(/first attempt/)
})

test('a failure with no signature is refused, never taken as known', () => {
  const name = policy.entries[0]!.job
  const v = gate(results((n, r) => (n === name ? {...r, code: 1, signatureError: 'unrecognized fatal failure'} : r)), COMMIT, '1')
  expect(v.failed.map(f => f.name)).toEqual([name])
})
