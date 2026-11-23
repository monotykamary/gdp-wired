// The full gate (publish.yml, full-suite.ts): the batch's jobs are the suite's, each through `box`, and the verdict
// passes only when every suite job answered 0 in this strict-once batch of this tree, from the run's first attempt,
// or failed exactly as known-failures.json records.
import {expect, test} from 'bun:test'
import {readFileSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {boxCommand, judge, suite, wrapped, type Batch, type JobState, type Result} from './full-suite'
import {canonicalJobHash} from './job-hash'

const ROOT = resolve(import.meta.dir, '../..')
const jobs = suite()
const policy = JSON.parse(readFileSync(join(ROOT, 'scripts/release-ci/known-failures.json'), 'utf8')) as {entries: {job: string; exitCode: number; signature: Result['signature']}[]}
const TREE = 't'.repeat(16)

function run(o: {state?: (name: string, s: JobState) => JobState | undefined; result?: (name: string, r: Result) => Result | undefined; batch?: Partial<Batch>; tree?: string; attempt?: string} = {}) {
  const batch: Batch = {id: 'b1', tree: TREE, limits: {strictOnce: true, maxAttempts: 1}, jobs: jobs.map(wrapped), ...o.batch}
  const states = jobs.map(j => (o.state ?? ((_, s) => s))(j.name, {st: 'done', exit: 0, attempts: 1}))
  const results = new Map(jobs.map((j, i) => [j.name, (o.result ?? ((_, r) => r))(j.name, {schema: 'gdp-full-suite-result/v1', name: j.name, definitionSha256: canonicalJobHash(j), batch: 'b1', code: states[i]?.exit ?? 0, signal: null, seconds: 1, installed: true})]))
  return judge({jobs, batch, tree: o.tree ?? TREE, attempt: o.attempt ?? '1', states: i => states[i], results: n => results.get(n), policy})
}

test("the batch's jobs: every suite job once, through box, with time for the install before it", () => {
  const w = jobs.map(wrapped)
  expect(w.map(j => j.name)).toEqual(jobs.map(j => j.name))
  for (const [i, j] of jobs.entries()) {
    expect(w[i]!.cmd).toBe(boxCommand(j.name))
    expect(w[i]!.cwd).toBe('.')
    expect(w[i]!.timeout as number).toBeGreaterThan(Number(j.timeout ?? 3600))
    expect(w[i]!.image).toBe(j.image)
  }
})

test('every job answered 0: the gate passes', () => {
  const v = run()
  expect(v.failed).toEqual([])
  expect(v.passed.length).toBe(jobs.length)
})

test('a known failure, exactly as recorded, is let through; the same job failing otherwise is not', () => {
  const known = policy.entries[0]!
  const failing = (s: JobState) => ({...s, exit: known.exitCode})
  const asKnown = run({state: (n, s) => (n === known.job ? failing(s) : s), result: (n, r) => (n === known.job ? {...r, code: known.exitCode, signature: known.signature} : r)})
  expect(asKnown.failed).toEqual([])
  expect(asKnown.known).toEqual([known.job])
  const otherwise = run({state: (n, s) => (n === known.job ? failing(s) : s), result: (n, r) => (n === known.job ? {...r, code: known.exitCode, signature: {failedTests: ['some.test.ts :: another test'], diagnostics: ['error: x']}} : r)})
  expect(otherwise.failed.map(f => f.name)).toEqual([known.job])
})

test("another tree, a batch that wasn't strict-once, or a later run attempt: refused as a whole", () => {
  expect(run({tree: 'x'.repeat(16)}).failed[0]!.why).toMatch(/tree/)
  expect(run({batch: {limits: {strictOnce: false, maxAttempts: 3}}}).failed[0]!.why).toMatch(/strict-once/)
  expect(run({attempt: '2'}).failed[0]!.why).toMatch(/first attempt/)
})

test("a lost job, a job tried twice, another job in a job's place, a result from elsewhere or of another definition: refused", () => {
  const [a, b, c, d, e, f] = jobs.map(j => j.name) as [string, string, string, string, string, string]
  const v = run({
    state: (n, s) => (n === a ? {...s, st: 'lost'} : n === b ? {...s, attempts: 2} : s),
    result: (n, r) => (n === c ? undefined : n === d ? {...r, batch: 'other'} : n === e ? {...r, definitionSha256: '0'.repeat(64)} : r),
    batch: {jobs: jobs.map(j => (j.name === f ? {...wrapped(j), cmd: 'true'} : wrapped(j)))},
  })
  expect(v.failed.map(x => x.name).sort()).toEqual([a, b, c, d, e, f].sort())
})

test('a failure with no signature, or whose dependencies did not install, is refused, never taken as known', () => {
  const name = policy.entries[0]!.job
  const failing = (n: string, s: JobState) => (n === name ? {...s, exit: 1} : s)
  expect(run({state: failing, result: (n, r) => (n === name ? {...r, code: 1, signatureError: 'unrecognized fatal failure'} : r)}).failed.map(x => x.name)).toEqual([name])
  expect(run({state: failing, result: (n, r) => (n === name ? {...r, code: 1, installed: false} : r)}).failed.map(x => x.name)).toEqual([name])
})
