// Receipt controls only: no upstream imports, vulnerable source or network.
import {expect, test} from 'bun:test'
import {mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {spawnSync} from 'node:child_process'
import {gzipSync} from 'node:zlib'

type Target = {id: string, revision: string, path: string, entry: string, methods?: string[]}
type Case = {id: string, fixed: {revision: string, sources: {path: string, sha256: string}[]}}
const catalog = (JSON.parse(readFileSync(new URL('./fixed-library-catalog.json', import.meta.url), 'utf8')) as {rows: Case[]}).rows
const targets = (JSON.parse(readFileSync(new URL('./fixed-library-policies.json', import.meta.url), 'utf8')) as {cases: Target[]}).cases
const receipt = (c: Case) => ({id: c.id, target: {...targets.find(t => t.id === c.id)!}, revision: c.fixed.revision, version: 'fixed', mode: 'fixed-reader-only',
  policyProof: 'not-run', vulnerableReplay: 'not-run', strictRecall: null, options: {check: true, failures: 'kept', propose: false, security: false, lawFiles: []},
  status: 'reader-refused', integrityBefore: true, integrityAfter: true, sourceHashes: c.fixed.sources.map(s => ({...s})),
  rules: [{ok: false, checked: '', refusals: [{where: 'fixture', what: 'unsupported'}], notes: []}]})
type Receipt = ReturnType<typeof receipt>
function collect(mutate?: (rs: Receipt[]) => void, duplicate = false) {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-fixed-receipts-'))
  try {
    const logs = join(dir, 'logs'), out = join(dir, 'out')
    mkdirSync(logs)
    const rows = catalog.map(receipt)
    mutate?.(rows)
    rows.forEach((r, i) => writeFileSync(join(logs, `${i}.log`), JSON.stringify({encoding: 'base64+gzip', data: gzipSync(JSON.stringify(r)).toString('base64')}) + '\n'))
    if (duplicate) writeFileSync(join(logs, 'duplicate.log'), readFileSync(join(logs, '0.log')))
    const p = spawnSync(process.execPath, [new URL('./collect-fixed-evaluation.ts', import.meta.url).pathname, '--frontend-revision', 'a'.repeat(40), '--out', out, logs], {encoding: 'utf8'})
    return {code: p.status, output: p.stdout + p.stderr, report: p.status === 0 ? JSON.parse(readFileSync(join(out, 'fixed-library-reader-results.json'), 'utf8')) as {summary: {cases: number, refused: number, readAndChecked: number, strictRecall: null}} : undefined}
  } finally { rmSync(dir, {recursive: true, force: true}) }
}

test('fixed reader catalog and targets bind all 16 entries and 25 exact source pins', () => {
  expect(catalog.length).toBe(16)
  expect(catalog.flatMap(c => c.fixed.sources).length).toBe(25)
  expect(new Set(catalog.map(c => c.id)).size).toBe(16)
  expect(new Set(targets.map(t => t.id))).toEqual(new Set(catalog.map(c => c.id)))
  for (const c of catalog) {
    const target = targets.find(t => t.id === c.id)!
    expect(c.fixed.revision).toMatch(/^[a-f0-9]{40}$/)
    expect(target.revision).toBe(c.fixed.revision)
    expect(c.fixed.sources.map(s => s.path)).toContain(target.path)
    for (const s of c.fixed.sources) {
      expect(s.path.startsWith('/')).toBe(false)
      expect(s.path.split('/')).not.toContain('..')
      expect(s.sha256).toMatch(/^[a-f0-9]{64}$/)
    }
  }
})
test('fixed-only refusal receipts never become a recall result', () => {
  const x = collect()
  expect(x.code).toBe(0)
  expect(x.report!.summary).toMatchObject({cases: 16, refused: 16, readAndChecked: 0, strictRecall: null})
})
for (const [name, mutate] of [
  ['target', (r: Receipt) => { r.target.entry = 'different' }],
  ['revision', (r: Receipt) => { r.revision = 'b'.repeat(40) }],
  ['source bytes', (r: Receipt) => { r.sourceHashes[0]!.sha256 = 'b'.repeat(64) }],
  ['integrity', (r: Receipt) => { r.integrityAfter = false }],
  ['conformance', (r: Receipt) => { r.status = 'read-and-conformance-checked'; r.rules[0]!.ok = true }],
  ['policy execution', (r: Receipt) => { r.options.security = true }],
  ['disabled conformance', (r: Receipt) => { r.options.check = false }],
  ['failure model', (r: Receipt) => { r.options.failures = 'discarded' }],
] as const) {
  test(`collector rejects mismatched ${name}`, () => { expect(collect(rs => mutate(rs[0]!)).code).not.toBe(0) })
}
test('collector rejects a missing or duplicated cohort entry', () => {
  expect(collect(rs => { rs.pop() }).code).not.toBe(0)
  expect(collect(undefined, true).code).not.toBe(0)
})
test('an evaluation error is reported but fails the evidence gate', () => {
  expect(collect(rs => { rs[0]!.status = 'evaluation-error' }).code).not.toBe(0)
})
