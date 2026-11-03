import {afterEach, expect, test} from 'bun:test'
import {createHash} from 'node:crypto'
import {existsSync, mkdtempSync, mkdirSync, readFileSync, rmSync, statSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {buildInventory, csvCell, ledgerHeader, legacyInventory, parseSnapshot, repository, sentHistory, sourceInventory, writeInventory, type Snapshot} from './inventory.ts'

const sha = 'a'.repeat(40)
const row = {repo: 'Example/Widget', commit: sha, licence: 'MIT', path: 'src/state.ts', entry: 'State'}
const catalog = (rows: unknown, path = 'catalog.json') => ({path, text: JSON.stringify(rows)})
const snapshot = (): Snapshot => ({catalogs: [catalog([row])], documents: [], readerExports: ['./extract', './extract-py']})
test('CLI validates arguments, emits metadata artifacts and never executes catalog commands', () => {
  const p = root(), input = join(p, 'input.json'), script = new URL('./inventory.ts', import.meta.url).pathname
  const s = snapshot()
  s.catalogs = [catalog({...row, setup: 'touch forbidden', repro: {script: 'touch forbidden'}})]
  writeFileSync(input, JSON.stringify(s))
  const invoke = (args: string[]) => Bun.spawnSync({cmd: [process.execPath, script, ...args], cwd: p})
  expect(invoke([]).exitCode).toBe(1)
  expect(invoke(['--snapshot', input, '--out', 'outside']).exitCode).toBe(1)
  const good = invoke(['--snapshot', input, '--out', 'runs/result'])
  expect(good.exitCode).toBe(0)
  expect((JSON.parse(good.stdout.toString()) as {executedTargets: number}).executedTargets).toBe(0)
  expect(existsSync(join(p, 'forbidden'))).toBe(false)
  expect(readFileSync(join(p, 'runs/result/LEDGER.proposed.csv'), 'utf8')).toBe(ledgerHeader)
  expect(invoke(['--snapshot', input, '--out', 'runs/result']).exitCode).toBe(1)
})
const roots: string[] = []
const root = () => { const p = mkdtempSync(join(tmpdir(), 'metadata-inventory-')); roots.push(p); return p }
afterEach(() => { for (const p of roots.splice(0)) rmSync(p, {recursive: true, force: true}) })

test('repository identities accept GitHub metadata, not arbitrary remote addresses', () => {
  for (const s of ['Example/Widget', 'https://github.com/Example/Widget', 'https://github.com/Example/Widget.git/'])
    expect(repository(s)).toBe('example/widget')
  for (const s of ['https://other.test/e/w', 'git@github.com:e/w', '../widget', 'e/..', 'e/w/issues/1', 'https://github.com/e/w?x=1'])
    expect(repository(s)).toBeUndefined()
})

test('normalizes explicit metadata without executing setup, edits or repro fields', () => {
  const r = sourceInventory([catalog([{...row, setup: 'exit 99', repro: {script: 'never.py'}, edits: []}])], ['./extract']).sources[0]!
  expect(r.repo).toBe('example/widget')
  expect(r.pin).toBe('immutable')
  expect(r.readers).toEqual(['./extract'])
  expect(r.problems).toEqual([])
  expect(r.provenance[0]?.sha256).toHaveLength(64)
})

test('mutable, missing and abbreviated refs stay unresolved; tag case is preserved', () => {
  for (const commit of ['', 'abcdef0', 'ReleaseCandidate', 'main']) {
    const r = sourceInventory([catalog({...row, commit})], []).sources[0]!
    expect(r.commit).toBe(commit)
    expect(r.pin).toBe('unresolved')
    expect(r.problems).toContain('missing-or-mutable-pin')
  }
  expect(sourceInventory([catalog({...row, commit: 'A'.repeat(64)})], []).sources[0]?.pin).toBe('immutable')
})

test('deduplicates source identities but preserves every provenance and license declaration', () => {
  const {sources} = sourceInventory([catalog(row, 'a.json'), catalog({...row, license: 'Apache-2.0'}, 'b.json')], ['./extract'])
  expect(sources).toHaveLength(1)
  expect(sources[0]?.provenance).toHaveLength(2)
  expect(sources[0]?.licenses).toEqual(['Apache-2.0', 'MIT'])
  const s = snapshot(); s.catalogs = [catalog([row, {...row, license: 'Apache-2.0'}])]
  expect(buildInventory(s).summary.licenseConflictRepositories).toBe(1)
  s.catalogs = [catalog([row, {...row, commit: 'b'.repeat(40), licence: 'Apache-2.0'}])]
  expect(buildInventory(s).summary.licenseConflictRepositories).toBe(0)
})

test('handles target/check/files shapes; invalid paths and missing licenses are not hidden', () => {
  const {sources, rejected} = sourceInventory([catalog([
    {repo: row.repo, commit: sha, target: 'one.py', check: ['two.py'], files: ['three.py', '../escape', '/root/x'], lang: 'Python'},
    {repo: 'not-a-repository'},
  ])], ['./extract-py'])
  expect(rejected).toHaveLength(1)
  expect(sources[0]?.paths).toEqual(['one.py', 'three.py', 'two.py'])
  expect(sources[0]?.readers).toEqual(['./extract-py'])
  expect(sources[0]?.problems).toContain('invalid-source-path')
  expect(sources[0]?.problems).toContain('missing-declared-license')
})

test('reader hints are limited to registered exports; unknown formats stay unsupported', () => {
  const s = snapshot(); s.catalogs = [catalog([{...row, path: 'rule.cedar'}, {...row, path: 'a.rs'}])]
  expect(buildInventory(s).summary.readerHintRecords).toBe(0)
  s.readerExports.push('./extract-rs')
  expect(buildInventory(s).summary.readerHintRecords).toBe(1)
  expect(buildInventory(s).summary.newVerifiedFindings).toBe(0)
})

test('counts distinct repos, not source rows or versions, toward the inventory target', () => {
  const s = snapshot(); s.catalogs = [catalog(Array.from({length: 350}, (_, i) => ({...row, path: `src/${i}.ts`})))]
  const {summary} = buildInventory(s)
  expect(summary.sourceRecords).toBe(350)
  expect(summary.repositories).toBe(1)
  expect(summary.targetMet).toBe(false)
})

test('SENT preserves dated claims and negative notes without changing current status', () => {
  const history = sentHistory({path: 'SENT.md', text: '## widget (example/widget)\n- 2026-01-01T00:00:00Z: comment recorded\n- 2026-01-02T00:00:00Z, another historical entry\nProse 2026-01-03T00:00:00Z does not count.\nNothing was sent for another item.\n## no-send\nNot sent (skipped by the user).\n'})
  expect(history).toHaveLength(2)
  expect(history[0]?.datedEntries).toBe(2)
  expect(history[0]?.negativeNote).toBe(true)
  expect(history[1]?.datedEntries).toBe(0)
  const docs = legacyInventory([{path: 'widget.md', text: `# Verified, approved, sent\nhttps://github.com/Example/Widget/blob/${sha}/x\n`}], history)
  expect(docs[0]?.historyKeys).toEqual(['widget'])
  expect(docs[0]?.evidenceStatus).toBe('historical-unverified')
  expect(docs[0]?.currentStatus).toBe('not-assessed')
  expect(docs[0]?.mentionedRepositories).toEqual(['example/widget'])
  expect(docs[0]?.mentionedCommits).toEqual([sha])
})

test('no fuzzy document-to-finding associations or SENT authority', () => {
  const s = snapshot(); s.sent = {path: 'SENT.md', text: '## widget\n- 2026-01-01T00:00:00Z: sent\n'}
  s.documents = [{path: 'widget-issue-1.md', text: '# Widget report'}]
  const {summary, files} = buildInventory(s)
  expect(summary.unmatchedHistoryKeys).toEqual(['widget'])
  expect(summary.unmatchedLegacyDocuments).toEqual(['widget-issue-1.md'])
  expect(files['LEDGER.proposed.csv']).toBe(ledgerHeader)
  expect(summary.ledgerRows).toBe(0)
})

test('CSV quotes commas, quotes, newlines and neutralizes spreadsheet formulas', () => {
  expect(csvCell('a,"b"\nc')).toBe('"a,""b""\nc"')
  for (const value of ['=1+1', '+SUM(A1)', '-1', '@name', ' \t=cmd', '\nplain'])
    expect(csvCell(value).startsWith('"\'')).toBe(true)
  expect(csvCell('plain')).toBe('"plain"')
})

test('artifacts are deterministic and SHA256SUMS binds every output other than itself', () => {
  const a = buildInventory(snapshot()), b = buildInventory(snapshot())
  expect(a.files).toEqual(b.files)
  for (const line of a.files.SHA256SUMS!.trim().split('\n')) {
    const [digest, name] = line.split('  ')
    expect(createHash('sha256').update(a.files[name!]!).digest('hex')).toBe(digest!)
  }
})

test('snapshot validation refuses malformed documents, duplicate paths and path traversal', () => {
  expect(parseSnapshot(snapshot())).toEqual(snapshot())
  expect(parseSnapshot({...snapshot(), documents: [{path: 'notes/🚀.md', text: ''}]}).documents[0]?.path).toBe('notes/🚀.md')
  for (const x of [null, {}, {...snapshot(), readerExports: [1]}, {...snapshot(), documents: [{path: '../escape', text: ''}]}, {...snapshot(), documents: [{path: 'a\u0000b', text: ''}]},
    {...snapshot(), documents: [{path: 'catalog.json', text: ''}]}, {...snapshot(), sent: {path: '/secret', text: ''}}])
    expect(() => parseSnapshot(x)).toThrow()
})

test('output is fresh, private, under runs and does not overwrite existing evidence', () => {
  const p = root()
  expect(() => writeInventory(snapshot(), 'private/disclosure', p)).toThrow('under runs')
  writeInventory(snapshot(), 'runs/private/disclosure/result', p)
  const out = join(p, 'runs/private/disclosure/result')
  expect(statSync(out).mode & 0o777).toBe(0o700)
  expect(statSync(join(out, 'inventory.json')).mode & 0o777).toBe(0o600)
  expect(readFileSync(join(out, 'LEDGER.proposed.csv'), 'utf8')).toBe(ledgerHeader)
  expect(() => writeInventory(snapshot(), 'runs/private/disclosure/result', p)).toThrow('already exists')
  expect(() => writeInventory(snapshot(), 'runs/../../escape', p)).toThrow()
})

test('symlink output ancestors are refused and invalid input creates no result directory', () => {
  const p = root(), outside = root()
  mkdirSync(join(p, 'runs')); symlinkSync(outside, join(p, 'runs/link'))
  expect(() => writeInventory(snapshot(), 'runs/link/result', p)).toThrow('symlink')
  const s = snapshot(); s.catalogs = [catalog(null)]
  expect(() => writeInventory(s, 'runs/bad-result', p)).toThrow()
  expect(existsSync(join(p, 'runs/bad-result'))).toBe(false)
})
