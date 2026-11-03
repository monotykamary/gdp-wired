import './fixed-family.test.ts'
import './policy-identity.test.ts'
import './constructor-argument.test.ts'
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {check} from '../../core/cli.ts'
import {replayClass} from './mutants/replay.ts'
import {type RecallSide, scoreRecall} from './score.ts'
const side = (version: string, verdict: string): RecallSide => ({version, status: 'checked', result: {rules: [{ok: true, entry: 'Handler', laws: [{name: 'policy', expr: 'result implies admin', verdict, run: ['run'], replayed: 'original code agrees'}]}]}})
test('recall requires the same stated policy, original replay and fixed counterpart', () => {
  const a = side('vulnerable', 'broken'), b = side('fixed', 'proven')
  expect(scoreRecall([a,b]).found).toBe(true)
  expect(scoreRecall([a,side('fixed','unknown')]).found).toBe(true)
  expect(scoreRecall([a,side('fixed','broken')]).found).toBe(false)
  expect(scoreRecall([a]).found).toBe(false)
  b.result!.rules[0]!.laws[0]!.expr = 'another policy'
  expect(scoreRecall([a,b]).found).toBe(false)
})
test('deliberate training flaws require reproduction but no fictional fixed revision', () => {
  const a = side('vulnerable', 'broken')
  expect(scoreRecall([a], true).found).toBe(true)
  expect(scoreRecall([a]).found).toBe(false)
  a.result!.rules[0]!.ok = false
  expect(scoreRecall([a], true).found).toBe(false)
})

test('refusals, absent laws and un-replayed environment schedules never count', () => {
  const a = side('vulnerable', 'broken'), b = side('fixed', 'proven')
  a.result!.rules[0]!.ok = false
  expect(scoreRecall([a,b]).found).toBe(false)
  a.result!.rules[0]!.ok = true
  delete a.result!.rules[0]!.laws[0]!.replayed
  expect(scoreRecall([a,b]).found).toBe(false)
  a.result!.rules[0]!.laws = []
  expect(scoreRecall([a,b]).found).toBe(false)
  const runtime = {version: 'vulnerable', status: 'runtime-only', accepted: true}
  expect(scoreRecall([runtime], true).found).toBe(false)
  expect(scoreRecall([runtime, {version: 'fixed', status: 'runtime-only'}]).found).toBe(false)
})

test('duplicate or unexpected revision receipts cannot inflate strict recall', () => {
  const before = side('vulnerable', 'broken'), fixed = side('fixed', 'proven')
  for (const rows of [[before, fixed, fixed], [before, before, fixed], [before, fixed, side('other', 'proven')]]) {
    expect(scoreRecall(rows).found).toBe(false)
    expect(scoreRecall([...rows].reverse()).found).toBe(false)
  }
  expect(scoreRecall([before, before], true).found).toBe(false)
})

test('failed, incomplete and unreviewable receipts never count despite surviving law data', () => {
  for (const status of ['error', 'refused', 'runtime-only', '', 'checked ']) {
    const before = side('vulnerable', 'broken'), fixed = side('fixed', 'proven')
    before.status = status
    expect(scoreRecall([before, fixed]).found).toBe(false)
    before.status = 'checked'; fixed.status = status
    expect(scoreRecall([before, fixed]).found).toBe(false)
  }
  const before = side('vulnerable', 'broken'), fixed = side('fixed', 'proven')
  fixed.result!.rules.push({ok: true, entry: 'Unread', laws: [{name: 'unread policy', expr: 'true', verdict: 'not read'}]})
  expect(scoreRecall([before, fixed]).found).toBe(false)
})

test('strict recall requires an unambiguous entry, constructor and policy match', () => {
  const before = side('vulnerable', 'broken'), fixed = side('fixed', 'proven')
  before.result!.rules[0]!.ctor = '()'; fixed.result!.rules[0]!.ctor = '(boolean)'
  expect(scoreRecall([before, fixed]).found).toBe(false)
  fixed.result!.rules[0]!.ctor = '()'
  expect(scoreRecall([before, fixed]).found).toBe(true)
  fixed.result!.rules.push({...fixed.result!.rules[0]!, laws: [{...fixed.result!.rules[0]!.laws[0]!, verdict: 'broken'}]})
  expect(scoreRecall([before, fixed]).found).toBe(false)
  fixed.result!.rules.pop()
  fixed.result!.rules[0]!.laws.push({...fixed.result!.rules[0]!.laws[0]!})
  expect(scoreRecall([before, fixed]).found).toBe(false)
})

test('blank replay, empty trace and unnamed policies are not original-code evidence', () => {
  for (const change of [
    (s: RecallSide) => { s.result!.rules[0]!.laws[0]!.replayed = '   ' },
    (s: RecallSide) => { s.result!.rules[0]!.laws[0]!.run = [''] },
    (s: RecallSide) => { s.result!.rules[0]!.laws[0]!.run = [] },
    (s: RecallSide) => { s.result!.rules[0]!.laws[0]!.name = '' },
    (s: RecallSide) => { s.result!.rules[0]!.laws[0]!.expr = ' ' },
    (s: RecallSide) => { delete s.result!.rules[0]!.entry },
  ]) {
    const before = side('vulnerable', 'broken')
    change(before)
    expect(scoreRecall([before, side('fixed', 'proven')]).found).toBe(false)
    expect(scoreRecall([before], true).found).toBe(false)
  }
})

test('owned paired source is checked and the exact witness replays before strict admission', async () => {
  const root = mkdtempSync(join(tmpdir(), 'owned-strict-recall-'))
  const original = `export class OwnedCounter {
    value = 0;
    // gdp: law only allowed calls change value: value != old(value) implies allowed
    hit(allowed: boolean): void { this.value++; }
  }`
  const repaired = original.replace('this.value++;', 'if (allowed) this.value++;')
  const beforePath = join(root, 'original.ts'), fixedPath = join(root, 'fixed.ts')
  writeFileSync(beforePath, original); writeFileSync(fixedPath, repaired)
  try {
    const options = {entry: 'OwnedCounter', propose: false, security: true, ms: 3000}
    const before = await check([beforePath], options), fixed = await check([fixedPath], options)
    expect(before.exit).toBe(1); expect(fixed.exit).toBe(0)
    expect([...before.rules, ...fixed.rules].every(r => r.ok && !!r.checked)).toBe(true)
    const broken = before.rules[0]!.laws[0]!, counterpart = fixed.rules[0]!.laws[0]!
    expect(broken.verdict).toBe('broken'); expect(counterpart.verdict).toBe('proven')
    expect(broken.run?.length).toBeGreaterThan(0)
    const sides: RecallSide[] = [{version: 'vulnerable', status: 'checked', result: before}, {version: 'fixed', status: 'checked', result: fixed}]
    expect(scoreRecall(sides).found).toBe(false) // a model witness alone is not source replay
    const replay = await replayClass(beforePath, 'OwnedCounter', broken.expr, broken.run!)
    const clean = await replayClass(fixedPath, 'OwnedCounter', broken.expr, broken.run!)
    expect(replay.ok && replay.broken && replay.steps.length > 0).toBe(true)
    expect(clean.ok && !clean.broken && clean.steps.length === replay.steps.length).toBe(true)
    const hash = (file: string) => createHash('sha256').update(readFileSync(file)).digest('hex')
    expect(readFileSync(beforePath, 'utf8')).toBe(original)
    expect(readFileSync(fixedPath, 'utf8')).toBe(repaired)
    broken.replayed = 'owned original source replayed; the same witness leaves the fixed original unrefuted'
    expect(scoreRecall(sides).found).toBe(true)
    const candidatesOnly = structuredClone(sides)
    candidatesOnly[0]!.result!.rules[0]!.laws = []
    expect(scoreRecall(candidatesOnly).found).toBe(false)
    console.log('OWNED_RECALL_CONTROL ' + JSON.stringify({scope: 'self-owned synthetic source only; not upstream recall', originalSha256: hash(beforePath), fixedSha256: hash(fixedPath), strict: {found: 1, total: 1}, fixedRefuted: 0, sourceReplays: 2, candidatesCounted: 0}))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 60_000)

const java = () => ['javac', 'java'].every(tool => spawnSync(tool, ['-version'], {timeout: 5000}).status === 0)
;(java() ? test : test.skip)('owned Java constructor contexts retain exact native replay identity', async () => {
  const root = mkdtempSync(join(tmpdir(), 'owned-constructor-recall-'))
  const original = `public class OwnedCounter {
    public int value = 0;
    public boolean guarded;
    public OwnedCounter() { guarded = false; }
    public OwnedCounter(boolean choice) { guarded = true; }
    // gdp: law only allowed calls change value: value != old(value) implies allowed
    public void hit(boolean allowed) { if (guarded && !allowed) return; value++; }
  }`
  const fixed = original.replace('guarded = false;', 'guarded = true;')
  const runner = `public class ReplayMain {
    public static void main(String[] args) {
      OwnedCounter current = args[0].equals("default") ? new OwnedCounter() : new OwnedCounter(true);
      boolean broken = false;
      for (int i = 1; i < args.length; i++) {
        boolean allowed = Boolean.parseBoolean(args[i]);
        int previous = current.value;
        current.hit(allowed);
        if (current.value != previous && !allowed) broken = true;
      }
      System.out.println(broken + ":" + current.value + ":" + (args.length - 1));
    }
  }`
  const results: Awaited<ReturnType<typeof check>>[] = [], controls: {version: string, ctor: string, broken: boolean, value: number, steps: number}[] = []
  const hashes: string[] = []
  try {
    for (const [version, source] of [['original', original], ['fixed', fixed]] as const) {
      const dir = join(root, version)
      mkdirSync(dir)
      const path = join(dir, 'OwnedCounter.java')
      writeFileSync(path, source); writeFileSync(join(dir, 'ReplayMain.java'), runner)
      results.push(await check([path], {entry: 'OwnedCounter', methods: ['hit'], propose: false, ms: 3000, check: {runs: 10, depth: 6, states: 20}}))
      const compiled = spawnSync('javac', [path, join(dir, 'ReplayMain.java')], {encoding: 'utf8', timeout: 30_000})
      expect(compiled.status, compiled.stderr).toBe(0)
      expect(readFileSync(path, 'utf8')).toBe(source)
      hashes.push(createHash('sha256').update(source).digest('hex'))
    }
    const [before, after] = results
    expect(before!.exit).toBe(1); expect(after!.exit).toBe(0)
    for (const result of results) {
      expect(result.rules.map(r => r.ctor).sort((a, b) => (a ?? '').localeCompare(b ?? ''))).toEqual(['()', '(boolean)'])
      expect(result.rules.every(r => r.ok && !!r.checked && r.entry === 'OwnedCounter')).toBe(true)
    }
    const broken = before!.rules.find(r => r.ctor === '()')!.laws[0]!
    expect(broken.verdict).toBe('broken')
    expect(before!.rules.find(r => r.ctor === '(boolean)')!.laws[0]!.verdict).toBe('proven')
    expect(after!.rules.every(r => r.laws[0]!.verdict === 'proven')).toBe(true)
    const args = broken.run!.map(line => {
      const match = /^hit\(allowed=(true|false)\)$/.exec(line)
      if (!match) throw Error('owned Java witness is outside the boolean hit fixture')
      return match[1]!
    })
    expect(args.length).toBeGreaterThan(0)
    for (const version of ['original', 'fixed']) for (const ctor of ['()', '(boolean)']) {
      const replay = spawnSync('java', ['-cp', join(root, version), 'ReplayMain', ctor === '()' ? 'default' : 'guarded', ...args], {encoding: 'utf8', timeout: 10_000})
      expect(replay.status, replay.stderr).toBe(0)
      const [bad, value, steps] = replay.stdout.trim().split(':')
      expect(['true', 'false']).toContain(bad ?? '')
      expect(Number(steps)).toBe(args.length)
      expect(bad === 'true').toBe(version === 'original' && ctor === '()')
      controls.push({version, ctor, broken: bad === 'true', value: Number(value), steps: Number(steps)})
    }
    expect(readFileSync(join(root, 'original/OwnedCounter.java'), 'utf8')).toBe(original)
    expect(readFileSync(join(root, 'fixed/OwnedCounter.java'), 'utf8')).toBe(fixed)
    const sides: RecallSide[] = [{version: 'vulnerable', status: 'checked', result: before!}, {version: 'fixed', status: 'checked', result: after!}]
    expect(scoreRecall(sides).found).toBe(false)
    broken.replayed = 'exact boolean witness replayed by javac/java on both unchanged owned originals and both constructors'
    expect(scoreRecall(sides).found).toBe(true)
    expect(scoreRecall([sides[0]!, {...sides[1]!, result: before!}]).found).toBe(false) // the other constructor was already safe
    console.log('OWNED_CONSTRUCTOR_REPLAY ' + JSON.stringify({scope: 'self-owned Java source only; not upstream recall', hashes, controls, matchingFixedAdmitted: true, unchangedOriginalAdmitted: false}))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 90_000)

type Seed = {id: string, set: string, advisory: string, repo: string, before: string, after?: string, path: string, entry: string, policy: string, fixEvidence?: string, cve?: string | null}
const seeds = JSON.parse(readFileSync(new URL('./cases.json', import.meta.url), 'utf8')) as Seed[]
test('published recall seeds are distinct pinned policy cases with explicit fixes', () => {
  const published = seeds.filter(c => c.set === 'published')
  expect(published.length).toBeGreaterThanOrEqual(18)
  expect(new Set(seeds.map(c => c.id)).size).toBe(seeds.length)
  expect(new Set(published.map(c => c.advisory)).size).toBe(published.length)
  const cves = published.flatMap(c => c.cve ? [c.cve] : [])
  expect(new Set(cves).size).toBe(cves.length)
  for (const c of seeds) {
    expect(c.id).toMatch(/^[a-z0-9-]+$/)
    expect(c.repo).toMatch(/^[\w-]+\/[\w.-]+$/)
    expect(c.before).toMatch(/^[a-f0-9]{40}$/)
    expect(c.path.startsWith('/')).toBe(false)
    expect(c.path.split('/')).not.toContain('..')
    expect(c.entry).toBeTruthy()
    expect(c.policy).toBeTruthy()
    if (c.set === 'published') {
      expect(c.advisory).toMatch(/^https:\/\/github\.com\/advisories\/GHSA-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}$/)
      expect(c.after).toMatch(/^[a-f0-9]{40}$/)
      expect(c.before).not.toBe(c.after)
      expect(c.fixEvidence).toBe(`https://github.com/${c.repo}/commit/${c.after}`)
    } else expect(c.set).toBe('training')
  }
})

test('published measurement covers both exact revisions without hiding refusals', () => {
  type Row = {id: string, set: string, found: boolean, sides: {version: string, sha: string, sourceSha256: string, status: string}[]}
  const m = JSON.parse(readFileSync(new URL('./measurement.json', import.meta.url), 'utf8')) as {rows: Row[], published: {found: number, total: number}, training: {found: number, total: number}}
  expect(m.rows.map(r => r.id)).toEqual(seeds.map(c => c.id))
  for (const c of seeds) {
    const r = m.rows.find(r => r.id === c.id)!
    expect(r.set).toBe(c.set)
    expect(r.sides.map(s => s.version)).toEqual(c.after ? ['vulnerable', 'fixed'] : ['vulnerable'])
    for (const s of r.sides) {
      expect(s.sha).toBe(s.version === 'vulnerable' ? c.before : c.after ?? '')
      expect(s.sourceSha256).toMatch(/^[a-f0-9]{64}$/)
      expect(s.status).not.toBe('error')
    }
  }
  for (const set of ['published', 'training'] as const) {
    const rows = m.rows.filter(r => r.set === set)
    expect(m[set]).toEqual({found: rows.filter(r => r.found).length, total: rows.length})
  }
})

test('Solidity harness recall preserves original pairs and reports deployment assumptions, not findings', () => {
  type Side = {version: string, sha: string, sourceSha256: string, originalUnchanged: boolean, status: string, harness: {target: {source: string, contract: string}, source: string, entry: string, constructors: string[], overrides: string[], notes: string[]}}
  type Row = {id: string, found: boolean, sides: Side[]}
  const m = JSON.parse(readFileSync(new URL('./solidity-harness-measurement.json', import.meta.url), 'utf8')) as {frontendSnapshot: string, rows: Row[], published: {found: number, total: number}, extractionCoverage: {readable: number, total: number}, sideCoverage: {readable: number, total: number}, originalsVerified: number}
  const baseline = JSON.parse(readFileSync(new URL('./measurement.json', import.meta.url), 'utf8')) as {rows: {id: string, sides: {version: string, sourceSha256: string}[]}[]}
  expect(m.frontendSnapshot).toMatch(/^[a-f0-9]{12,64}$/)
  expect(new Set(m.rows.map(r => r.id)).size).toBe(6)
  for (const r of m.rows) {
    const c = seeds.find(c => c.id === r.id)!
    expect(c.set).toBe('published')
    expect(r.found).toBe(false)
    expect(r.sides.map(s => s.version)).toEqual(['vulnerable', 'fixed'])
    for (const s of r.sides) {
      expect(s.sha).toBe(s.version === 'vulnerable' ? c.before : c.after!)
      expect(s.sourceSha256).toBe(baseline.rows.find(b => b.id === r.id)!.sides.find(b => b.version === s.version)!.sourceSha256)
      expect(s.originalUnchanged).toBe(true)
      expect(['refused', 'needs-reviewed-policy-and-original-replay']).toContain(s.status)
      expect(s.harness.target).toEqual({source: c.path, contract: c.entry})
      expect(s.harness.source).toBeTruthy()
      expect(s.harness.entry).toBeTruthy()
      expect(s.harness.notes.join('\n')).toContain('not every possible subclass')
      expect(Array.isArray(s.harness.constructors)).toBe(true)
      expect(Array.isArray(s.harness.overrides)).toBe(true)
    }
  }
  const readable = (s: Side) => s.status === 'needs-reviewed-policy-and-original-replay'
  expect(m.published).toEqual({found: 0, total: m.rows.length})
  expect(m.extractionCoverage).toEqual({readable: m.rows.filter(r => r.sides.every(readable)).length, total: m.rows.length})
  expect(m.sideCoverage).toEqual({readable: m.rows.flatMap(r => r.sides).filter(readable).length, total: 2 * m.rows.length})
  expect(m.originalsVerified).toBe(2 * m.rows.length)
})
