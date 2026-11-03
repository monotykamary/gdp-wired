// Self-owned evidence controls only. No upstream source or vulnerability is fetched.
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {check} from '../../core/cli.ts'
import {scoreRecall, type RecallSide} from './score.ts'

const family = (version: string, verdicts: string[]): RecallSide => ({version, status: 'checked', result: {rules: verdicts.map((verdict, i) => ({
  entry: 'OwnedFamily', ctor: i === 0 ? '()' : '(boolean)', ok: true,
  laws: [{name: 'only allowed changes', expr: 'value != old(value) implies allowed', verdict, run: ['hit(allowed=false)'], replayed: 'owned source replay'}],
}))}})

test('constructor family refuses a partial repair in either initializer', () => {
  const before = family('vulnerable', ['broken', 'broken'])
  for (const verdicts of [['proven', 'broken'], ['broken', 'proven'], ['unknown', 'broken']]) {
    expect(scoreRecall([before, family('fixed', verdicts)]).found).toBe(false)
  }
  expect(scoreRecall([before, family('fixed', ['proven', 'proven'])]).found).toBe(true)
  expect(scoreRecall([before, family('fixed', ['proven', 'unknown'])]).found).toBe(true)
})

test('constructor family retains every original context and the same policy in each', () => {
  const before = family('vulnerable', ['broken', 'broken'])
  const missing = family('fixed', ['proven'])
  expect(scoreRecall([before, missing]).found).toBe(false)
  const omitted = family('fixed', ['proven', 'proven'])
  omitted.result!.rules[1]!.laws = []
  expect(scoreRecall([before, omitted]).found).toBe(false)
  const drift = family('fixed', ['proven', 'proven'])
  drift.result!.rules[1]!.laws[0]!.expr = 'true'
  expect(scoreRecall([before, drift]).found).toBe(false)
  const missingBefore = family('vulnerable', ['broken', 'unknown'])
  missingBefore.result!.rules[1]!.laws = []
  expect(scoreRecall([missingBefore, family('fixed', ['proven', 'proven'])]).found).toBe(false)
})

test('constructor family checks newly added contexts without conflating unrelated entries', () => {
  const before = family('vulnerable', ['broken'])
  expect(scoreRecall([before, family('fixed', ['proven', 'broken'])]).found).toBe(false)
  expect(scoreRecall([before, family('fixed', ['proven', 'proven'])]).found).toBe(true)
  const fixed = family('fixed', ['proven'])
  fixed.result!.rules.push({...family('fixed', ['broken']).result!.rules[0]!, entry: 'Unrelated'})
  expect(scoreRecall([before, fixed]).found).toBe(true)
})

const nativeTest = ['javac', 'java'].every(tool => spawnSync(tool, ['-version'], {timeout: 5000}).status === 0) ? test : test.skip
nativeTest('owned constructor family requires a complete native repair', async () => {
  const root = mkdtempSync(join(tmpdir(), 'owned-family-'))
  const source = (first: boolean, second: boolean) => `public class OwnedFamily {
    public int value = 0;
    public boolean guarded;
    public OwnedFamily() { guarded = ${first}; }
    public OwnedFamily(boolean choice) { guarded = ${second}; }
    // gdp: law only allowed changes: value != old(value) implies allowed
    public void hit(boolean allowed) { if (guarded && !allowed) return; value++; }
  }`
  const driver = `public class ReplayFamily {
    public static void main(String[] args) {
      OwnedFamily current = args[0].equals("()") ? new OwnedFamily() : new OwnedFamily(Boolean.parseBoolean(args[1]));
      boolean broken = false;
      for (int i = 2; i < args.length; i++) {
        boolean allowed = Boolean.parseBoolean(args[i]);
        int previous = current.value;
        current.hit(allowed);
        if (current.value != previous && !allowed) broken = true;
      }
      System.out.println(broken + ":" + (args.length - 2));
    }
  }`
  const sources = [source(false, false), source(true, false), source(true, true)]
  const names = ['original', 'partial', 'complete']
  const results: Awaited<ReturnType<typeof check>>[] = []
  const controls: {version: string, ctor: string, choice: boolean | null, broken: boolean, steps: number}[] = []
  try {
    for (const [i, text] of sources.entries()) {
      const dir = join(root, names[i]!)
      mkdirSync(dir)
      const file = join(dir, 'OwnedFamily.java')
      writeFileSync(file, text); writeFileSync(join(dir, 'ReplayFamily.java'), driver)
      results.push(await check([file], {entry: 'OwnedFamily', methods: ['hit'], propose: false, ms: 3000, check: {runs: 10, depth: 6, states: 20}}))
      const compiled = spawnSync('javac', [file, join(dir, 'ReplayFamily.java')], {encoding: 'utf8', timeout: 30_000})
      expect(compiled.status, compiled.stderr).toBe(0)
    }
    expect(results.map(r => r.exit)).toEqual([1, 1, 0])
    for (const result of results) {
      expect(result.rules.map(r => r.ctor).sort((a, b) => (a ?? '').localeCompare(b ?? ''))).toEqual(['()', '(boolean)'])
      expect(result.rules.every(r => r.ok && !!r.checked)).toBe(true)
    }
    for (const rule of results[0]!.rules) {
      const law = rule.laws[0]!
      expect(law.verdict).toBe('broken')
      const lines = [...law.run!]
      const constructor = /^made with choice = (true|false)$/.exec(lines[0] ?? '')
      expect(!!constructor).toBe(rule.ctor === '(boolean)')
      if (constructor) lines.shift()
      const choice = constructor?.[1] ?? 'false'
      const args = lines.map(line => {
        const match = /^hit\(allowed=(true|false)\)$/.exec(line)
        if (!match) throw Error('owned family witness is outside the boolean hit fixture: ' + JSON.stringify(law.run))
        return match[1]!
      })
      expect(args.length).toBeGreaterThan(0)
      for (const [i, version] of names.entries()) {
        const replay = spawnSync('java', ['-cp', join(root, version), 'ReplayFamily', rule.ctor!, choice, ...args], {encoding: 'utf8', timeout: 10_000})
        expect(replay.status, replay.stderr).toBe(0)
        const [bad, steps] = replay.stdout.trim().split(':')
        expect(['true', 'false']).toContain(bad ?? '')
        expect(Number(steps)).toBe(args.length)
        const expected = i === 0 || (i === 1 && rule.ctor === '(boolean)')
        expect(bad === 'true').toBe(expected)
        controls.push({version, ctor: rule.ctor!, choice: constructor ? choice === 'true' : null, broken: bad === 'true', steps: Number(steps)})
      }
      law.replayed = 'same native witness replayed across the original, partial and complete owned family'
    }
    for (const [i, text] of sources.entries()) expect(readFileSync(join(root, names[i]!, 'OwnedFamily.java'), 'utf8')).toBe(text)
    const before: RecallSide = {version: 'vulnerable', status: 'checked', result: results[0]!}
    const after = (i: number): RecallSide => ({version: 'fixed', status: 'checked', result: results[i]!})
    const partial = scoreRecall([before, after(1)]), complete = scoreRecall([before, after(2)])
    expect(partial.found).toBe(false)
    expect(complete.found).toBe(true)
    console.log('OWNED_FAMILY_CONTROL ' + JSON.stringify({scope: 'self-owned native Java only; no upstream recall', hashes: sources.map(text => createHash('sha256').update(text).digest('hex')), controls, partialAdmitted: partial.found, completeAdmitted: complete.found}))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 120_000)
