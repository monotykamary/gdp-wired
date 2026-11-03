// Source controls written for this test; no upstream source or live targets.
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {check} from '../../core/cli.ts'
import {scoreRecall, type RecallSide} from './score.ts'

const nativeTest = ['javac', 'java'].every(tool => spawnSync(tool, ['-version'], {timeout: 5000}).status === 0) ? test : test.skip
nativeTest('owned source policy identity cannot be renamed or weakened into a repair', async () => {
  const root = mkdtempSync(join(tmpdir(), 'owned-policy-identity-'))
  const name = 'only allowed changes', expr = 'value != old(value) implies allowed'
  const variants = [
    {id: 'original', name, expr, guarded: false},
    {id: 'renamed', name: 'renamed allowed changes', expr, guarded: true},
    {id: 'weakened', name, expr: 'true', guarded: false},
    {id: 'repaired', name, expr, guarded: true},
  ]
  const sources = variants.map(v => `public class OwnedPolicy {
    public int value = 0;
    public boolean guarded;
    public OwnedPolicy() { guarded = ${v.guarded}; }
    // gdp: law ${v.name}: ${v.expr}
    public void hit(boolean allowed) { if (guarded && !allowed) return; value++; }
  }`)
  const driver = `public class ReplayPolicy {
    public static void main(String[] args) {
      OwnedPolicy current = new OwnedPolicy();
      boolean brokenOriginalContract = false;
      for (String arg : args) {
        boolean allowed = Boolean.parseBoolean(arg);
        int previous = current.value;
        current.hit(allowed);
        if (current.value != previous && !allowed) brokenOriginalContract = true;
      }
      System.out.println(brokenOriginalContract + ":" + args.length);
    }
  }`
  const results: Awaited<ReturnType<typeof check>>[] = []
  const controls: {variant: string, originalContractBroken: boolean, steps: number}[] = []
  try {
    // Name-only drift differs from the real repair only by its annotation; weakening
    // differs from the broken original only by its annotation, not executable code.
    expect(sources[1]!.replace('renamed allowed changes', name)).toBe(sources[3]!)
    expect(sources[2]!.replace(`// gdp: law ${name}: true`, `// gdp: law ${name}: ${expr}`)).toBe(sources[0]!)
    for (const [i, variant] of variants.entries()) {
      const dir = join(root, variant.id)
      mkdirSync(dir)
      const file = join(dir, 'OwnedPolicy.java')
      writeFileSync(file, sources[i]!); writeFileSync(join(dir, 'ReplayPolicy.java'), driver)
      results.push(await check([file], {entry: 'OwnedPolicy', methods: ['hit'], propose: false, ms: 3000, check: {runs: 10, depth: 6, states: 20}}))
      const compiled = spawnSync('javac', [file, join(dir, 'ReplayPolicy.java')], {encoding: 'utf8', timeout: 30_000})
      expect(compiled.status, compiled.stderr).toBe(0)
      const result = results[i]!
      expect(result.rules).toHaveLength(1)
      const rule = result.rules[0]!
      expect(rule.entry).toBe('OwnedPolicy')
      expect(rule.ctor).toBeUndefined() // singleton entries have no overload selector
      expect(rule.ok && !!rule.checked).toBe(true)
      expect(rule.laws).toHaveLength(1)
      expect(rule.laws[0]!.name).toBe(variant.name)
      expect(rule.laws[0]!.expr).toBe(variant.expr)
      expect(rule.laws[0]!.verdict).toBe(i === 0 ? 'broken' : 'proven')
    }
    expect(results.map(r => r.exit)).toEqual([1, 0, 0, 0])
    const before: RecallSide = {version: 'vulnerable', status: 'checked', result: results[0]!}
    const after = (i: number): RecallSide => ({version: 'fixed', status: 'checked', result: results[i]!})
    expect(scoreRecall([before, after(3)]).found).toBe(false) // native original replay is still missing
    const original = results[0]!.rules[0]!.laws[0]!
    const args = original.run!.map(line => {
      const call = /^hit\(allowed=(true|false)\)$/.exec(line)
      if (!call) throw Error('owned policy witness is outside the boolean fixture: ' + JSON.stringify(original.run))
      return call[1]!
    })
    expect(args.length).toBeGreaterThan(0)
    for (const [i, variant] of variants.entries()) {
      const native = spawnSync('java', ['-cp', join(root, variant.id), 'ReplayPolicy', ...args], {encoding: 'utf8', timeout: 10_000})
      expect(native.status, native.stderr).toBe(0)
      const [bad, steps] = native.stdout.trim().split(':')
      expect(['true', 'false']).toContain(bad ?? '')
      expect(Number(steps)).toBe(args.length)
      expect(bad === 'true').toBe(!variant.guarded)
      controls.push({variant: variant.id, originalContractBroken: bad === 'true', steps: Number(steps)})
      expect(readFileSync(join(root, variant.id, 'OwnedPolicy.java'), 'utf8')).toBe(sources[i]!)
    }
    original.replayed = 'exact original witness replayed on four unchanged owned sources under the original contract'
    const admissions = variants.slice(1).map((v, i) => ({variant: v.id, found: scoreRecall([before, after(i + 1)]).found}))
    expect(admissions).toEqual([{variant: 'renamed', found: false}, {variant: 'weakened', found: false}, {variant: 'repaired', found: true}])
    console.log('OWNED_POLICY_IDENTITY ' + JSON.stringify({scope: 'self-owned native Java only; no upstream recall', hashes: sources.map(text => createHash('sha256').update(text).digest('hex')), policies: variants.map((v, i) => ({variant: v.id, name: v.name, expr: v.expr, verdict: results[i]!.rules[0]!.laws[0]!.verdict})), witness: original.run, controls, admissions}))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 120_000)
