// Source controls written for this test; no upstream source or live targets.
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {check} from '../../core/cli.ts'
import {scoreRecall, type RecallSide} from './score.ts'

// Extraction replay remains useful, but Java has no enabled native source-law journal.
const sourceUnknown = (law: Awaited<ReturnType<typeof check>>['rules'][number]['laws'][number], kernelProven?: boolean) => {
  expect(law).toMatchObject({verdict: 'unknown', translation: 'unchecked', ...(kernelProven === undefined ? {} : {kernelProven})})
  expect(law.run).toBeUndefined()
  expect(law.replayed).toBeUndefined()
  expect(law.cert).toBeUndefined()
}


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
      sourceUnknown(rule.laws[0]!, i !== 0)
    }
    expect(results.map(r => r.exit)).toEqual([2, 2, 2, 2])
    const before: RecallSide = {version: 'vulnerable', status: 'checked', result: results[0]!}
    const after = (i: number): RecallSide => ({version: 'fixed', status: 'checked', result: results[i]!})
    expect(scoreRecall([before, after(3)]).found).toBe(false) // native original replay is still missing
    const original = results[0]!.rules[0]!.laws[0]!
    // Authored native control; the source verdict supplies no witness or finding.
    const witness = ['hit(allowed=false)']
    const args = witness.map(line => {
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
    sourceUnknown(original, false)
    const admissions = variants.slice(1).map((v, i) => ({variant: v.id, found: scoreRecall([before, after(i + 1)]).found}))
    expect(admissions).toEqual([{variant: 'renamed', found: false}, {variant: 'weakened', found: false}, {variant: 'repaired', found: false}])
    console.log('OWNED_POLICY_IDENTITY ' + JSON.stringify({scope: 'self-owned native Java only; no upstream recall', hashes: sources.map(text => createHash('sha256').update(text).digest('hex')), policies: variants.map((v, i) => ({variant: v.id, name: v.name, expr: v.expr, verdict: results[i]!.rules[0]!.laws[0]!.verdict})), witness, controls, admissions}))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 120_000)

nativeTest('owned duplicate policy declarations remain ambiguous in either order', async () => {
  const root = mkdtempSync(join(tmpdir(), 'owned-duplicate-policies-'))
  const name = 'only allowed changes', expr = 'value != old(value) implies allowed'
  const variants = [
    {id: 'original', guarded: false, policies: [expr]},
    {id: 'repaired', guarded: true, policies: [expr]},
    {id: 'duplicate-fixed', guarded: true, policies: [expr, expr]},
    {id: 'conflicting-fixed', guarded: true, policies: [expr, 'true']},
    {id: 'reordered-fixed', guarded: true, policies: ['true', expr]},
    {id: 'conflicting-original', guarded: false, policies: [expr, 'true']},
  ]
  const sources = variants.map(v => `public class OwnedDuplicate {
    public int value = 0;
    public boolean guarded;
    public OwnedDuplicate() { guarded = ${v.guarded}; }
    ${v.policies.map(p => `// gdp: law ${name}: ${p}`).join('\n    ')}
    public void hit(boolean allowed) { if (guarded && !allowed) return; value++; }
  }`)
  const driver = `public class ReplayDuplicate {
    public static void main(String[] args) {
      OwnedDuplicate current = new OwnedDuplicate();
      boolean broken = false;
      for (String arg : args) {
        boolean allowed = Boolean.parseBoolean(arg);
        int previous = current.value;
        current.hit(allowed);
        if (current.value != previous && !allowed) broken = true;
      }
      System.out.println(broken + ":" + args.length);
    }
  }`
  const body = (text: string) => text.split('\n').filter(line => !line.trimStart().startsWith('// gdp: law ')).join('\n')
  const results: Awaited<ReturnType<typeof check>>[] = []
  const controls: {variant: string, broken: boolean, steps: number}[] = []
  try {
    for (let i = 2; i < sources.length; i++) expect(body(sources[i]!)).toBe(body(sources[i === 5 ? 0 : 1]!))
    for (const [i, variant] of variants.entries()) {
      const dir = join(root, variant.id)
      mkdirSync(dir)
      const file = join(dir, 'OwnedDuplicate.java')
      writeFileSync(file, sources[i]!); writeFileSync(join(dir, 'ReplayDuplicate.java'), driver)
      results.push(await check([file], {entry: 'OwnedDuplicate', methods: ['hit'], propose: false, ms: 3000, check: {runs: 10, depth: 6, states: 20}}))
      const compiled = spawnSync('javac', [file, join(dir, 'ReplayDuplicate.java')], {encoding: 'utf8', timeout: 30_000})
      expect(compiled.status, compiled.stderr).toBe(0)
      const result = results[i]!
      expect(result.rules).toHaveLength(1)
      const rule = result.rules[0]!
      expect(rule.entry).toBe('OwnedDuplicate')
      expect(rule.ctor).toBeUndefined()
      expect(rule.ok && !!rule.checked).toBe(true)
      expect(rule.laws.map(l => l.name)).toEqual(variant.policies.map(() => name))
      expect(rule.laws.map(l => l.expr)).toEqual(variant.policies)
      if (i < 2) {
        sourceUnknown(rule.laws[0]!, i !== 0)
      } else {
        expect(result.exit).not.toBe(0)
        expect(rule.laws.every(l => l.verdict === 'not read' && l.why?.includes('a law of this name is stated twice'))).toBe(true)
      }
    }
    const original = results[0]!.rules[0]!.laws[0]!
    // Authored native control; the source verdict supplies no witness or finding.
    const witness = ['hit(allowed=false)']
    const args = witness.map(line => {
      const call = /^hit\(allowed=(true|false)\)$/.exec(line)
      if (!call) throw Error('owned duplicate-policy witness is outside the boolean fixture: ' + JSON.stringify(original.run))
      return call[1]!
    })
    expect(args.length).toBeGreaterThan(0)
    for (const [i, variant] of variants.entries()) {
      const native = spawnSync('java', ['-cp', join(root, variant.id), 'ReplayDuplicate', ...args], {encoding: 'utf8', timeout: 10_000})
      expect(native.status, native.stderr).toBe(0)
      const [bad, steps] = native.stdout.trim().split(':')
      expect(['true', 'false']).toContain(bad ?? '')
      expect(Number(steps)).toBe(args.length)
      expect(bad === 'true').toBe(!variant.guarded)
      controls.push({variant: variant.id, broken: bad === 'true', steps: Number(steps)})
      expect(readFileSync(join(root, variant.id, 'OwnedDuplicate.java'), 'utf8')).toBe(sources[i]!)
    }
    sourceUnknown(original, false)
    const side = (version: string, i: number): RecallSide => ({version, status: 'checked', result: results[i]!})
    expect(scoreRecall([side('vulnerable', 0), side('fixed', 1)]).found).toBe(false)
    const admissions = [2, 3, 4].map(i => ({variant: variants[i]!.id, ...scoreRecall([side('vulnerable', 0), side('fixed', i)])}))
    admissions.push({variant: variants[5]!.id, ...scoreRecall([side('vulnerable', 5), side('fixed', 1)])})
    for (const admitted of admissions) {
      expect(admitted.found).toBe(false)
      expect(admitted.reason).toContain('ambiguous')
    }
    console.log('OWNED_DUPLICATE_POLICIES ' + JSON.stringify({scope: 'self-owned native Java only; no upstream recall', hashes: sources.map(text => createHash('sha256').update(text).digest('hex')), policies: variants.map((v, i) => ({variant: v.id, declarations: results[i]!.rules[0]!.laws.map(l => ({name: l.name, expr: l.expr, verdict: l.verdict, why: l.why}))})), witness, controls, admissions}))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 120_000)
