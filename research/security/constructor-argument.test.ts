// A finite owned constructor-argument contrast, not a general replay guarantee.
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
nativeTest('owned boolean constructor argument changes the native witness outcome', async () => {
  const root = mkdtempSync(join(tmpdir(), 'owned-boolean-argument-'))
  const source = (repaired: boolean) => `public class OwnedArgument {
    public int value = 0;
    public boolean guarded;
    public OwnedArgument(boolean enforce) { guarded = ${repaired ? 'true' : 'enforce'}; }
    // gdp: law only allowed changes: value != old(value) implies allowed
    public void hit(boolean allowed) { if (guarded && !allowed) return; value++; }
  }`
  const driver = `public class ReplayArgument {
    public static void main(String[] args) {
      OwnedArgument current = new OwnedArgument(Boolean.parseBoolean(args[0]));
      boolean initialGuarded = current.guarded;
      boolean broken = false;
      for (int i = 1; i < args.length; i++) {
        boolean allowed = Boolean.parseBoolean(args[i]);
        int previous = current.value;
        current.hit(allowed);
        if (current.value != previous && !allowed) broken = true;
      }
      System.out.println(initialGuarded + ":" + broken + ":" + current.value + ":" + (args.length - 1));
    }
  }`
  const sources = [source(false), source(true)], versions = ['original', 'repaired']
  const hashes = sources.map(text => createHash('sha256').update(text).digest('hex'))
  const results: Awaited<ReturnType<typeof check>>[] = []
  const controls: {version: string, scenario: string, argument: string, calls: string[], initialGuarded: boolean, broken: boolean, value: number, steps: number, sourceSha256: string}[] = []
  try {
    for (const [i, version] of versions.entries()) {
      const dir = join(root, version)
      mkdirSync(dir)
      const file = join(dir, 'OwnedArgument.java')
      writeFileSync(file, sources[i]!); writeFileSync(join(dir, 'ReplayArgument.java'), driver)
      results.push(await check([file], {entry: 'OwnedArgument', methods: ['hit'], propose: false, ms: 3000, check: {runs: 10, depth: 6, states: 20}}))
      const compiled = spawnSync('javac', [file, join(dir, 'ReplayArgument.java')], {encoding: 'utf8', timeout: 30_000})
      expect(compiled.status, compiled.stderr).toBe(0)
      const rule = results[i]!.rules[0]!
      expect(results[i]!.rules).toHaveLength(1)
      expect(rule.entry).toBe('OwnedArgument')
      expect(rule.ctor).toBeUndefined()
      expect(rule.ok && !!rule.checked).toBe(true)
      expect(rule.laws).toHaveLength(1)
      sourceUnknown(rule.laws[0]!, i !== 0)
      expect(results[i]!.exit).toBe(2)
    }
    const side = (version: string, i: number): RecallSide => ({version, status: 'checked', result: results[i]!})
    expect(scoreRecall([side('vulnerable', 0), side('fixed', 1)]).found).toBe(false)
    // Authored native constructor/call control, not a source finding.
    const law = results[0]!.rules[0]!.laws[0]!, witness = ['made with enforce = false', 'hit(allowed=false)']
    const init = /^made with enforce = (true|false)$/.exec(witness[0] ?? '')
    expect(init).not.toBeNull()
    expect(init![1]).toBe('false')
    const calls = witness.slice(1).map(line => {
      const call = /^hit\(allowed=(true|false)\)$/.exec(line)
      if (!call) throw Error('owned argument witness is outside the boolean fixture: ' + JSON.stringify(witness))
      return call[1]!
    })
    expect(calls.length).toBeGreaterThan(0)
    expect(calls).toContain('false')
    const scenarios = [{kind: 'exact', argument: init![1]!}, {kind: 'flipped', argument: init![1] === 'true' ? 'false' : 'true'}]
    const flippedWitness = [`made with enforce = ${scenarios[1]!.argument}`, ...witness.slice(1)]
    expect(flippedWitness.slice(1)).toEqual(witness.slice(1))
    for (const [i, version] of versions.entries()) for (const scenario of scenarios) {
      const native = spawnSync('java', ['-cp', join(root, version), 'ReplayArgument', scenario.argument, ...calls], {encoding: 'utf8', timeout: 10_000})
      expect(native.status, native.stderr).toBe(0)
      const [guarded, bad, value, steps] = native.stdout.trim().split(':')
      expect(['true', 'false']).toContain(guarded ?? '')
      expect(['true', 'false']).toContain(bad ?? '')
      const expectedGuard = i === 1 || scenario.argument === 'true'
      expect(guarded === 'true').toBe(expectedGuard)
      expect(bad === 'true').toBe(!expectedGuard)
      expect(Number(value)).toBe(calls.filter(call => !expectedGuard || call === 'true').length)
      expect(Number(steps)).toBe(calls.length)
      const bytes = readFileSync(join(root, version, 'OwnedArgument.java'), 'utf8')
      expect(bytes).toBe(sources[i]!)
      const sourceSha256 = createHash('sha256').update(bytes).digest('hex')
      expect(sourceSha256).toBe(hashes[i]!)
      controls.push({version, scenario: scenario.kind, argument: scenario.argument, calls, initialGuarded: guarded === 'true', broken: bad === 'true', value: Number(value), steps: Number(steps), sourceSha256})
    }
    expect(controls[0]!.broken).toBe(true)
    expect(controls[1]!.broken).toBe(false)
    expect(controls[0]!.calls).toEqual(controls[1]!.calls)
    expect(controls[0]!.sourceSha256).toBe(controls[1]!.sourceSha256)
    sourceUnknown(law, false)
    const repaired = scoreRecall([side('vulnerable', 0), side('fixed', 1)])
    const unchanged = scoreRecall([side('vulnerable', 0), side('fixed', 0)])
    expect(repaired.found).toBe(false)
    expect(unchanged.found).toBe(false) // a safe alternate argument is not a repaired source
    console.log('OWNED_BOOLEAN_ARGUMENT ' + JSON.stringify({scope: 'finite owned boolean-argument contrast only; no general forwarding or upstream recall guarantee', hashes, witness, flippedWitness, controls, repairedAdmitted: repaired.found, unchangedAdmitted: unchanged.found}))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 120_000)

nativeTest('owned same-type constructor arguments require their original positions', async () => {
  const root = mkdtempSync(join(tmpdir(), 'owned-argument-order-'))
  const source = (repaired: boolean) => `public class OwnedPair {
    public int value = 0;
    public boolean guarded;
    public OwnedPair(boolean permit, boolean deny) { guarded = ${repaired ? 'true' : 'permit || !deny'}; }
    // gdp: law only allowed changes: value != old(value) implies allowed
    public void hit(boolean allowed) { if (guarded && !allowed) return; value++; }
  }`
  const driver = `public class ReplayPair {
    public static void main(String[] args) {
      OwnedPair current = new OwnedPair(Boolean.parseBoolean(args[0]), Boolean.parseBoolean(args[1]));
      boolean initialGuarded = current.guarded;
      boolean broken = false;
      for (int i = 2; i < args.length; i++) {
        boolean allowed = Boolean.parseBoolean(args[i]);
        int previous = current.value;
        current.hit(allowed);
        if (current.value != previous && !allowed) broken = true;
      }
      System.out.println(initialGuarded + ":" + broken + ":" + current.value + ":" + (args.length - 2));
    }
  }`
  const sources = [source(false), source(true)], versions = ['original', 'repaired']
  const hashes = sources.map(text => createHash('sha256').update(text).digest('hex'))
  const results: Awaited<ReturnType<typeof check>>[] = []
  const controls: {version: string, scenario: string, arguments: string[], calls: string[], initialGuarded: boolean, broken: boolean, value: number, steps: number, sourceSha256: string}[] = []
  try {
    for (const [i, version] of versions.entries()) {
      const dir = join(root, version)
      mkdirSync(dir)
      const file = join(dir, 'OwnedPair.java')
      writeFileSync(file, sources[i]!); writeFileSync(join(dir, 'ReplayPair.java'), driver)
      results.push(await check([file], {entry: 'OwnedPair', methods: ['hit'], propose: false, ms: 3000, check: {runs: 10, depth: 6, states: 20}}))
      const compiled = spawnSync('javac', [file, join(dir, 'ReplayPair.java')], {encoding: 'utf8', timeout: 30_000})
      expect(compiled.status, compiled.stderr).toBe(0)
      expect(results[i]!.rules).toHaveLength(1)
      const rule = results[i]!.rules[0]!
      expect(rule.entry).toBe('OwnedPair')
      expect(rule.ctor).toBeUndefined()
      expect(rule.ok && !!rule.checked).toBe(true)
      expect(rule.laws).toHaveLength(1)
      sourceUnknown(rule.laws[0]!, i !== 0)
      expect(results[i]!.exit).toBe(2)
    }
    // Authored native argument-order control, not a source finding.
    const law = results[0]!.rules[0]!.laws[0]!, witness = ['made with permit = false, deny = true', 'hit(allowed=false)']
    const init = /^made with (.+)$/.exec(witness[0] ?? '')
    expect(init).not.toBeNull()
    const named = new Map<string, string>()
    for (const field of init![1]!.split(', ')) {
      const match = /^(permit|deny) = (true|false)$/.exec(field)
      if (!match || named.has(match[1]!)) throw Error('invalid owned constructor binding: ' + field)
      named.set(match[1]!, match[2]!)
    }
    expect([...named.keys()].sort((a, b) => a.localeCompare(b))).toEqual(['deny', 'permit'])
    const exact: [string, string] = [named.get('permit')!, named.get('deny')!]
    expect(exact).toEqual(['false', 'true'])
    const calls = witness.slice(1).map(line => {
      const call = /^hit\(allowed=(true|false)\)$/.exec(line)
      if (!call) throw Error('owned pair witness is outside the boolean fixture: ' + JSON.stringify(witness))
      return call[1]!
    })
    expect(calls.length).toBeGreaterThan(0)
    expect(calls).toContain('false')
    const flip = (value: string) => value === 'true' ? 'false' : 'true'
    const scenarios: {kind: string, args: [string, string]}[] = [
      {kind: 'exact', args: exact},
      {kind: 'swapped', args: [exact[1], exact[0]]},
      {kind: 'permit-only-flip', args: [flip(exact[0]), exact[1]]},
      {kind: 'deny-only-flip', args: [exact[0], flip(exact[1])]},
    ]
    for (const [i, version] of versions.entries()) for (const scenario of scenarios) {
      const native = spawnSync('java', ['-cp', join(root, version), 'ReplayPair', ...scenario.args, ...calls], {encoding: 'utf8', timeout: 10_000})
      expect(native.status, native.stderr).toBe(0)
      const [guarded, bad, value, steps] = native.stdout.trim().split(':')
      expect(['true', 'false']).toContain(guarded ?? '')
      expect(['true', 'false']).toContain(bad ?? '')
      const expectedGuard = i === 1 || scenario.args[0] === 'true' || scenario.args[1] === 'false'
      expect(guarded === 'true').toBe(expectedGuard)
      expect(bad === 'true').toBe(!expectedGuard)
      expect(Number(value)).toBe(calls.filter(call => !expectedGuard || call === 'true').length)
      expect(Number(steps)).toBe(calls.length)
      const bytes = readFileSync(join(root, version, 'OwnedPair.java'), 'utf8')
      expect(bytes).toBe(sources[i]!)
      const sourceSha256 = createHash('sha256').update(bytes).digest('hex')
      expect(sourceSha256).toBe(hashes[i]!)
      controls.push({version, scenario: scenario.kind, arguments: scenario.args, calls, initialGuarded: guarded === 'true', broken: bad === 'true', value: Number(value), steps: Number(steps), sourceSha256})
    }
    const originals = controls.filter(c => c.version === 'original')
    expect(originals.map(c => c.broken)).toEqual([true, false, false, false])
    for (const control of originals) {
      expect(control.calls).toEqual(calls)
      expect(control.sourceSha256).toBe(hashes[0]!)
    }
    sourceUnknown(law, false)
    const side = (version: string, i: number): RecallSide => ({version, status: 'checked', result: results[i]!})
    expect(scoreRecall([side('vulnerable', 0), side('fixed', 1)]).found).toBe(false)
    expect(scoreRecall([side('vulnerable', 0), side('fixed', 0)]).found).toBe(false)
    console.log('OWNED_ARGUMENT_SWAP ' + JSON.stringify({scope: 'finite owned same-type argument contrast only; no general forwarding or upstream recall guarantee', hashes, witness, parameterOrder: ['permit', 'deny'], controls}))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 120_000)
