// Finite owned method-order contrast; only fixed allowlisted calls are replayed.
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, unlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {check} from '../../core/cli.ts'
import {scoreRecall, type RecallSide} from './score.ts'

type OwnedCall = 'arm' | 'hit'
// Fixture-only gate: validate every line before dispatch, then hand over a frozen copy.
function replayOwnedTrace<T>(trace: unknown, dispatch: (calls: readonly OwnedCall[]) => T): T {
  if (!Array.isArray(trace) || trace.length === 0) throw Error('owned replay requires a nonempty trace')
  const calls: OwnedCall[] = []
  for (const line of trace as unknown[]) {
    if (line === 'arm()') calls.push('arm')
    else if (line === 'hit()') calls.push('hit')
    else throw Error('owned replay rejects a nonallowlisted call')
  }
  return dispatch(Object.freeze(calls))
}

type OwnedNativeObservation = {status: number | null, signal: string | null, error?: Error, stdout: unknown}
// This is only the fixed OwnedOrder fixture's result format, not a general receipt API.
function ownedNativeRow(result: OwnedNativeObservation, expectedSteps: number): readonly [string, string, string, string] {
  if (result.status !== 0 || result.signal !== null || result.error !== undefined || typeof result.stdout !== 'string') {
    throw Error('owned native replay did not finish successfully')
  }
  const match = /^(true|false):(0|[1-9]\d*):(0|[1-9]\d*):(true|false)\n$/.exec(result.stdout)
  if (!match || match[0] !== result.stdout || !Number.isSafeInteger(Number(match[2])) || !Number.isSafeInteger(Number(match[3])) || Number(match[3]) !== expectedSteps) {
    throw Error('owned native replay returned an invalid or incomplete row')
  }
  return [match[1]!, match[2]!, match[3]!, match[4]!]
}

test('owned native rows reject inconsistent process or output fields', () => {
  const good = {status: 0, signal: null, stdout: 'false:0:1:true\n'}
  expect(ownedNativeRow(good, 1)).toEqual(['false', '0', '1', 'true'])
  for (const patch of [{status: null}, {signal: 'SIGTERM'}, {error: new Error('owned transport failure')}, {stdout: undefined}, {stdout: false}]) {
    expect(() => ownedNativeRow({...good, ...patch}, 1)).toThrow()
  }
})

test('owned replay validates the whole trace before any dispatch', () => {
  let dispatches = 0, coercions = 0
  const invalid: unknown[] = [
    null, undefined, 42, 'arm()', {}, [], ['arm()', 7], ['hit()', null], new Array(2),
    ['arm()', {toString: () => { coercions++; return 'arm()' }}],
  ]
  for (const bad of ['unknown()', 'arm(1)', 'arm();', ' hit()', 'hit() ', 'hit()\narm()', 'ARM()', '']) {
    invalid.push([bad, 'arm()', 'hit()'], ['arm()', bad, 'hit()'], ['arm()', 'hit()', bad])
  }
  for (const trace of invalid) {
    expect(() => replayOwnedTrace(trace, () => { dispatches++; return null })).toThrow()
    expect(dispatches).toBe(0)
  }
  expect(coercions).toBe(0)
  console.log('OWNED_TRACE_REJECTION ' + JSON.stringify({scope: 'fixture-only malformed-input controls; no general replay guarantee', cases: invalid.length, dispatches, coercions}))
})

test('owned replay dispatches one frozen order-preserving snapshot', () => {
  const input = ['hit()', 'arm()', 'arm()', 'hit()']
  let dispatches = 0
  const received = replayOwnedTrace(input, calls => {
    dispatches++
    expect(Object.isFrozen(calls)).toBe(true)
    input.fill('unknown()')
    return [...calls]
  })
  expect(received).toEqual(['hit', 'arm', 'arm', 'hit'])
  expect(dispatches).toBe(1)
})

const nativeTest = ['javac', 'java'].every(tool => spawnSync(tool, ['-version'], {timeout: 5000}).status === 0) ? test : test.skip
nativeTest('owned multi-call witness order changes the native policy outcome', async () => {
  const root = mkdtempSync(join(tmpdir(), 'owned-call-order-'))
  const source = (repaired: boolean) => `public class OwnedOrder {
    public int value = 0;
    public boolean armed;
    public OwnedOrder() { armed = false; }
    public void arm() { armed = true; }
    // gdp: law no value writes: value == old(value)
    public void hit() { if (armed) value += ${repaired ? 0 : 1}; }
  }`
  const driver = `public class ReplayOrder {
    public static void main(String[] args) {
      OwnedOrder current = new OwnedOrder();
      boolean broken = false;
      for (String call : args) {
        int previous = current.value;
        switch (call) {
          case "arm": current.arm(); break;
          case "hit": current.hit(); break;
          default: throw new IllegalArgumentException("call is not allowlisted");
        }
        if (current.value != previous) broken = true;
      }
      System.out.println(broken + ":" + current.value + ":" + args.length + ":" + current.armed);
    }
  }`
  const sources = [source(false), source(true)], versions = ['original', 'repaired']
  const hashes = sources.map(text => createHash('sha256').update(text).digest('hex'))
  const results: Awaited<ReturnType<typeof check>>[] = []
  const controls: {version: string, scenario: string, calls: string[], broken: boolean, value: number, steps: number, finalArmed: boolean, sourceSha256: string}[] = []
  try {
    for (const [i, version] of versions.entries()) {
      const dir = join(root, version)
      mkdirSync(dir)
      const file = join(dir, 'OwnedOrder.java')
      writeFileSync(file, sources[i]!); writeFileSync(join(dir, 'ReplayOrder.java'), driver)
      results.push(await check([file], {entry: 'OwnedOrder', methods: ['arm', 'hit'], propose: false, ms: 3000, check: {runs: 10, depth: 6, states: 30}}))
      const compiled = spawnSync('javac', [file, join(dir, 'ReplayOrder.java')], {encoding: 'utf8', timeout: 30_000})
      expect(compiled.status, compiled.stderr).toBe(0)
      expect(results[i]!.rules).toHaveLength(1)
      const rule = results[i]!.rules[0]!
      expect(rule.entry).toBe('OwnedOrder')
      expect(rule.ctor).toBeUndefined()
      expect(rule.ok && !!rule.checked).toBe(true)
      expect(rule.laws).toHaveLength(1)
      expect(rule.laws[0]!.verdict).toBe(i === 0 ? 'broken' : 'proven')
    }
    const side = (version: string, i: number): RecallSide => ({version, status: 'checked', result: results[i]!})
    expect(scoreRecall([side('vulnerable', 0), side('fixed', 1)]).found).toBe(false)
    const law = results[0]!.rules[0]!.laws[0]!, witness = law.run!
    const exact = replayOwnedTrace(witness, calls => [...calls])
    expect(exact).toContain('arm')
    expect(exact).toContain('hit')
    const reordered = [...exact.filter(call => call === 'hit'), ...exact.filter(call => call === 'arm')]
    const sorted = (calls: string[]) => [...calls].sort((a, b) => a.localeCompare(b))
    expect(sorted(reordered)).toEqual(sorted(exact))
    expect(reordered).not.toEqual(exact)
    const scenarios = [{kind: 'exact', calls: exact}, {kind: 'reordered', calls: reordered}]
    for (const [i, version] of versions.entries()) for (const scenario of scenarios) {
      const native = replayOwnedTrace(scenario.calls.map(call => call + '()'), calls =>
        spawnSync('java', ['-cp', join(root, version), 'ReplayOrder', ...calls], {encoding: 'utf8', timeout: 10_000}))
      expect(native.status, native.stderr).toBe(0)
      const [bad, value, steps, armed] = ownedNativeRow(native, scenario.calls.length)
      expect(['true', 'false']).toContain(bad ?? '')
      const firstArm = scenario.calls.indexOf('arm')
      const expectedValue = i === 0 ? scenario.calls.filter((call, j) => call === 'hit' && j > firstArm).length : 0
      expect(Number(value)).toBe(expectedValue)
      expect(bad === 'true').toBe(expectedValue > 0)
      expect(Number(steps)).toBe(scenario.calls.length)
      expect(armed).toBe('true')
      const bytes = readFileSync(join(root, version, 'OwnedOrder.java'), 'utf8')
      expect(bytes).toBe(sources[i]!)
      const sourceSha256 = createHash('sha256').update(bytes).digest('hex')
      expect(sourceSha256).toBe(hashes[i]!)
      controls.push({version, scenario: scenario.kind, calls: scenario.calls, broken: bad === 'true', value: Number(value), steps: Number(steps), finalArmed: armed === 'true', sourceSha256})
    }
    expect(controls[0]!.broken).toBe(true)
    expect(controls[1]!.broken).toBe(false)
    expect(controls[0]!.sourceSha256).toBe(controls[1]!.sourceSha256)
    law.replayed = 'exact allowlisted multi-call witness replayed natively; order-only contrast preserved call multiset and source bytes'
    expect(scoreRecall([side('vulnerable', 0), side('fixed', 1)]).found).toBe(true)
    expect(scoreRecall([side('vulnerable', 0), side('fixed', 0)]).found).toBe(false)
    console.log('OWNED_CALL_ORDER ' + JSON.stringify({scope: 'finite owned allowlisted method-order contrast only; no general replay or upstream recall guarantee', hashes, constructorArguments: [], methodArguments: [], witness, reorderedWitness: reordered.map(call => call + '()'), controls}))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 120_000)

nativeTest('owned native process failures never produce an accepted result row', () => {
  const root = mkdtempSync(join(tmpdir(), 'owned-result-boundary-'))
  const file = join(root, 'OwnedResultProbe.java')
  const source = `public class OwnedResultProbe {
    public static void main(String[] args) throws Exception {
      String good = "false:0:1:true\\n";
      switch (args[0]) {
        case "ok": System.out.print(good); break;
        case "absent": break;
        case "invalid": System.out.println("not a result row"); break;
        case "truncated": System.out.print("false:0:1:"); break;
        case "no-newline": System.out.print("false:0:1:true"); break;
        case "extra-row": System.out.print(good + good); break;
        case "extra-newline": System.out.print(good + "\\n"); break;
        case "wrong-count": System.out.println("false:0:2:true"); break;
        case "overflow": System.out.println("false:9007199254740992:1:true"); break;
        case "nonzero": System.out.print(good); System.exit(7); break;
        case "timeout": System.out.print(good); System.out.flush(); Thread.sleep(30000); break;
        default: throw new IllegalArgumentException("unknown owned probe mode");
      }
    }
  }`
  const observations: {mode: string, status: number | null, signal: string | null, error: string | null, stdout: string, accepted: boolean}[] = []
  try {
    writeFileSync(file, source)
    const compiled = spawnSync('javac', [file], {encoding: 'utf8', timeout: 30_000})
    expect(compiled.status, compiled.stderr).toBe(0)
    for (const mode of ['ok', 'absent', 'invalid', 'truncated', 'no-newline', 'extra-row', 'extra-newline', 'wrong-count', 'overflow', 'nonzero', 'timeout']) {
      const native = spawnSync('java', ['-cp', root, 'OwnedResultProbe', mode], {encoding: 'utf8', timeout: mode === 'timeout' ? 2000 : 10_000})
      let accepted = false
      const collect = () => {
        const row = ownedNativeRow(native, 1)
        accepted = true
        return row
      }
      if (mode === 'ok') expect(collect()).toEqual(['false', '0', '1', 'true'])
      else expect(collect).toThrow()
      expect(accepted).toBe(mode === 'ok')
      if (mode === 'nonzero') {
        expect(native.status).toBe(7)
        expect(native.stdout).toBe('false:0:1:true\n')
      }
      if (mode === 'timeout') {
        expect(native.error).toBeDefined()
        expect(native.status).not.toBe(0)
      }
      observations.push({mode, status: native.status, signal: native.signal, error: native.error?.message ?? null, stdout: native.stdout, accepted})
      expect(readFileSync(file, 'utf8')).toBe(source)
    }
    console.log('OWNED_NATIVE_RESULT_FAILURES ' + JSON.stringify({scope: 'finite owned process/row probes; accepted means fixture row validation only, not policy proof', sourceSha256: createHash('sha256').update(source).digest('hex'), observations}))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 120_000)

nativeTest('owned invalid traces do not launch the armed native entry probe', () => {
  const root = mkdtempSync(join(tmpdir(), 'owned-launch-boundary-'))
  const marker = join(root, 'entry.log'), file = join(root, 'OwnedLaunch.java')
  const source = `import java.nio.file.*;
    import java.util.Arrays;
    public class OwnedLaunch {
      public static void main(String[] args) throws Exception {
        Files.writeString(Path.of(args[0]), "entered\\n", StandardOpenOption.CREATE, StandardOpenOption.APPEND);
        for (int i = 1; i < args.length; i++) {
          if (!args[i].equals("arm") && !args[i].equals("hit")) throw new IllegalArgumentException("call not allowed");
        }
        System.out.println(String.join(",", Arrays.copyOfRange(args, 1, args.length)));
      }
    }`
  let launches = 0
  try {
    writeFileSync(file, source)
    const compiled = spawnSync('javac', [file], {encoding: 'utf8', timeout: 30_000})
    expect(compiled.status, compiled.stderr).toBe(0)
    expect(existsSync(marker)).toBe(false)
    const launch = (calls: readonly OwnedCall[]) => {
      launches++
      return spawnSync('java', ['-cp', root, 'OwnedLaunch', marker, ...calls], {encoding: 'utf8', timeout: 10_000})
    }
    const before = replayOwnedTrace(['arm()', 'hit()'], launch)
    expect(before.status, before.stderr).toBe(0)
    expect(before.stdout.trim()).toBe('arm,hit')
    expect(readFileSync(marker, 'utf8')).toBe('entered\n')
    expect(launches).toBe(1)
    unlinkSync(marker)
    const invalid: unknown[] = [
      ['arm()', 'unknown()'], ['hit()', 'arm()', 'unknown()'],
      ['arm()', 'hit() ', 'hit()'], ['arm()', 'arm(1)'],
      ['hit()', 'hit()\narm()'], ['arm()', null], ['arm()', 1], ['arm()', {}],
      ['unknown()', 'arm()'], [], null, 'arm()',
    ]
    for (const trace of invalid) {
      expect(() => replayOwnedTrace(trace, launch)).toThrow()
      expect(launches).toBe(1)
      expect(existsSync(marker)).toBe(false)
    }
    const after = replayOwnedTrace(['hit()', 'arm()'], launch)
    expect(after.status, after.stderr).toBe(0)
    expect(after.stdout.trim()).toBe('hit,arm')
    expect(readFileSync(marker, 'utf8')).toBe('entered\n')
    expect(launches).toBe(2)
    expect(readFileSync(file, 'utf8')).toBe(source)
    console.log('OWNED_NO_NATIVE_LAUNCH ' + JSON.stringify({scope: 'finite owned replay-entry probe, not a general process isolation guarantee', sourceSha256: createHash('sha256').update(source).digest('hex'), rejectedCases: invalid.length, rejectedReplayLaunches: 0, rejectedEntryMarkers: 0, positiveReplayLaunches: launches, positiveOrders: [before.stdout.trim(), after.stdout.trim()]}))
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 120_000)
