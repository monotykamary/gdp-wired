import {expect, setDefaultTimeout, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {existsSync, mkdtempSync, rmSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {HarnessFailure, sandbox} from './extract-check.ts'
import {extract} from './extract.ts'
import {extractEffect} from './effect.ts'
import {extractXState} from './extract-xstate.ts'
import * as effect from 'effect'
import * as xstate from 'xstate'

setDefaultTimeout(120_000)

const repo = new URL('../', import.meta.url).pathname
const cliTs = new URL('./cli.ts', import.meta.url).pathname
const cliJs = new URL('../dist/core/cli.js', import.meta.url).pathname
const built = existsSync(cliJs)

const manyClassLaws = Array.from({length: 40}, (_, i) => `  // gdp: law bound ${i}: tokens <= capacity + ${i}`).join('\n')
const A2_CLASS = `export class Bucket {
  tokens: number
  constructor(public capacity: number) { this.tokens = capacity }
  // gdp: law never negative: tokens >= 0
${manyClassLaws}
  take(n: number) { if (n < 0) throw new Error('neg'); this.tokens -= n }
  refill(n: number) { this.tokens = Math.min(this.capacity, this.tokens + Math.max(0, n)) }
}
`

const manyEffectLaws = Array.from({length: 40}, (_, i) => `// gdp: law bound ${i}: tokens <= capacity + ${i}`).join('\n')
const A1_MANYLAWS = `import {Effect, Ref, Schema} from 'effect'

export class RateLimited extends Schema.TaggedError<RateLimited>()('RateLimited', {n: Schema.Number}) {}

// gdp: law tokens stay within the capacity: tokens <= capacity
// gdp: law tokens never go negative: tokens >= 0
${manyEffectLaws}
export const make = (capacity: number) => Effect.gen(function* () {
  const tokens = yield* Ref.make(capacity)

  const take = Effect.fn('take')(function* (n: number) {
    const left = yield* Ref.modify(tokens, (t) =>
      n < 0 ? [undefined, t] as const : [t - n, t - n] as const)
    if (left === undefined) return yield* new RateLimited({n})
    return left
  })

  const refill = (n: number) =>
    Ref.update(tokens, (t) => Math.min(capacity, t + Math.max(0, n)))

  return {take, refill}
})
`

const EXTRACTABLE_EFFECT_MANYLAWS = `import {Effect, Ref} from 'effect'

// gdp: law tokens stay within the capacity: tokens <= capacity
// gdp: law tokens never go negative: tokens >= 0
${manyEffectLaws}
export const make = (capacity: number) => Effect.gen(function* () {
  const tokens = yield* Ref.make(capacity)

  const take = Effect.fn('take')(function* (n: number) {
    if (n < 0) return yield* Effect.fail('neg')
    const t = yield* Ref.get(tokens)
    yield* Ref.set(tokens, t - n)
    return t - n
  })

  const refill = Effect.fn('refill')(function* (n: number) {
    const t = yield* Ref.get(tokens)
    const add = n > 0 ? n : 0
    yield* Ref.set(tokens, Math.min(capacity, t + add))
  })

  return {take, refill}
})
`

test('fail-safe exit code: an unsettled main exits 2 with a stderr diagnostic on Bun and Node', () => {
  const runtimes: Array<{cmd: string, args: (code: string) => string[], target: string}> = [
    {cmd: process.execPath, args: code => ['-e', code], target: cliTs},
    ...(built ? [{cmd: 'node', args: (code: string) => ['--input-type=module', '-e', code], target: cliJs}] : []),
  ]
  for (const rt of runtimes) {
    const unsettled = `import {runCli} from ${JSON.stringify(rt.target)}; runCli(['check'], {run: () => new Promise(() => {})});`
    const res = spawnSync(rt.cmd, rt.args(unsettled), {cwd: repo, encoding: 'utf8', timeout: 15_000})
    expect(res.status, `${rt.cmd} unsettled stderr=${res.stderr}`).toBe(2)
    expect(res.stderr).toContain('gdp-wired: the check did not complete')

    const unsettledCli = `import {runCli} from ${JSON.stringify(rt.target)}; runCli(['check'], {label: 'gdp-wired-cli', run: () => new Promise(() => {})});`
    const resCli = spawnSync(rt.cmd, rt.args(unsettledCli), {cwd: repo, encoding: 'utf8', timeout: 15_000})
    expect(resCli.status, `${rt.cmd} unsettled-cli stderr=${resCli.stderr}`).toBe(2)
    expect(resCli.stderr).toContain('gdp-wired: the check did not complete')

    const rejected = `import {runCli} from ${JSON.stringify(rt.target)}; runCli(['check'], {run: () => Promise.reject(new Error('boom'))});`
    const resRej = spawnSync(rt.cmd, rt.args(rejected), {cwd: repo, encoding: 'utf8', timeout: 15_000})
    expect(resRej.status).toBe(2)
    expect(resRej.stdout).toContain('gdp-wired: boom')
    expect(resRej.stderr).toBe('')

    const resolvedZero = `import {runCli} from ${JSON.stringify(rt.target)}; runCli(['check'], {run: async () => 0});`
    const resOk = spawnSync(rt.cmd, rt.args(resolvedZero), {cwd: repo, encoding: 'utf8', timeout: 15_000})
    expect(resOk.status).toBe(0)
    expect(resOk.stderr).toBe('')
  }
})

test('CLI reports broken law (exit 1, never silent exit 0) on many-law TS class and never exits 0 on many-law Effect files', () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-cli-failsafe-'))
  try {
    symlinkSync(join(repo, 'node_modules'), join(dir, 'node_modules'))
    const a2 = join(dir, 'a2-class.ts')
    const a1 = join(dir, 'a1-manylaws.ts')
    const fx = join(dir, 'fx-manylaws.ts')
    writeFileSync(a2, A2_CLASS)
    writeFileSync(a1, A1_MANYLAWS)
    writeFileSync(fx, EXTRACTABLE_EFFECT_MANYLAWS)

    const runtimes: Array<{cmd: string, entry: string}> = [
      {cmd: process.execPath, entry: cliTs},
      ...(built ? [{cmd: 'node', entry: cliJs}] : []),
    ]
    for (const rt of runtimes) {
      const r2 = spawnSync(rt.cmd, [rt.entry, 'check', a2, '--no-propose', '--ms', '1000', '--json'], {cwd: repo, encoding: 'utf8', timeout: 60_000})
      expect(r2.status, `${rt.cmd} a2-class stderr=${r2.stderr}`).toBe(1)
      expect(r2.stdout.length).toBeGreaterThan(0)
      const parsed2 = JSON.parse(r2.stdout) as {exit: number, rules: {ok: boolean, laws: {name: string, verdict: string}[]}[]}
      expect(parsed2.exit).toBe(1)
      expect(parsed2.rules[0]?.ok).toBe(true)
      const neg = parsed2.rules[0]?.laws.find(l => l.name === 'never negative')
      expect(neg?.verdict).toBe('broken')
      expect(parsed2.rules[0]?.laws.filter(l => l.verdict === 'proven').length).toBe(40)

      const r1 = spawnSync(rt.cmd, [rt.entry, 'check', a1, '--no-propose', '--ms', '1000', '--json'], {cwd: repo, encoding: 'utf8', timeout: 60_000})
      expect(r1.status, `${rt.cmd} a1-manylaws stderr=${r1.stderr}`).not.toBe(0)
      expect(r1.stdout.length).toBeGreaterThan(0)
      const parsed1 = JSON.parse(r1.stdout) as {exit: number, rules: unknown[]}
      expect(parsed1.exit).toBe(r1.status!)
      expect(parsed1.rules.length).toBeGreaterThan(0)

      const rfx = spawnSync(rt.cmd, [rt.entry, 'check', fx, '--no-propose', '--ms', '1000', '--json'], {cwd: repo, encoding: 'utf8', timeout: 60_000})
      expect(rfx.status, `${rt.cmd} fx-manylaws stderr=${rfx.stderr}`).toBe(2)
      expect(rfx.stdout.length).toBeGreaterThan(0)
      const parsedFx = JSON.parse(rfx.stdout) as {exit: number, rules: {ok: boolean, laws: unknown[]}[]}
      expect(parsedFx.exit).toBe(2)
      expect(parsedFx.rules[0]?.ok).toBe(true)
      expect(parsedFx.rules[0]?.laws.length).toBe(42)
    }
  } finally { rmSync(dir, {recursive: true, force: true}) }
})

test('sandbox enforces deadlines without leaking timers into later host JavaScript', () => {
  // Normal calls followed by >1.2s host work must complete and run finally cleanly.
  const okBox = sandbox(`
    export function compute(n: number): number {
      "use strict"
      let s = 0
      for (let i = 0; i < n; i++) for (let j = 0; j < 2; j++) s += 1
      let k = 0
      do k++
      while (k < 2)
      const make = (x: number) => (y: number) => ({sum: x + y})
      return make(s)(k).sum
    }
  `, 'ok.ts', ['compute'])
  for (let i = 0; i < 200; i++) {
    const res = okBox.call('compute', undefined, [3])
    expect(res).toEqual({ok: true, value: 8})
  }
  let finallyRan = false
  try {
    const end = performance.now() + 1250
    while (performance.now() < end) { /* host work past the 1000 ms sandbox limit */ }
  } finally {
    finallyRan = true
  }
  expect(finallyRan).toBe(true)

  // Infinite loops (including braceless and try/catch-swallowing loops) still throw HarnessFailure.
  const spin1 = sandbox('export function spin(): number { while (true) ; }', 'spin1.ts', ['spin'])
  expect(() => spin1.call('spin', undefined, [])).toThrow(HarnessFailure)

  const spin2 = sandbox('export function spin(): number { try { for (;;) {} } catch { return 0 } }', 'spin2.ts', ['spin'])
  expect(() => spin2.call('spin', undefined, [])).toThrow(HarnessFailure)

  // Top-level infinite loop during module load still times out cleanly.
  expect(() => sandbox('for (;;) {} export const x = 1', 'load-spin.ts', ['x'])).toThrow(/timed out/i)
})

test('sources mentioning reserved harness names (__gdp_tick, __cov, __now) are explicitly refused', () => {
  for (const name of ['__gdp_tick', '__cov', '__now'] as const) {
    // Plain TS class (identifier, local, computed string mention)
    const cls = extract(`export class Counter { n = 0; hit(${name}: number) { this.n += ${name} } }`, {file: 'counter.ts'})
    expect(cls.ok).toBe(false)
    expect(cls.evidence).toBeUndefined()
    expect(cls.refusals[0]?.what).toContain(`${name}: reserved harness name`)

    const strMention = extract(`export class Counter { n = 0; hit() { const k = '${name}'; if (k.length) this.n += 1 } }`, {file: 'str.ts'})
    expect(strMention.ok).toBe(false)
    expect(strMention.refusals[0]?.what).toContain(`${name}: reserved harness name`)

    // Relative imported helper file mentioning reserved harness name
    const imported = extract(`import {step} from './helper'\nexport class Counter { n = 0; hit() { this.n = step(this.n) } }`, {
      file: 'main.ts',
      files: {'helper.ts': `export function step(x: number) { const ${name} = 1; return x + ${name} }`},
    })
    expect(imported.ok).toBe(false)
    expect(imported.refusals[0]?.what).toContain(`${name}: reserved harness name`)

    // Effect service
    const fx = extractEffect(`import {Effect, Ref} from 'effect'\nexport const make = Effect.gen(function* () { const n = yield* Ref.make(0); const hit = (${name}: number) => Ref.update(n, x => x + ${name}); return {hit} })`, {file: 'svc.ts', effect})
    expect(fx.ok).toBe(false)
    expect(fx.evidence).toBeUndefined()
    expect(fx.refusals[0]?.what).toContain(`${name}: reserved harness name`)

    // XState machine
    const xs = extractXState(`import {setup} from 'xstate'\nexport const machine = setup({types: {context: {} as {${name}: number}}}).createMachine({id: 'm', initial: 'a', context: {${name}: 0}, states: {a: {}}})`, {file: 'm.ts', xstate})
    expect(xs.ok).toBe(false)
    expect(xs.evidence).toBeUndefined()
    expect(xs.refusals[0]?.what).toContain(`${name}: reserved harness name`)

    // Defense-in-depth directly on sandbox()
    expect(() => sandbox(`export function f() { return typeof ${name} }`, 'sb.ts', ['f'])).toThrow(/reserved harness name/)
  }
})
