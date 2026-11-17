// Run in an isolated default-profile process. A two-run helper preflight is not
// bounded by the CLI work/watchdog options: refuse the mode before proving.
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {mkdtempSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {check} from './cli.ts'
import {nat, rule} from './dsl.ts'
import {extract} from './extract.ts'
import {buildTwoRuns} from './laws.ts'
import {noninterference, proveTwoRuns} from './relational.ts'

const source = `export class TwoRunBudget {
  value = 0;
  helper = 0;
  // gdp: law secret stays private: secret never reaches value
  tick(amount: number, secret: number) {
    this.value += amount;
    this.helper += 1;
    return secret;
  }
}
`
const refusal = (mode: 'work budget' | 'watchdog') =>
  `explicit ${mode} is not supported for two-run checks: helper preflight is not yet ${mode === 'work budget' ? 'work' : 'watchdog'}-scoped`
const cleanEnv = () => Object.fromEntries(Object.entries(process.env).filter(([key]) => !key.startsWith('GDP_WORK_') && key !== 'GDP_STEP_WORK'))

// The regression must exercise the genuine helper early-return path, not an
// empty-helper fallback that already receives the caller's options.
test('two-run positive control completes through nonempty helper preflight', () => {
  const r = rule('two-run budget control').inputs({amount: nat, secret: nat})
    .state({value: 0, helper: 0})
    .step(({amount, value, helper}) => ({value: value.plus(amount), helper: helper.plus(1)}))
  const two = noninterference(r, {secret: ['secret'], visible: ['value']})
  expect(two.helpers.length).toBeGreaterThan(0)
  let fallbackRead = false
  const out = proveTwoRuns(two, {get search(): false { fallbackRead = true; return false }})
  expect(out.proven && out.checked).toBe(true)
  expect(fallbackRead, 'checked helper result must return before fallback options are read').toBe(false)
}, 60000)

test('CLI refuses watchdog-only and work modes instead of running two-run helper preflight', async () => {
  const root = mkdtempSync(join(tmpdir(), 'gdp-two-run-budget-')), file = join(root, 'TwoRunBudget.ts')
  try {
    writeFileSync(file, source)
    const options = {entry: 'TwoRunBudget', propose: false, check: {runs: 10, depth: 6, states: 20}}
    const extracted = extract(file, {entry: options.entry, check: options.check})
    expect(extracted.ok, JSON.stringify(extracted.refusals)).toBe(true)
    const two = buildTwoRuns(extracted, {name: 'secret stays private', expr: 'secret never reaches value'})
    expect(two.helpers.length).toBeGreaterThan(0)
    let fallbackRead = false
    const preflight = proveTwoRuns(two, {invariants: extracted.invariants ?? [], get search(): false { fallbackRead = true; return false }})
    expect(preflight.proven && preflight.checked || preflight.kernelProven === true).toBe(true)
    expect(fallbackRead, 'the exact source fixture must complete inside helper preflight').toBe(false)
    const baseline = await check([file], {...options, ms: 5000})
    const positive = baseline.rules[0]?.laws.find(law => law.name === 'secret stays private')
    expect(positive?.kind).toBe('two runs')
    expect(positive?.verdict === 'proven' || positive?.kernelProven === true, JSON.stringify(baseline)).toBe(true)
    for (const [budget, mode] of [
      [{watchdogMs: 0}, 'watchdog'],
      [{watchdogMs: 60000}, 'watchdog'],
      [{work: 0}, 'work budget'],
      [{work: 0, watchdogMs: 0}, 'work budget'],
    ] as const) {
      const result = await check([file], {...options, ...budget})
      const law = result.rules[0]?.laws.find(candidate => candidate.name === 'secret stays private')
      expect(result.exit, JSON.stringify(result)).toBe(2)
      expect(law).toMatchObject({kind: 'two runs', verdict: 'unknown', why: refusal(mode)})
      expect(law?.kernelProven).toBeUndefined()
      expect(law?.stopped).toBeUndefined()
      expect(law?.termination).toBeUndefined()
      expect(law?.run).toBeUndefined()
      expect(law?.cert).toBeUndefined()
    }
    const argv = spawnSync(process.execPath, [new URL('./cli.ts', import.meta.url).pathname, 'check', file,
      '--entry', 'TwoRunBudget', '--no-propose', '--watchdog-ms', '0', '--json'],
    {env: cleanEnv(), encoding: 'utf8', timeout: 30000})
    expect(argv.status, argv.stderr).toBe(2)
    const law = (JSON.parse(argv.stdout) as Awaited<ReturnType<typeof check>>).rules[0]?.laws[0]
    expect(law).toMatchObject({kind: 'two runs', verdict: 'unknown', why: refusal('watchdog')})
    expect(law?.stopped).toBeUndefined()
    expect(law?.termination).toBeUndefined()
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 120000)
