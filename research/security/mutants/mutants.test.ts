import {expect, test} from 'bun:test'
import {mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {join, resolve} from 'node:path'
import {mutate} from './operators.ts'
import {holds, parseCall, replayClass, replayIsolation} from './replay.ts'
import {instrumentEffect} from './replay_effect.ts'
import {admit, fixtures, measure, type Side, type MutantResult} from './run.ts'
import {lawsIn, parse} from '../../../core/laws.ts'
import {securityLaws} from '../../../core/security.ts'
import {verify} from './verify.ts'

const source = (name: string, ext = 'ts') => readFileSync(join(import.meta.dir, 'fixtures', name, `module.${ext}`), 'utf8')

test('all owned modules receive only one-site generic mutations and keep every stated law', () => {
  let count = 0
  for (const name of fixtures) {
    const language = name === 'race' ? 'py' : 'ts', original = source(name, language)
    const mutants = mutate(original, language)
    expect(mutants.length).toBeGreaterThan(0)
    expect(new Set(mutants.map(m => m.id)).size).toBe(mutants.length)
    for (const m of mutants) {
      expect(m.source).toBe(original.slice(0, m.start) + m.after + original.slice(m.end))
      expect(m.before).toBe(original.slice(m.start, m.end))
      expect(lawsIn(m.source).map(l => [l.name, l.expr])).toEqual(lawsIn(original).map(l => [l.name, l.expr]))
    }
    count += mutants.length
  }
  expect(count).toBe(16)
})

test('renaming and formatting do not select different operators; constructors are not operation guards', () => {
  const a = mutate(source('quota'), 'ts')
  const b = mutate(source('quota').replaceAll('Quota', 'Bucket').replaceAll('used', 'spent').replaceAll('limit', 'capacity').replaceAll('  ', '    '), 'ts')
  expect(a.map(m => m.operator)).toEqual(['remove-guard', 'invert-guard', 'relax-boundary'])
  expect(b.map(m => m.operator)).toEqual(a.map(m => m.operator))
  expect(a.every(m => m.source.includes("if (limit < 0) throw new Error('negative limit')"))).toBe(true)
  const keys = mutate('class X { m(a: string, b: string, c: string) { this.rows.set(a, 0) } }', 'ts')
  expect(keys.map(m => m.after)).toEqual(['b', 'c'])
  expect(new Set(keys.map(m => m.id)).size).toBe(2)
})

test('policy replay checks the prerequisite before the call, and refuses unknown syntax or names', () => {
  expect(holds('done != old(done) implies old(ready)', {done: false, ready: false}, {done: true, ready: true})).toBe(false)
  expect(holds('false implies missing', {}, {})).toBe(true)
  expect(() => holds('missing', {}, {})).toThrow()
  expect(() => holds('min(1, 2) == 1', {}, {})).toThrow(/outside/)
  expect(() => holds('n + 1 > 0', {}, {n: Number.MAX_SAFE_INTEGER})).toThrow(/safe integer/)
})

test('old and new map domains detect foreign insertion and deleting a foreign zero-valued row', () => {
  const laws = lawsIn(source('tenant'))
  const empty = {rows: new Map(), tenant: 'alice'}, foreign = {rows: new Map([['bob', 0]]), tenant: 'alice'}
  expect(holds(laws[0]!.expr, empty, foreign)).toBe(false)
  expect(holds(laws[1]!.expr, foreign, empty)).toBe(false)
  expect(holds(laws[0]!.expr, empty, empty)).toBe(true)
  expect(holds(laws[1]!.expr, foreign, foreign)).toBe(true)
})

test('trace arguments are parsed as literals, not evaluated as code', () => {
  expect(parseCall('f(key="a,b=\\\"c", n=-3, allowed=false)')).toEqual({method: 'f', args: {key: 'a,b="c', n: -3, allowed: false}})
  expect(parseCall('made with limit = 0')).toEqual({method: 'constructor', args: {limit: 0}})
  for (const s of ['f(n=evil())', 'f(n=1,n=2)', 'f(n=1); g()', 'f(n=1', 'f(...x)']) expect(() => parseCall(s)).toThrow()
})

test('detection needs both readable sides, a matching stated refutation and two successful source replays', () => {
  const baseline: Side = {sha256: '', exit: 0, fullyRead: true, claims: [{name: 'p', expr: 'n <= cap', entry: 'C', verdict: 'proven', ms: 0}], rules: [], proposals: {count: 0, broken: 0, allReviewRequired: true}}
  const bad: Side = {...baseline, exit: 1, claims: [{...baseline.claims[0]!, verdict: 'broken', run: ['f()']}]}
  const replays: MutantResult['replays'] = [{law: 'p', expr: 'n <= cap', entry: 'C', mutant: {ok: true, broken: true, steps: ['source step']}, parent: {ok: true, broken: false, steps: ['source step']}}]
  expect(admit(baseline, bad, replays)).toBe(true)
  expect(admit({...baseline, fullyRead: false}, bad, replays)).toBe(false)
  expect(admit(baseline, {...bad, fullyRead: false}, replays)).toBe(false)
  expect(admit(bad, bad, replays)).toBe(false)
  expect(admit(baseline, {...bad, claims: [{...bad.claims[0]!, run: undefined}]}, replays)).toBe(false)
  expect(admit(baseline, {...baseline, proposals: {count: 1, broken: 1, allReviewRequired: true}}, replays)).toBe(false)
  expect(admit(baseline, bad, [{...replays[0]!, mutant: {ok: false, broken: false, steps: []}}])).toBe(false)
  expect(admit(baseline, bad, [{...replays[0]!, parent: {ok: true, broken: true, steps: []}}])).toBe(false)
  expect(admit(baseline, bad, [{...replays[0]!, expr: 'different policy'}])).toBe(false)
  expect(admit(baseline, bad, [{...replays[0]!, mutant: {ok: true, broken: true, steps: []}}])).toBe(false)
})

test('stated policies match the public security templates', () => {
  const authorization = securityLaws({kind: 'authorization', name: 'p', effect: 'changes != old(changes)', requires: 'allowed'})[0]!
  const workflow = securityLaws({kind: 'workflow', name: 'w', effect: 'shipped != old(shipped)', prerequisite: 'approved'})[0]!
  const isolation = securityLaws({kind: 'isolation', name: 'i', map: 'rows', identity: 'tenant', key: 'k', fields: ['value']})
  expect(parse(lawsIn(source('permission'))[0]!.expr)).toEqual(parse(authorization.expr))
  expect(parse(lawsIn(source('workflow'))[0]!.expr)).toEqual(parse(workflow.expr))
  expect(lawsIn(source('tenant')).slice(0, 2).map(l => parse(l.expr))).toEqual(isolation.map(l => parse(l.expr)))
})

test('a real violation in another method is not a replay of the scoped step law', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'security-scope-')), file = join(dir, 'module.ts')
  try {
    writeFileSync(file, 'export class C {\n value = 0\n // gdp: law scoped: value == old(value)\n safe() {}\n other() { this.value++ }\n}')
    const scoped = await replayClass(file, 'C', 'value == old(value)', ['other()'], 3)
    expect(scoped.ok).toBe(false)
    expect(scoped.why).toContain('outside the stated step-law scope')
    const actual = await replayClass(file, 'C', 'value == old(value)', ['other()'])
    expect(actual).toMatchObject({ok: true, broken: true})
  } finally { rmSync(dir, {recursive: true, force: true}) }
})

test('read isolation compares intermediate observations, not only an equal final result', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'read-isolation-')), file = join(dir, 'module.ts')
  try {
    const clean = source('read-isolation'), mutant = mutate(clean, 'ts')[0]!
    const run = ["B is 1 (run b takes only B's calls)", 'put(tenant="other", value=3)', 'read(tenant="me", _target="other")', 'put(tenant="other", value=0)', 'read(tenant="me", _target="other")']
    writeFileSync(file, mutant.source)
    expect(await replayIsolation(file, 'PrivateRows', 'isolated by tenant seeing result', run, 'me')).toMatchObject({ok: true, broken: true})
    const parent = join(dir, 'clean.ts')
    writeFileSync(parent, clean)
    expect(await replayIsolation(parent, 'PrivateRows', 'isolated by tenant seeing result', run, 'me')).toMatchObject({ok: true, broken: false})
    expect(await replayIsolation(file, 'PrivateRows', 'isolated by tenant seeing result', run, undefined)).toMatchObject({ok: false})
  } finally { rmSync(dir, {recursive: true, force: true}) }
})

test('source scheduling hooks stay outside locks and transactions; operators expose the intended boundaries', () => {
  for (const [fixture, before, after, op] of [['lock', 1, 3, 'remove-lock'], ['transaction', 1, 2, 'narrow-transaction'], ['compare-set', 2, 3, 'split-compare-set']] as const) {
    const clean = source(fixture), mutants = mutate(clean, 'ts')
    expect(mutants.map(m => m.operator)).toEqual([op])
    expect(instrumentEffect(clean, 'make', 'test').units).toEqual({claim: before})
    expect(instrumentEffect(mutants[0]!.source, 'make', 'test').units).toEqual({claim: after})
    const renamed = clean.replaceAll('consumed', 'claimed').replaceAll('granted', 'successes').replaceAll('claim', 'acquire')
    expect(mutate(renamed, 'ts').map(m => m.operator)).toEqual([op])
  }
})

test('source races also reproduce with native runtime preemption and no scheduling hooks', () => {
  const document = JSON.parse(readFileSync(join(import.meta.dir, 'measurement.json'), 'utf8')) as {rows: Parameters<typeof verify>[0]}
  const dir = mkdtempSync(join(tmpdir(), 'native-effect-'))
  symlinkSync(resolve(import.meta.dir, '../../..', 'node_modules'), join(dir, 'node_modules'), 'dir')
  let reproduced = 0
  try {
    for (const row of document.rows) {
      const original = source(row.fixture, row.file.endsWith('.py') ? 'py' : 'ts')
      if (!/from ['"]effect['"]/.test(original)) continue
      const mutants = mutate(original, 'ts')
      for (const mutant of row.mutants) {
        const generated = mutants.find(m => m.id === mutant.id)!
        const law = mutant.side.claims.find(l => l.verdict === 'broken' && l.run?.length)!
        for (const [label, code, expected] of [['parent', original, false], ['mutant', generated.source, true]] as const) {
          const file = join(dir, `${row.fixture}-${label}.ts`), input = join(dir, 'request.json')
          writeFileSync(file, code)
          writeFileSync(input, JSON.stringify({file, entry: law.entry, expr: law.expr, run: law.run, directory: dir}))
          const process = spawnSync('bun', [join(import.meta.dir, 'native_effect.ts'), input], {encoding: 'utf8', timeout: 15_000})
          expect(process.status).toBe(0)
          const receipt = JSON.parse(process.stdout) as {ok: boolean, broken: boolean, schedulingHooks: boolean}
          expect(receipt).toMatchObject({ok: true, broken: expected, schedulingHooks: false})
          console.log('NATIVE_REPLAY ' + JSON.stringify({fixture: row.fixture, side: label, ...receipt}))
        }
        reproduced++
      }
    }
    expect(reproduced).toBe(3)
  } finally { rmSync(dir, {recursive: true, force: true}) }
}, 120_000)

test('the complete saved corpus replays without asking the prover again', async () => {
  const document = JSON.parse(readFileSync(join(import.meta.dir, 'measurement.json'), 'utf8')) as {rows: Parameters<typeof verify>[0]}
  expect(await verify(document.rows)).toMatchObject({baselines: 10, baselineRefuted: 0, baselineProven: 10, mutants: 16, detected: 16, replayed: 16})
  const missing = await verify([]).catch((error: unknown) => error)
  expect(missing).toBeInstanceOf(Error)
  expect((missing as Error).message).toContain('every owned fixture')
}, 120_000)

test('every owned mutant is freshly refuted and source-replayed, with no clean policy refuted', async () => {
  let count = 0
  for (const fixture of fixtures) {
    const row = await measure(fixture)
    expect(row.baseline.fullyRead).toBe(true)
    expect(row.baseline.claims.length).toBeGreaterThan(0)
    expect(row.baseline.claims.every(l => l.verdict === 'proven')).toBe(true)
    expect(row.mutants.every(m => m.detected)).toBe(true)
    for (const m of row.mutants) expect(m.replays[0]!.mutant.steps.length).toBeGreaterThan(0)
    count += row.mutants.length
  }
  expect(count).toBe(16)
}, 600_000)
