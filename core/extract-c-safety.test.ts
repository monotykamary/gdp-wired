// Safety tests check the extracted model, not a generated native harness.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {proveLaws} from '../kernel/prove.ts'
import {bool, rule} from './dsl.ts'
import {check} from './cli.ts'
import {extractC, type COptions} from './extract-c.ts'

const hasClang = (() => { try { execFileSync('clang', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const withClang = hasClang ? test : test.skip

const analyze = (code: string, given: COptions = {}) => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-'))
  try {
    const file = join(dir, 'ring.c')
    writeFileSync(file, code)
    return extractC(file, {entry: 'ring', ...given, safety: true})
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}

withClang('C Safety checks a guarded eight-slot cursor and records AST positions', () => {
  const x = analyze(`struct ring { int head; int slots[8]; };
int rotate(struct ring *r) {
  if (r->head < 0 || r->head >= 8) return 0;
  int saved = r->slots[r->head];
  r->slots[r->head] = 1;
  if (r->head == 7) r->head = 0;
  else r->head = r->head + 1;
  return saved;
}
`)
  expect(x.safety?.status, JSON.stringify(x.refusals)).toBe('proven')
  const positions = x.safety!.issues.filter(o => o.kind === 'bounds').map(o => o.where.split('/').at(-1)?.replace(/-\d+:\d+(?:#\d+)?$/, '')).sort()
  expect(positions).toEqual(['ring.c:4:15', 'ring.c:5:3'])
  expect(x.evidence).toBeUndefined()
}, 60_000)

withClang('C Safety refuses uncovered constructs rather than certifying an incomplete rule', () => {
  const x = analyze(`struct ring { int head; int slots[8]; };
void reset(struct ring *r) {
  while (r->head != 0) r->head = 0;
}
`)
  expect(x.safety?.status).toBe('unchecked')
  expect(x.refusals.map(r => r.what).join('; ')).toMatch(/loop|while/i)
  expect(x.evidence).toBeUndefined()
}, 60_000)

withClang('C Safety never lets a later configured refusal hide division or signed remainder faults', () => {
  const x = analyze(`struct ring { int head; };
int update(struct ring *r, int x) {
  r->head = x % -1;
  return -1;
}
`, {fails: {update: '== -1'}})
  expect(x.safety?.status, JSON.stringify(x.refusals)).toBe('unproven')
  expect(x.safety?.issues).toContainEqual({kind: 'division', where: expect.stringMatching(/ring\.c:3:/), status: 'unproven'})
  expect(x.evidence).toBeUndefined()
}, 60_000)

withClang('C Safety rejects an off-by-one guard in the static model at its access site', () => {
  const code = `struct ring { int slots[8]; };
void put(struct ring *r, int index) {
  if (index < 0 || index >= 8) return;
  r->slots[index] = 1;
}
`
  expect(analyze(code).safety?.status).toBe('proven')
  const result = analyze(code.replace('index >= 8', 'index > 8'))
  expect(result.safety?.issues).toContainEqual({kind: 'bounds', where: expect.stringMatching(/ring\.c:4:/), status: 'unproven'})
  expect(result.evidence).toBeUndefined()
}, 60_000)

withClang('C Safety inventories constant arithmetic and skips a later fault after the first', () => {
  const exact = analyze(`struct ring { int head; };
void move(struct ring *r) { r->head = 1 + 2; }
`)
  expect(exact.safety?.issues).toContainEqual({kind: 'overflow', where: expect.stringMatching(/ring\.c:2:/), status: 'proven'})
  const ordered = analyze(`struct ring { int head; };
void move(struct ring *r, int n) {
  int value = n / 0;
  r->head = value % -1;
}
`)
  const divisions = ordered.safety?.issues.filter(s => s.kind === 'division')
  expect(divisions).toEqual([
    {kind: 'division', where: expect.stringMatching(/ring\.c:3:/), status: 'unproven'},
    {kind: 'division', where: expect.stringMatching(/ring\.c:4:/), status: 'proven'},
  ])
  expect(ordered.evidence).toBeUndefined()
}, 60_000)

withClang('C Safety marks a selected file with no supported model unchecked in the CLI', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-cli-'))
  try {
    const file = join(dir, 'ring.c')
    writeFileSync(file, '// gdp: safety\nstruct ring { int head; };\nvoid update(struct ring *r) { while (r->head) r->head = 0; }\n')
    const x = await check([file], {entry: 'ring', propose: false})
    expect(x.exit).toBe(2)
    expect(x.rules[0]?.safety).toMatchObject({status: 'unchecked'})
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 60_000)

test('removing an abstract bounds guard does not prove absence of alarms', () => {
  // The mutant is only a Boolean model: no C source, index, replay, or sampled request.
  const check = (guarded: boolean) => {
    const r = rule('abstract access guard').inputs({request: bool, inBounds: bool}).state({alarm: bool.from(false)})
      .step(({alarm, request, inBounds}) => {
        const reached = guarded ? request.and(inBounds) : request
        return {alarm: alarm.or(reached.and(inBounds.not()))}
      })
    const clear = r.law('the bounds alarm stays clear', ({alarm}) => alarm.not())
    const {proven, checked, failed} = proveLaws(r.machine, [clear])
    return {proven, checked, stuck: failed?.stuck}
  }
  expect(check(true)).toMatchObject({proven: true, checked: true})
  expect(check(false)).toMatchObject({proven: false, checked: false, stuck: 'sat'})
})
