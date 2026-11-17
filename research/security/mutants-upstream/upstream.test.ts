import {expect, test} from 'bun:test'
import {mkdtempSync, readFileSync, rmSync} from 'node:fs'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
import {cases, measure, prepare, python, validateVendor, type Mutation, type Row} from './run.ts'
import {verify} from './verify.ts'

const temporary = <T>(f: (directory: string) => T): T => {
  const dir = mkdtempSync(join(tmpdir(), 'upstream-test-'))
  try { return f(dir) } finally { rmSync(dir, {recursive: true, force: true}) }
}

test('upstream provenance keeps complete pinned MIT source and dependencies', () => {
  for (const c of cases) {
    expect(c.commit).toMatch(/^[a-f0-9]{40}$/)
    expect(c.license).toBe('MIT')
    validateVendor(c)
    const license = readFileSync(join(import.meta.dir, 'vendor', c.vendor, 'LICENSE'), 'utf8')
    expect(license).toContain('Permission is hereby granted')
    expect(license).toContain('Copyright')
  }
})

test('structural operators make exactly one UTF-8 edit and retain every generated mutant', () => temporary(dir => {
  let total = 0
  for (const c of cases) {
    const prepared = prepare(c, dir), bytes = Buffer.from(prepared.source)
    for (const m of prepared.mutations) {
      expect(bytes.subarray(m.startByte, m.endByte).toString()).toBe(m.before)
      expect(Buffer.concat([bytes.subarray(0, m.startByte), Buffer.from(m.after), bytes.subarray(m.endByte)]).toString()).toBe(m.source)
    }
    total += prepared.mutations.length
  }
  expect(total).toBe(9)
}))

test('operators depend on syntax rather than fixture names and handle non-BMP prefixes', () => temporary(dir => {
  const code = '# 🚀 UTF-8 byte offsets, not JS character offsets\nclass Other:\n    def grant(self, n):\n        if self.left < n:\n            raise ValueError()\n        self.left -= n\n    def give_back(self):\n        if self.used > 0:\n            self.used -= 1\n'
  const first = python<Mutation[]>({action: 'mutate', source: code, entry: 'Other'}, dir)
  const second = python<Mutation[]>({action: 'mutate', source: code.replaceAll('Other', 'Renamed').replaceAll('left', 'stock').replaceAll('used', 'count'), entry: 'Renamed'}, dir)
  expect(first.map(m => m.operator)).toEqual(second.map(m => m.operator))
  expect(first).toHaveLength(6)
  for (const m of first) expect(Buffer.from(code).subarray(m.startByte, m.endByte).toString()).toBe(m.before)
}))

test('the corpus refuses to omit a public callable or conceal a property descriptor', () => temporary(dir => {
  const c = cases[1]!
  expect(() => prepare({...c, methods: c.methods.slice(1)}, dir)).toThrow('omits')
  expect(() => prepare({...c, properties: []}, dir)).toThrow('omits')
}))

test('all saved upstream witnesses reproduce independently on both original and mutated source', () => {
  const document = JSON.parse(readFileSync(join(import.meta.dir, 'measurement.json'), 'utf8')) as {rows: Row[]}
  expect(verify(document.rows)).toEqual({modules: 2, mutants: 9, witnesses: 9, sourceReplays: 18})
  const forged = structuredClone(document.rows)
  forged[0]!.mutants[0]!.before = 'forged'
  expect(() => verify(forged)).toThrow('mutation edit changed')
}, 60_000)

test('strict upstream verification rejects refused, unchecked and unproven baselines', () => {
  const document = JSON.parse(readFileSync(join(import.meta.dir, 'measurement.json'), 'utf8')) as {rows: Row[]}
  for (const kind of ['refused', 'unchecked', 'unproven'] as const) {
    const rows = structuredClone(document.rows), baseline = rows[0]!.baseline
    baseline.fullyRead = kind !== 'refused'
    baseline.exit = 2
    baseline.claims[0]!.verdict = kind === 'refused' ? 'not read' : 'unknown'
    if (kind !== 'unproven') baseline.claims[0]!.translation = kind === 'refused' ? 'error' : 'unchecked'
    expect(() => verify(rows)).toThrow('clean baseline not fully proven')
  }
})

test('the fresh pinned Python corpus detects mutants only against proven native baselines', async () => {
  let total = 0
  for (const c of cases) {
    const row = await measure(c)
    expect(row.baseline.exit).toBe(0)
    expect(row.baseline.fullyRead).toBe(true)
    expect(row.baseline.claims).toHaveLength(c.policies.length)
    expect(row.baseline.rules.every(r => r.refusals.length === 0)).toBe(true)
    for (const [i, policy] of c.policies.entries()) {
      const claim = row.baseline.claims[i]!
      expect(claim).toMatchObject({name: policy.name, expr: policy.expr, verdict: 'proven', translation: 'sampled'})
      expect(claim.translationChecks).toBeGreaterThan(0)
    }
    expect(row.mutants.length).toBeGreaterThan(0)
    total += row.mutants.length
    for (const mutant of row.mutants) {
      expect(mutant.detected).toBe(true)
      expect(mutant.side.exit).toBe(1)
      expect(mutant.side.fullyRead).toBe(true)
      expect(mutant.side.claims).toHaveLength(c.policies.length)
      for (const [i, policy] of c.policies.entries()) {
        const law = mutant.side.claims[i]!
        expect(law).toMatchObject({name: policy.name, expr: policy.expr, verdict: 'broken', translation: 'sampled'})
        expect(law.run!.length).toBeGreaterThan(0)
        const replay = mutant.replays.find(r => r.policy.name === policy.name && r.policy.expr === policy.expr)
        expect(replay).toBeDefined()
        expect(replay!.mutant).toMatchObject({ok: true, broken: true})
        expect(replay!.parent).toMatchObject({ok: true, broken: false})
        expect(replay!.mutant.steps.length).toBeGreaterThan(0)
        expect(replay!.parent.steps.length).toBeGreaterThan(0)
      }
    }
  }
  expect(total).toBe(9)
}, 180_000)
