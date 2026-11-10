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

test('the fresh pinned Python corpus cannot count unchecked native-law results as strict recall', async () => {
  for (const c of cases) {
    const row = await measure(c)
    expect(row.baseline.fullyRead).toBe(true)
    expect(row.baseline.exit).toBe(2)
    expect(row.baseline.claims.length).toBeGreaterThan(0)
    expect(row.baseline.claims.every(l => l.verdict === 'unknown' && l.translation === 'unchecked' && l.kernelProven)).toBe(true)
    expect(row.mutants.every(m => !m.detected && m.side.fullyRead)).toBe(true)
    expect(row.mutants.every(m => m.side.exit === 2 && m.side.claims.every(l => l.verdict === 'unknown' && l.translation === 'unchecked'))).toBe(true)
  }
}, 180_000)
