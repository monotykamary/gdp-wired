import {test, expect} from 'bun:test'
import {extract, proveRule} from './extract.ts'
import {mkdtempSync, writeFileSync, rmSync, readFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
const file = new URL('./orm-fixtures/handlers.ts', import.meta.url).pathname
const orm = {schema: 'schema.prisma', model: 'Account'}
for (const [entry, kind] of [['create', 'prisma'], ['update', 'prisma'], ['read', 'prisma'], ['lookup', 'typeorm'], ['save', 'typeorm']] as const) {
  test(`ORM ${entry} checks the original async handler`, () => {
    const x = extract(file, {entry, orm: {...orm, kind, ...(kind === 'typeorm' ? {schema: 'entity.ts'} : {})}, check: {runs: 8, depth: 3, states: 15, probes: true}})
    expect(x.refusals).toEqual([])
    expect(x.ok).toBe(true)
    expect(x.evidence!.requests).toBeGreaterThan(0)
    expect(x.model!.maps.length).toBe(1)
  })
}

test('nullable reads and incomplete saves fail closed', () => {
  const a = extract(file, {entry: 'unsafeRead', orm})
  expect(a.ok).toBe(false)
  expect(a.refusals[0]!.what).toContain('immediately')
  const b = extract(file, {entry: 'badSave', orm: {schema: 'entity.ts', model: 'Account', kind: 'typeorm'}})
  expect(b.ok).toBe(false)
  expect(b.refusals[0]!.what).toContain('every ORM column')
})
test('the harness imports the original module, not generated code', () => {
  const x = extract(new URL('./orm-fixtures/unloadable.ts', import.meta.url).pathname, {entry: 'create', orm, check: {runs: 1, states: 1}})
  expect(x.ok).toBe(false)
  expect(x.refusals[0]!.what).toContain('load')
})
test('multiple handlers share one table', () => {
  const x = extract(file, {entry: ['create', 'update', 'read'], orm, check: {runs: 12, depth: 4, states: 20}})
  expect(x.refusals).toEqual([])
  expect(x.evidence!.requests).toBeGreaterThan(0)
  expect(x.model!.maps).toHaveLength(1)
})

test('ORM map representation invariant is proved and kernel checked', () => {
  const x = extract(file, {entry: ['create', 'update', 'read'], orm, check: {runs: 8, states: 10, probes: true}})
  expect(x.refusals).toEqual([])
  expect(x.invariants!.length).toBeGreaterThan(0)
  expect(proveRule(x.rule!, x.invariants!)).toMatchObject({proven: true, checked: true})
}, 30000)

test('exported service method executes the actual class', () => {
  const x = extract(file, {entry: 'Service.create', orm, check: {runs: 8, depth: 3, states: 15}})
  expect(x.refusals).toEqual([])
  expect(x.evidence!.requests).toBeGreaterThan(0)
})

test('refuses generator, rest, client shadowing and custom constructor', () => {
  for (const entry of ['generator', 'rest', 'alias', 'WithConstructor.create']) {
    expect(extract(file, {entry, orm}).ok).toBe(false)
  }
})

test('schema spoofing and duplicate keys refuse', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-orm-ts-`)
  try {
    const handler = `${dir}/handler.ts`
    writeFileSync(handler, 'export async function create(db: any, id: string, amount: number) { await db.account.create({data: {id, amount}}) }')
    for (const schema of [
      '// model Account {\n// id String @id\n// amount Int\n// }',
      'model Account {\n id String @id\n amount Int @id\n}',
      'model Account {\n id String @id @id\n amount Int\n}',
      'model Account {\n id String @id\n amount Int @default(0)\n}',
      'model Account {\n id String @id\n amount Int\n}\nmodel Account {\n id String @id\n amount Int\n}',
    ]) {
      writeFileSync(`${dir}/schema.prisma`, schema)
      expect(extract(handler, {entry: 'create', orm}).ok).toBe(false)
    }
    writeFileSync(`${dir}/entity.ts`, 'function Entity() {}\nfunction Column() {}\nfunction PrimaryColumn() {}\n@Entity() class Account { @PrimaryColumn() id!: string; @Column() amount!: number }')
    expect(extract(handler, {entry: 'create', orm: {schema: 'entity.ts', model: 'Account', kind: 'typeorm'}}).ok).toBe(false)
  } finally { rmSync(dir, {recursive: true, force: true}) }
})

test('harness snapshots isolate rows, prototype keys and duplicate creates', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-orm-harness-`)
  try {
    const input = `${dir}/in`, output = `${dir}/out`
    const leaf = {name: 'Account', key: 'str', orm: {key: 'id', fields: [{name: 'id', t: {k: 'str'}}, {name: 'amount', t: {k: 'int'}}, {name: 'active', t: {k: 'bool'}}]}}
    const state = JSON.parse('{"Account":{"__proto__":{"amount":"7","active":true}}}')
    const args = [['id', {in: '__proto__'}], ['amount', {in: 9}], ['active', {in: false}]]
    const requests = [{op: 'hello', path: file, kind: 'prisma', model: 'Account', leaves: [leaf]}, {op: 'at', state}, {op: 'at', state}, {op: 'call', id: 1, m: 'create', a: args}, {op: 'call', id: 1, m: 'update', a: args.slice(0, 2)}, {op: 'get', id: 1}, {op: 'get', id: 2}, {op: 'at', state: {Account: {bad: {amount: '1', active: true, extra: 3}}}}]
    writeFileSync(input, requests.map(x => JSON.stringify(x)).join('\n') + '\n')
    const run = spawnSync('bun', [new URL('./orm/harness.js', import.meta.url).pathname, input, output], {encoding: 'utf8'})
    expect(run.status).toBe(0)
    const out = readFileSync(output, 'utf8').trim().split('\n').map(s => JSON.parse(s))
    expect(out[3].err).toContain('duplicate key')
    expect(out[4].err).toBeUndefined()
    expect(out[5].state.Account['__proto__'].amount).toBe('9')
    expect(out[6].state).toEqual(state)
    expect(out[7].error).toContain('invalid ORM cell')
  } finally { rmSync(dir, {recursive: true, force: true}) }
})

test('non-key updates refuse', () => {
  const x = extract(file, {entry: 'bad', orm})
  expect(x.ok).toBe(false)
  expect(x.refusals[0]!.what).toContain('primary key')
})
