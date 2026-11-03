import {expect, setDefaultTimeout, test} from 'bun:test'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {check} from './cli.ts'
import {securityLaws} from './security.ts'

setDefaultTimeout(120_000)
const file = (source: string) => {
  const dir = mkdtempSync(`${tmpdir()}/security-law-`), path = `${dir}/app.ts`
  writeFileSync(path, source)
  return path
}
const run = async (source: string, security = false) => check([file(source)], {ms: 8000, propose: false, security})

// Deliberately vulnerable training code only. No third-party vulnerability inferred from these.
test('authorization candidates are reviewed policy, never extra assumptions; a stated law breaks with a real run', async () => {
  const body = `export class Vault {
    balance = 0;
    // gdp: law only an admin credits: balance != old(balance) implies admin
    credit(admin: boolean, amount: number): boolean { this.balance += amount; return true; }
  }`
  const r = await run(body, true), law = r.rules[0]!.laws[0]!
  expect(r.exit).toBe(1)
  expect(law.verdict).toBe('broken')
  expect(law.run?.join(' ')).toContain('admin=false')
  expect(r.rules[0]!.security?.some(l => l.securityKind === 'authorization' && l.verdict === 'broken')).toBe(true)
  expect(r.rules[0]!.security?.every(l => l.review === 'required')).toBe(true)
  const fixed = await run(body.replace('this.balance += amount;', 'if (!admin) return false; this.balance += amount;'))
  expect(fixed.rules[0]!.laws[0]!.verdict).toBe('proven')
})

test('a broken candidate alone is not a claimed vulnerability or a failing policy', async () => {
  const r = await run(`export class Counter { value = 0; hit(allowed: boolean) { this.value++; } }`, true)
  expect(r.exit).toBe(0)
  expect(r.rules[0]!.security?.some(l => l.verdict === 'broken')).toBe(true)
  expect((await run(`export class Counter { value = 0; hit(allowed: boolean) { this.value++; } }`)).rules[0]!.security).toBeUndefined()
})

test('workflow checks the prerequisite BEFORE the effect, not a flag set by the bypass', async () => {
  const [law] = securityLaws({kind: 'workflow', name: 'approved first', effect: 'shipped', prerequisite: 'approved'})
  const body = `export class Order { approved = false; shipped = false; approve() { this.approved = true; }
    // gdp: law ${law!.name}: ${law!.expr}
    ship() { this.approved = true; this.shipped = true; }
  }`
  expect((await run(body)).rules[0]!.laws[0]!.verdict).toBe('broken')
  expect((await run(body.replace('this.approved = true; this.shipped = true;', 'if (this.approved) this.shipped = true;'))).rules[0]!.laws[0]!.verdict).toBe('proven')
})

test('quota and ledger laws cover adversarial negative costs as well as over-limit credits', async () => {
  const laws = [
    ...securityLaws({kind: 'quota', name: 'cap', used: 'used', limit: 'limit'}),
    ...securityLaws({kind: 'ledger', name: 'no negative', balance: 'used'}),
  ].map(l => `// gdp: law ${l.name}: ${l.expr}`).join('\n')
  const body = `export class Budget { used = 0; constructor(readonly limit: number) { if (limit < 0) throw new Error('negative limit'); }\n${laws}\nspend(cost: number) { this.used += cost; } }`
  const broken = await run(body)
  expect(broken.rules[0]!.laws.map(l => l.verdict)).toEqual(['broken', 'broken'])
  const safe = await run(body.replace('this.used += cost;', 'if (cost >= 0 && this.used + cost <= this.limit) this.used += cost;'))
  expect(safe.rules[0]!.laws.map(l => l.verdict)).toEqual(['proven', 'proven'])
})

test('tenant isolation templates cover creation, updates and deletion including a zero-valued foreign row', async () => {
  const laws = securityLaws({kind: 'isolation', name: 'own rows only', map: 'rows', identity: 'tenant', fields: ['value']})
  expect(laws).toHaveLength(2)
  const comments = laws.map(l => `// gdp: law ${l.name}: ${l.expr}`).join('\n')
  const body = `export class Rows { rows = new Map<string, number>();\n${comments}\nput(tenant: string, target: string, value: number) { this.rows.set(target, value); } }`
  const r = await run(body)
  expect(r.rules[0]!.laws[0]!.verdict).toBe('broken')
  const fixed = await run(body.replace('this.rows.set(target, value);', 'if (tenant === target) this.rows.set(target, value);'))
  expect(fixed.rules[0]!.laws.map(l => l.verdict)).toEqual(['proven', 'proven'])
  const deletion = `export class Rows { rows = new Map<string, number>();
    put(tenant: string, target: string, value: number) { this.rows.set(tenant, 0); }
    ${comments}
    remove(tenant: string, target: string, value: number) { this.rows.delete(target); }
  }`
  const del = await run(deletion)
  expect(del.rules[0]!.laws[1]!.verdict).toBe('broken')
})

test('read isolation is two-run noninterference, not absence of foreign writes', async () => {
  const [l] = securityLaws({kind: 'isolation', name: 'private reads', identity: 'tenant', seeing: 'result'})
  const source = `export class Rows { rows = new Map<string, number>();
    put(tenant: string, value: number) { this.rows.set(tenant, value); }
    // gdp: law ${l!.name}: ${l!.expr}
    read(tenant: string, target: string): number { return this.rows.get(target) ?? 0; }
  }`
  const bad = await run(source)
  expect(bad.rules[0]!.laws[0]!.verdict).toBe('broken')
  const good = await run(source.replace('this.rows.get(target)', 'this.rows.get(tenant)'))
  expect(good.rules[0]!.laws[0]!.verdict).toBe('proven')
})

test('security mode refuses unsupported concurrency rather than proving the atomic handler', async () => {
  const source = `export class Counter { value = 0; hit(allowed: boolean) { if (allowed) this.value++; } }`
  const r = await check([file(source)], {propose: false, security: true, ms: 3000, env: 'read committed'})
  expect(r.exit).toBe(2)
  expect(r.rules[0]!.ok).toBe(false)
  expect(r.rules[0]!.refusals[0]!.what).toContain('environment')
  expect(r.rules[0]!.security).toBeUndefined()
  expect(r.rules[0]!.env).toBeUndefined()
})

test('a bound key cannot shadow the identity and make isolation vacuous', () => {
  expect(() => securityLaws({kind: 'isolation', name: 'bad', map: 'rows', identity: 'securityKey', fields: ['value']})).toThrow(/fresh/)
  expect(() => securityLaws({kind: 'isolation', name: 'bad', map: 'rows', identity: 'tenant', key: 'tenant', fields: ['value']})).toThrow(/fresh/)
})

test('bad policy names and unsupported code are refused, never proven', async () => {
  const r = await run(`export class Counter { value = 0;
    // gdp: law missing identity: value != old(value) implies administrator
    hit() { this.value++; }
  }`, true)
  expect(r.rules[0]!.laws[0]!.verdict).toBe('not read')
  expect(r.exit).toBe(2)
})
