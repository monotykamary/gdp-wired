import {expect, test} from 'bun:test'
import {type C, type Machine, type State, cpair, interpret} from '../../core/machine.ts'
import {allowed} from '../../core/watch.ts'
import {historicalLockServer} from './fixtures/lock-server-pre-symbolic.ts'
import {lockServerSized} from './lock-server-sized.ts'

// Change only domain guards, not the radix coefficients or the state machine.
// This is a negative control, deliberately NOT a proposed migration.
function growGuard(c: C): C {
  if (c.op === 'and' || c.op === 'or') return {...c, xs: c.xs.map(growGuard)}
  if (c.op === 'not') return {...c, x: growGuard(c.x)}
  if (c.op === '<' && c.b.op === 'const' && c.b.value === 64) return {...c, b: {op: 'const', value: 65}}
  return c
}
const cell = (m: Machine, s: State, map: string, key: number) => s.maps[map]!.get(key) ?? s.defaults?.[map] ?? m.maps![map]!
const pack = (c: number, s: number) => 64 * c + s

test('historical fixed-radix cap erasure admits a two-request mutex counterexample', () => {
  const old = historicalLockServer().machine
  const originalBytes = JSON.stringify(old)
  const grown: Machine = {...old, assume: growGuard(old.assume!)}
  const original = interpret(old), run = interpret(grown)
  const first = {op: 0, c: 0, s: 64}, second = {op: 0, c: 0, s: 0}
  expect(allowed(old, original, {}, original.init({}), first)).toBe(false)
  let state = run.init({})
  for (const request of [first, second]) {
    expect(allowed(grown, run, {}, state, request)).toBe(true)
    state = run.step({}, state, request)
  }
  expect(pack(0, 64)).toBe(pack(1, 0))
  expect(cell(grown, state, 'Link', pack(0, 0))).toBe(1)
  expect(cell(grown, state, 'Link', pack(1, 0))).toBe(1)
  expect(JSON.stringify(old)).toBe(originalBytes)
})

test('native tuple domains do not have the fixed-radix counterexample', () => {
  const m = lockServerSized().machine, run = interpret(m), params = {clients: 2, servers: 65}
  let state = run.init(params)
  for (const request of [{op: 0, c: 0, s: 64}, {op: 0, c: 0, s: 0}]) {
    expect(allowed(m, run, params, state, request)).toBe(true)
    state = run.step(params, state, request)
  }
  expect(cpair(0, 64)).not.toBe(cpair(1, 0))
  expect(cell(m, state, 'Link', cpair(0, 0))).toBe(1)
  expect(cell(m, state, 'Link', cpair(1, 0))).toBe(0)
})

test('retained inventory is 29 cases and 67 declarations, never a claimed cutoff', async () => {
  const inventory: {
    status: string, protocols: number, theoremDeclarations: number, obligations: number,
    rows: {id: string, theorems: string[], cutoff: null, coveredBy64: null, obligations: unknown[]}[],
  } = await Bun.file(new URL('./cutoff-inventory.json', import.meta.url)).json()
  expect(inventory.status).toBe('STOP_UNPROVED_TRANSPORT')
  expect(inventory.protocols).toBe(29)
  expect(new Set(inventory.rows.map(row => row.id)).size).toBe(29)
  expect(inventory.theoremDeclarations).toBe(67)
  expect(inventory.rows.flatMap(row => row.theorems)).toHaveLength(67)
  expect(new Set(inventory.rows.flatMap(row => row.theorems)).size).toBe(67)
  expect(inventory.rows.flatMap(row => row.obligations)).toHaveLength(897)
  expect(inventory.obligations).toBe(897)
  for (const row of inventory.rows) {
    expect(row.cutoff).toBeNull()
    expect(row.coveredBy64).toBeNull()
  }
})
