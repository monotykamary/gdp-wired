import {expect, test} from 'bun:test'
import {type Machine, type State, interpret} from '../../core/machine.ts'
import {allowed} from '../../core/watch.ts'
import {scope} from '../../kernel/kernel.ts'
import {protocols, tk} from '../protocols/ic3syn/models.ts'

const ids = ['tcommit', 'twophase', 'two_phase_commit', 'client_server_ae', 'client_server_db_ae', 'learning_switch', 'learning_switch_i4']
const get = (id: string) => protocols.find(p => p.id === id)!
const cell = (m: Machine, st: State, map: string, ...key: number[]) => st.maps[map]!.get(tk(...key)) ?? st.defaults?.[map] ?? m.maps![map]!

for (const id of ids) test(`${id}: symbolic sizes, scoped machine, same broken branch`, () => {
  const p = get(id), r = p.make(), m: Machine = r.machine
  expect(m.params!.length).toBeGreaterThan(0)
  // .sorts labels are search hints, not emitted Machine fields. The actual
  // domain semantics reside in parameter-dependent guards and tuple updates.
  if (id.includes('client_server') || id.includes('learning_switch'))
    expect(Object.values(m.relations ?? {}).some(sorts => sorts.length > 1)).toBe(true)
  expect(m.counts).toBeUndefined()
  expect(m.facts).toBeUndefined()
  // No legacy radix or ceiling may remain anywhere in the emitted machine/laws.
  const visit = (x: unknown) => {
    if (!x || typeof x !== 'object') return
    if ('op' in x && x.op === 'const' && 'value' in x) expect(x.value).not.toBe(64)
    if ('op' in x && x.op === 'mul' && 'k' in x) expect(x.k).not.toBe(64)
    for (const v of Object.values(x)) visit(v)
  }
  visit(m); visit(p.laws(r))
  scope(m)
  // Universal-existential safety is lowered by proveRule, not by scope.
  scope(m, p.laws(r).filter(law => !law.some?.length))
  expect(JSON.stringify(p.make(p.bug).machine)).not.toBe(JSON.stringify(m))
})

for (const [id, map] of [['tcommit', 'St'], ['twophase', 'Rm']] as const) test(`${id}: RM 64 can prepare`, () => {
  const m = get(id).make().machine, run = interpret(m), params = {size: 65}, st = run.init(params)
  const input = {op: id === 'tcommit' ? 0 : 3, rm: 64}
  expect(allowed(m, run, params, st, input)).toBe(true)
  expect(cell(m, run.step(params, st, input), map, 64)).toBe(1)
  expect(allowed(m, run, params, st, {...input, rm: 65})).toBe(false)
})

test('two_phase_commit: Node 64 votes, no upper ceiling', () => {
  const m = get('two_phase_commit').make().machine, run = interpret(m), params = {size: 65}, st = run.init(params), input = {op: 0, n: 64, w: 0}
  expect(allowed(m, run, params, st, input)).toBe(true)
  expect(cell(m, run.step(params, st, input), 'VoteYes', 64)).toBe(1)
})

for (const id of ['client_server_ae', 'client_server_db_ae']) test(`${id}: distinct tuple identities beyond the old radix`, () => {
  const m = get(id).make().machine, run = interpret(m), params = {nodes: 2, requestSize: 65, responses: 66, ...(id.endsWith('db_ae') ? {ids: 67} : {})}
  let st = run.init(params)
  const request = {op: 0, n: 0, r: 0, p: 64, i: 66}
  expect(allowed(m, run, params, st, request)).toBe(true)
  st = run.step(params, st, request)
  expect(cell(m, st, 'Match', 0, 64)).toBe(1)
  expect(cell(m, st, 'Match', 1, 0)).toBe(0)
  st = run.step(params, st, {...request, r: 64, p: 65})
  expect(cell(m, st, 'Match', 64, 65)).toBe(1)
  expect(allowed(m, run, params, st, {...request, r: 65})).toBe(false)
  expect(allowed(m, run, params, st, {...request, p: 66})).toBe(false)
  if (id.endsWith('db_ae')) expect(allowed(m, run, params, st, {...request, i: 67})).toBe(false)
})

test('learning_switch: Node 64 emits its packet with native quadruple identity', () => {
  const m = get('learning_switch').make().machine, run = interpret(m), params = {size: 65}, st = run.init(params)
  const input = {op: 0, ps: 64, pd: 0, sw0: 0, sw1: 0, nondet: 0}
  expect(allowed(m, run, params, st, input)).toBe(true)
  expect(cell(m, run.step(params, st, input), 'P', 64, 0, 64, 64)).toBe(1)
}, 60_000)

test('learning_switch_i4: Packet and Node sizes independently exceed the old cap', () => {
  const m = get('learning_switch_i4').make().machine, run = interpret(m), params = {size: 66, packets: 65}, st = run.init(params)
  const input = {op: 0, p: 64, sw0: 65, sw1: 0, sw2: 0}
  expect(allowed(m, run, params, st, input)).toBe(true)
  const next = run.step(params, st, input)
  expect(cell(m, next, 'Src', 64)).toBe(65)
  expect(cell(m, next, 'SrcSet', 64)).toBe(1)
  expect(allowed(m, run, params, st, {...input, p: 65})).toBe(false)
  expect(allowed(m, run, params, st, {...input, sw0: 66})).toBe(false)
}, 60_000)
