import {expect, test} from 'bun:test'
import {type Machine, type State, cpair, interpret, loadJs} from '../../../core/machine.ts'
import {allowed} from '../../../core/watch.ts'
import {scope} from '../../../kernel/kernel.ts'
import {protocols} from './models.ts'

const ids = ['lock_server', 'lockserv', 'lockserv_automaton', 'simple_decentralized_lock', 'simple', 'simple_regular', 'simple_election', 'firewall']
const protocol = (id: string) => protocols.find(p => p.id === id)!
const machine = (id: string, broken = false) => { const p = protocol(id); return p.make(broken ? p.bug : undefined).machine }
const cell = (m: Machine, s: State, name: string, key: number) => s.maps[name]?.get(key) ?? s.defaults?.[name] ?? m.maps?.[name] ?? 0
const trace = (id: string, params: Record<string, number>, inputs: Record<string, number | Map<number, number>>[], broken = false) => {
  const m = machine(id, broken), run = interpret(m)
  let s = run.init(params)
  for (const input of inputs) { expect(allowed(m, run, params, s, input)).toBe(true); s = run.step(params, s, input) }
  return {m, s}
}

test('all eight machines are scoped and original safety laws have symbolic params, no literal cap', () => {
  for (const id of ids) for (const broken of [false, true]) {
    const p = protocol(id), r = p.make(broken ? p.bug : undefined), m = r.machine
    expect(m.params!.length).toBeGreaterThan(0)
    // Public existential laws are lowered by proveRule, not by the low-level machine scope checker.
    scope(m, [])
    const visit = (x: unknown): void => {
      if (typeof x === 'number') expect(x).not.toBe(64)
      if (x && typeof x === 'object') Object.values(x).forEach(visit)
    }
    visit(m); visit(p.laws(r))
  }
})

test('lock-server collision at server 64 is absent in both runtimes', () => {
  const m = machine('lock_server'), params = {clients: 2, servers: 65}
  for (const run of [interpret(m), loadJs(m)]) {
    let s = run.init(params)
    for (const input of [{op: 0, c: 0, s: 64}, {op: 0, c: 0, s: 0}]) s = run.step(params, s, input)
    expect(cell(m, s, 'Link', cpair(0, 64))).toBe(1)
    expect(cell(m, s, 'Link', cpair(0, 0))).toBe(1)
    expect(cell(m, s, 'Link', cpair(1, 0))).toBe(0)
  }
})

test('both lock server variants admit node 64 and retain their broken transition', () => {
  for (const [id, ops] of [['lockserv', [0, 1, 2]], ['lockserv_automaton', [0, 2, 3]]] as const) {
    const good = trace(id, {size: 65}, ops.map(op => ({op, n: 64})))
    expect(cell(good.m, good.s, 'HoldsLock', 64)).toBe(1)
    const bad = trace(id, {size: 65}, [0, 64].flatMap(n => ops.map(op => ({op, n}))), true)
    expect(cell(bad.m, bad.s, 'HoldsLock', 0)).toBe(1)
    expect(cell(bad.m, bad.s, 'HoldsLock', 64)).toBe(1)
  }
})

test('decentralized transfer across old radix boundary preserves and breaks exactly one lock', () => {
  for (const broken of [false, true]) {
    const {m, s} = trace('simple_decentralized_lock', {size: 65}, [0, 1, 2].map(op => ({op, src: 0, dst: 64})), broken)
    expect(cell(m, s, 'HasLock', 64)).toBe(1)
    expect(cell(m, s, 'HasLock', 0)).toBe(broken ? 1 : 0)
    expect(cell(m, s, 'Message', cpair(0, 64))).toBe(0)
  }
})

test('ring ports admit arbitrary positive size, including predecessor wrap at 65', () => {
  for (const regular of [false, true]) {
    const id = regular ? 'simple_regular' : 'simple'
    const inputs = [{op: 0, self: 64, v: 0}, ...(regular ? [{op: 1, self: 64, v: 0}] : []),
      {op: 0, self: 0, v: 0}, ...(regular ? [{op: 1, self: 0, v: 0}] : []), {op: 2, self: 0, v: 1}]
    const {m, s} = trace(id, {n: 65}, inputs)
    expect(cell(m, s, 'Pc', 0)).toBe(regular ? 3 : 2)
    expect(cell(m, s, 'Y', 0)).toBe(1)
  }
})

test('election counts an actual majority of 65 acceptors for proposer 65', () => {
  const {m, s} = trace('simple_election', {size: 65, proposers: 66}, [
    {op: 0, a: 0, p: 65, Q: new Map()},
    ...Array.from({length: 33}, (_, a) => ({op: 1, a, p: 65, Q: new Map<number, number>()})),
    {op: 2, a: 0, p: 65, Q: new Map(Array.from({length: 33}, (_, a) => [a, 1]))},
  ])
  expect(cell(m, s, 'Leader', 65)).toBe(1)
  expect(cell(m, s, 'Promise', cpair(65, 32))).toBe(1)
  expect(cell(m, s, 'Promise', cpair(64, 32))).toBe(0)
})

test('firewall tuple directions do not alias above 64', () => {
  const {m, s} = trace('firewall', {size: 65}, [
    {op: 0, s: 64, d: 0}, {op: 1, s: 64, d: 0}, {op: 2, s: 64, d: 0}, {op: 3, s: 0, d: 64},
  ])
  expect(cell(m, s, 'Sent', cpair(64, 0))).toBe(1)
  expect(cell(m, s, 'Sent', cpair(0, 64))).toBe(1)
  expect(cell(m, s, 'Sent', cpair(1, 0))).toBe(0)
})

test('empty and boundary-sized domains refuse out-of-domain identities', () => {
  for (const id of ['lockserv', 'lockserv_automaton', 'simple_decentralized_lock', 'firewall']) {
    const m = machine(id), run = interpret(m)
    for (const size of [0, 65]) {
      const params = {size}, input = {op: 0, n: size, src: size, dst: 0, s: size, d: 0}
      expect(allowed(m, run, params, run.init(params), input)).toBe(false)
    }
  }
})
