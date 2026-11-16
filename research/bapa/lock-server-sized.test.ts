import {expect, test} from 'bun:test'
import {type Machine, type State, cpair, interpret, loadJs} from '../../core/machine.ts'
import {allowed} from '../../core/watch.ts'
import {checkLaws, scope} from '../../kernel/kernel.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {protocols} from '../protocols/ic3syn/models.ts'
import {lockServerSized, lockServerSizedLaws, lockServerUnrestrictedLaws} from './lock-server-sized.ts'

const cell = (m: Machine, st: State, map: string, key: number) => st.maps[map]!.get(key) ?? st.defaults?.[map] ?? m.maps![map]!
const projection = (m: Machine, st: State, pair: (c: number, s: number) => number, clients: number, servers: number) => [
  Array.from({length: servers}, (_, s) => cell(m, st, 'Semaphore', s)),
  Array.from({length: clients}, (_, c) => Array.from({length: servers}, (_, s) => cell(m, st, 'Link', pair(c, s)))),
]

test('symbolic original safety, helper given not found, is checked without counts', () => {
  const r = lockServerSized(), m = r.machine, laws = [...r.kindLaws(), ...lockServerSizedLaws(r)]
  expect(m.params).toEqual(['clients', 'servers'])
  expect(m.pre).toBeUndefined()
  expect(m.counts).toBeUndefined()
  expect(m.relations).toEqual({Link: ['Client', 'Server']})
  scope(m, laws)
  const out = proveLaws(m, laws)
  expect(out).toMatchObject({proven: true, checked: true})
  expect(out.proof).toBeDefined()
  expect(checkLaws(m, laws, out.proof!)).toBe(true)
  const bad = lockServerSized(true)
  expect(checkLaws(bad.machine, [...bad.kindLaws(), ...lockServerSizedLaws(bad)], out.proof!)).toBe(false)
}, 60_000)

test('stronger unguarded uniqueness is also proved, helper given not found', () => {
  const r = lockServerSized(), laws = [...r.kindLaws(), ...lockServerUnrestrictedLaws(r)]
  const out = proveLaws(r.machine, laws)
  expect(out).toMatchObject({proven: true, checked: true})
  expect(out.proof).toBeDefined()
  expect(checkLaws(r.machine, laws, out.proof!)).toBe(true)
}, 60_000)

test('all 2x2 reachable states and transitions match the canonical tuple port', () => {
  const oldRule = protocols.find(p => p.id === 'lock_server')!.make(), old = oldRule.machine
  const fresh = lockServerSized().machine, a = interpret(old), b = interpret(fresh), params = {clients: 2, servers: 2}
  const projectA = (st: State) => projection(old, st, cpair, 2, 2)
  const projectB = (st: State) => projection(fresh, st, cpair, 2, 2)
  const queue: [State, State][] = [[a.init(params), b.init(params)]], seen = new Set<string>()
  for (let i = 0; i < queue.length; i++) {
    const [sa, sb] = queue[i]!, key = JSON.stringify(projectA(sa))
    if (seen.has(key)) continue
    seen.add(key)
    expect(projectB(sb)).toEqual(projectA(sa))
    for (const op of [0, 1]) for (const c of [0, 1]) for (const s of [0, 1]) {
      const input = {op, c, s}
      expect(allowed(fresh, b, params, sb, input)).toBe(allowed(old, a, params, sa, input))
      const na = a.step(params, sa, input), nb = b.step(params, sb, input)
      expect(projectB(nb)).toEqual(projectA(na))
      queue.push([na, nb])
    }
    expect(seen.size).toBeLessThanOrEqual(9)
  }
  expect(seen.size).toBe(9)
})

test('sizes beyond 64 use distinct native tuple keys and both runtimes agree', () => {
  const m = lockServerSized().machine, a = interpret(m), b = loadJs(m), p = {clients: 130, servers: 201}
  let sa = a.init(p), sb = b.init(p)
  for (const input of [{op: 0, c: 64, s: 200}, {op: 0, c: 129, s: 200}, {op: 1, c: 129, s: 200}, {op: 1, c: 64, s: 200}, {op: 0, c: 129, s: 200}]) {
    sa = a.step(p, sa, input); sb = b.step(p, sb, input)
    expect(projection(m, sb, cpair, 130, 201)).toEqual(projection(m, sa, cpair, 130, 201))
  }
  expect(cell(m, sa, 'Link', cpair(64, 200))).toBe(0)
  expect(cell(m, sa, 'Link', cpair(129, 200))).toBe(1)
  expect(cell(m, sa, 'Semaphore', 200)).toBe(0)
})

test('empty sorts admit no request, and missing-semaphore mutant has the original failure', () => {
  const r = lockServerSized(), m = r.machine, run = interpret(m)
  for (const p of [{clients: 0, servers: 1}, {clients: 1, servers: 0}, {clients: 0, servers: 0}])
    expect(allowed(m, run, p, run.init(p), {op: 0, c: 0, s: 0})).toBe(false)
  const bad = lockServerSized(true).machine, badRun = interpret(bad), p = {clients: 2, servers: 1}
  let st = badRun.init(p)
  for (const c of [0, 1]) st = badRun.step(p, st, {op: 0, c, s: 0})
  expect(cell(bad, st, 'Link', cpair(0, 0))).toBe(1)
  expect(cell(bad, st, 'Link', cpair(1, 0))).toBe(1)
})
