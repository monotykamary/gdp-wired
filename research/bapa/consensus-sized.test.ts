import {expect, test} from 'bun:test'
import {type Machine, type Request, type State, cpair, interpret, loadJs, walk} from '../../core/machine.ts'
import {allowed} from '../../core/watch.ts'
import {scope} from '../../kernel/kernel.ts'
import {protocols} from '../protocols/ic3syn/models.ts'

const ids = ['consensus', 'consensus_epr', 'consensus_forall', 'consensus_wo_decide', 'toy_consensus', 'toy_consensus_epr', 'toy_consensus_forall', 'naive_consensus']
const cell = (m: Machine, s: State, name: string, key: number) => s.maps[name]?.get(key) ?? s.defaults?.[name] ?? m.maps?.[name] ?? 0

for (const id of ids) test(`${id}: symbolic sorts, no cap/radix, original safety only`, () => {
  const p = protocols.find(p => p.id === id)!, r = p.make(), m = r.machine
  expect(m.params).toEqual(id === 'consensus' ? ['values'] : id === 'consensus_wo_decide' ? ['size'] : ['size', 'values'])
  expect(m.pre).toBeUndefined()
  expect(p.laws(r)).toHaveLength(1)
  scope(m, [...r.kindLaws(), ...p.laws(r)])
  walk([m, p.laws(r)], o => {
    expect(o.op === 'const' && o.value === 64).toBe(false)
    expect(o.op === 'mul' && o.k === 64).toBe(false)
  })
  if (id === 'toy_consensus_epr' || id === 'naive_consensus') expect(m.relations).toEqual({Vote: ['Value', 'Node']})
  if (id.startsWith('consensus_')) {
    expect(m.relations?.Votes).toEqual(['Node', 'Node'])
    if (id !== 'consensus_wo_decide') expect(m.relations?.Decided).toEqual(['Node', 'Value'])
  }
})

// Exercise actual high identities and majority cardinalities, not just an AST
// cap deletion. The interpreter supports counted/native-tuple flags; compileJs
// currently refuses those, so compare the compiled runtime for consensus only.
// Each original bug gets a bad run.
for (const id of ids) for (const broken of [false, true]) test(`${id}: size 66 positive/broken=${broken}`, () => {
  const p = protocols.find(p => p.id === id)!, m = p.make(broken ? p.bug : undefined).machine
  const params = {size: 66, values: 66}, a = interpret(m), b = id === 'consensus' ? loadJs(m) : undefined
  let sa = a.init(params), sb = b?.init(params)
  const step = (q: Request) => {
    expect(allowed(m, a, params, sa, q)).toBe(true)
    sa = a.step(params, sa, q)
    if (b && sb) {
      sb = b.step(params, sb, q)
      for (const name of Object.keys(m.maps ?? {})) {
        const keys = new Set([...sa.maps[name]!.keys(), ...sb.maps[name]!.keys()])
        for (const key of keys) expect(cell(m, sa, name, key)).toBe(cell(m, sb, name, key))
      }
      expect(sb.scalars).toEqual(sa.scalars)
    }
  }
  const Q = new Map(Array.from({length: 34}, (_, k) => [k + 32, 1]))
  if (id === 'consensus') {
    step({v: 64}); step({v: 65})
    expect(cell(m, sa, 'Chosen', 64)).toBe(1)
    expect(cell(m, sa, 'Chosen', 65)).toBe(Number(broken))
  } else if (id.startsWith('consensus_')) {
    const epr = id === 'consensus_epr', decides = id !== 'consensus_wo_decide', shift = epr ? 0 : 1
    const req = (op: number, i: number, j = i, v = 64) => step({op, i, j, v, nondet: 1, Q})
    if (!epr) req(0, 64)
    for (const leader of [64, 65]) {
      for (const voter of Q.keys()) {
        req(shift, leader, voter)
        req(shift + 1, voter, leader)
        req(shift + 2, leader, voter)
      }
      req(epr ? 3 : 5, leader)
      if (decides) req(epr ? 4 : 6, leader, leader, leader)
    }
    expect(cell(m, sa, 'Leader', 64)).toBe(1)
    expect(cell(m, sa, 'Leader', 65)).toBe(Number(broken))
    if (decides) {
      expect(cell(m, sa, 'Decided', cpair(64, 64))).toBe(1)
      expect(cell(m, sa, 'Decided', cpair(65, 65))).toBe(Number(broken))
    }
    // Distinct tuples at the old radix's collision, neither gets a ghost vote.
    expect(cell(m, sa, 'Votes', cpair(65, 0))).toBe(0)
  } else {
    for (const value of [64, 65]) {
      for (const node of Q.keys()) step({op: 0, i: node, n: node, v: value, Q})
      step({op: 1, i: 64, n: 64, v: value, Q})
      if (id === 'naive_consensus') step({op: 2, n: 64, v: value, Q})
    }
    const name = id === 'toy_consensus' || id === 'naive_consensus' ? 'Decision' : 'Decided'
    expect(cell(m, sa, name, 64)).toBe(1)
    expect(cell(m, sa, name, 65)).toBe(Number(broken))
    if (id === 'toy_consensus_epr' || id === 'naive_consensus') {
      expect(cell(m, sa, 'Vote', cpair(64, 64))).toBe(1)
      expect(cell(m, sa, 'Vote', cpair(65, 0))).toBe(0)
    }
  }
}, 60_000)

for (const id of ids) test(`${id}: empty input sort and endpoint are refused`, () => {
  const m = protocols.find(p => p.id === id)!.make().machine, r = interpret(m)
  const q = {op: 0, i: 0, j: 0, n: 0, v: 0, nondet: 0, Q: new Map([[0, 1]])}
  const empty: Record<string, number> = id === 'consensus' ? {values: 0} : {size: 0, values: 1}
  expect(allowed(m, r, empty, r.init(empty), q)).toBe(false)
  const params = {size: 66, values: 66}
  expect(allowed(m, r, params, r.init(params), id === 'consensus_wo_decide' ? {...q, i: 66} : {...q, v: 66})).toBe(false)
})
