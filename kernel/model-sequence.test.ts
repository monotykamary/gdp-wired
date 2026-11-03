import {expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, atMost, n, x} from '../core/machine.ts'
import {check, type Goal} from './kernel.ts'
import {clock, decideLaw, grow, modelInstances, proveSetFast, withStrict} from './prove.ts'
import {Cond, nat, proveDecision, proveRule, rule} from '../core/dsl.ts'
import {decideHook} from './epr.ts'
import {REFUTED} from './cdcl.ts'
import {modelSequence} from './model-sequence.ts'

test('growing model queries remap cores after insertion, reordering and duplication', () => {
  const ask = modelSequence(), lower=atMost(n(2),x('x')), upper=atMost(x('x'),n(1)), other=atMost(x('y'),n(4))
  expect(ask({name:'sequence',hyps:[other,lower]},clock()+5000)).toMatchObject({stuck:'sat'})
  const goal:Goal={name:'sequence',hyps:[lower,upper,other,lower]}
  const out=ask(goal,clock()+5000)
  expect(out).toMatchObject({why:REFUTED})
  expect(out.core?.length).toBeGreaterThan(0)
  expect(out.core!.every(i=>Number.isInteger(i)&&i>=0&&i<goal.hyps.length)).toBe(true)
  const part={...goal,hyps:out.core!.map(i=>goal.hyps[i]!)}
  const proof=grow(part,new Map(),{nodes:0,until:clock()+5000})
  expect('tree' in proof && check(part,proof.tree)).toBe(true)
  // A removed hypothesis must invalidate learned contradictions.
  expect(ask({name:'sequence',hyps:[other,lower]},clock()+5000)).toMatchObject({stuck:'sat'})
  // A changed bound is not the old expression, even under the same goal name.
  expect(ask({name:'sequence',hyps:[atMost(x('x'),n(3)),other,lower]},clock()+5000)).toMatchObject({stuck:'sat'})
})

const get = (map: string, key: E): E => ({op: 'get', map, key})
const ge = (a: E, b: E): C => ({op: '<=', a: b, b: a})
const src = get('Src', x('p'))
// Packet keys and node values are distinct sorts. A spurious Src[node] cell must not consume the atomic pass.
const m: Machine = {
  name: 'typed model refinement', params: ['size', 'packets'], inputs: ['p', 'node'], state: {}, maps: {Src: 0, R: 0, S: 0, T: 0}, step: {},
  assume: {op: 'and', xs: [
    {op: '<', a: x('node'), b: x('size')}, {op: '<', a: x('p'), b: x('packets')}, {op: '<', a: src, b: x('size')},
    ge(get('R', x('node')), n(0)), ge(get('T', {op: 'tup', a: x('node'), b: x('node')}), n(0)),
  ]},
}
const laws: Law[] = [
  {name: 'packet source range', forall: 'k', holds: {op: '<', a: get('Src', x('k')), b: x('size')}},
  {name: 'node support', forall: 'k', holds: {op: 'or', xs: [{op: '=', a: get('R', x('k')), b: n(0)}, ge(get('S', x('k')), n(1))]}},
]
const goal: Goal = {name: 'typed probe', hyps: [ge(get('R', src), n(0)), ge(get('R', x('node')), n(0))]}
const witness = {p: 4, node: 2, size: 10, packets: 5, 'Src[p:1]': 3, 'Src[node:1]': 11, 'R[Src[p:1]:1]': 1, 'S[Src[p:1]:1]': 0, 'R[node:1]': 0}

test('wrong-sort atomic proposals do not suppress a valid function-valued instance', () => {
  const out = modelInstances(m, laws, {}, goal, witness, undefined, true)
  expect(out?.['packet source range'] ?? []).toEqual([])
  expect(out?.['node support']).toEqual([src])
})

test('eligible atomic model additions still respect the global cap', () => {
  const out = modelInstances(m, laws, {}, goal, {...witness, 'R[node:1]': 1}, 1, true)
  expect(out?.['packet source range'] ?? []).toEqual([])
  expect(out?.['node support']).toEqual([x('node')])
  expect(Object.values(out ?? {}).reduce((sum, terms) => sum + terms.length, 0)).toBe(1)
  expect(modelInstances(m, laws, {}, goal, witness, 0, true)).toBeUndefined()
})

test('model refinement does not repeat existing eligible instances', () => {
  const inst = {'node support': [src]}
  expect(modelInstances(m, laws, inst, goal, witness, undefined, true)).toEqual(inst)
  expect(inst).toEqual({'node support': [src]})
})

test('unsorted model consumers retain their unfiltered refinement policy', () => {
  const out = modelInstances(m, laws, {}, goal, witness)
  expect(out?.['packet source range']).toEqual([x('node')])
  expect(out?.['node support']).toBeUndefined()
})

test('a sorted model with only ineligible new tuples returns an unchanged instance set', () => {
  const out = modelInstances(m, laws, {}, goal, {...witness, 'R[Src[p:1]:1]': 0}, undefined, true)
  expect(out).toEqual({})
})

test('strict decisions do not answer from a model broken only at another sort', () => {
  const target: Law = {name: 'strict sort-only target', holds: {op: '=', a: x('ok'), b: n(0)}}
  const machine: Machine = {...m, name: 'strict sort-only model', state: {ok: n(0)}, step: {state: {ok: n(1)}}, pre: {op: '<', a: n(0), b: x('size')}}
  const before = decideHook.on
  let models = 0
  decideHook.on = (g, d, ms, shaped) => {
    before?.(g, d, ms, shaped)
    if (g.name !== `${target.name} @step` || !('sat' in d) || !d.sat) return
    models++
    // The unconstrained Node cell is not a Packet instance. All eligible instances hold.
    for (const k of Object.keys(d.witness)) delete d.witness[k]
    Object.assign(d.witness, witness, {'R[Src[p:1]:1]': 0, ok: 0})
  }
  try {
    const out = withStrict(() => decideLaw(machine, [...laws, target], laws.length))
    expect(models).toBeGreaterThan(0)
    expect(out).toBeUndefined()
  } finally { decideHook.on = before }
})

for (const confirmed of [false, true]) test(confirmed ? 'confirmed strict models remain reusable by both callers' : 'ordinary cached models remain unavailable to strict decisions', () => {
  const target: Law = {name: `cache origin target ${confirmed}`, holds: {op: '=', a: x('ok'), b: n(0)}}
  const machine: Machine = {...m, name: `cache origin model ${confirmed}`, state: {ok: n(0)}, step: {state: {ok: n(1)}}, pre: {op: '<', a: n(0), b: x('size')}}
  const set = [target, ...laws], before = decideHook.on
  let models = 0
  decideHook.on = (g, d, ms, shaped) => {
    before?.(g, d, ms, shaped)
    if (g.name !== `${target.name} @step` || !('sat' in d) || !d.sat) return
    models++
    for (const k of Object.keys(d.witness)) delete d.witness[k]
    Object.assign(d.witness, witness, {'R[Src[p:1]:1]': 0, 'Src[node:1]': confirmed ? 0 : 11, ok: 0})
  }
  try {
    const first = confirmed ? withStrict(() => decideLaw(machine, set, 0)) : proveSetFast(machine, set)
    expect(first?.proven).toBe(false)
    const asked = models
    expect(asked).toBeGreaterThan(0)
    // Ordinary callers keep their old cache policy, including unconfirmed models.
    expect(proveSetFast(machine, set).proven).toBe(false)
    expect(models).toBe(asked)
    const strict = withStrict(() => decideLaw(machine, set, 0))
    if (confirmed) {
      expect(strict).toMatchObject({proven: false, stuck: 'sat'})
      expect(models).toBe(asked)
    } else {
      expect(strict).toBeUndefined()
      expect(models).toBeGreaterThan(asked)
    }
  } finally { decideHook.on = before }
})

test('public fast proveRule cache does not contaminate strict decisions', () => {
  const target: Law = {name: 'public cache target', holds: {op: '=', a: x('ok'), b: n(0)}}
  // The sampled parameter range cannot enter this rule, so the public prover reaches its symbolic path.
  const r = rule('public cache origin').params({size: nat, packets: nat}).inputs({p: nat, node: nat})
    .state({ok: 0}).maps({Src: 0, R: 0, S: 0, T: 0}).pre(({size}) => size.gt(100))
    .assume(() => new Cond(m.assume!)).step(() => ({ok: 1}))
  const set = [target, ...laws], before = decideHook.on
  let models = 0
  decideHook.on = (g, d, ms, shaped) => {
    before?.(g, d, ms, shaped)
    if (g.name !== `${target.name} @step` || !('sat' in d) || !d.sat) return
    models++
    for (const k of Object.keys(d.witness)) delete d.witness[k]
    Object.assign(d.witness, witness, {size: 1000, 'Src[node:1]': 1001, 'R[Src[p:1]:1]': 0, ok: 0})
  }
  try {
    const raw = proveRule(r as never, set, {fast: true, search: false})
    expect(raw).toMatchObject({proven: false, checked: false, stuck: 'sat', witness: {'Src[node:1]': 1001}})
    expect(raw.run).toBeUndefined()
    const asked = models
    expect(asked).toBeGreaterThan(0)
    expect(proveRule(r as never, set, {fast: true, search: false}).witness).toEqual(raw.witness)
    expect(models).toBe(asked)
    // A plain public decision uses grow, not the law-decision memo, and remains independently checked.
    expect(proveDecision(r.decide('public cache independent decision', () => [], ({node}) => node.atMost(node)))).toMatchObject({proven: true, checked: true})
    const all = [...r.kindLaws(), ...set]
    expect(withStrict(() => decideLaw(r.withSumsOf(set).machine, all, all.indexOf(target)))).toBeUndefined()
    expect(models).toBeGreaterThan(asked)
  } finally { decideHook.on = before }
})
