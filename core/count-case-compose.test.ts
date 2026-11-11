import {expect, test} from 'bun:test'
import {type Law, type Machine, all, get, n, same, x} from './machine.ts'
import {certFor} from './counts.ts'
import {prepareGuardCountContext} from './count-guard-context.ts'
import {proveFixedCountPhase} from './count-phase.ts'
import {composeCountOperationProofs, type FixedOperationProof} from './count-case-compose.ts'
import {proveFixedCountOperations} from './count-guard-composition.ts'
import {checkMC, countedObligations} from '../kernel/kernel.ts'
import {clock, counted, fullRate, withWall} from '../kernel/prove.ts'
function fixture() {
  const key = (a: string, b: string) => ({op: 'add' as const, a: {op: 'mul' as const, k: 4, a: x(a)}, b: x(b)}), member = same(get('edge', key('row', 'member')), n(1)), below = x('size')
  const m: Machine = {name: 'three renamed operations', params: ['size'], inputs: ['move'], state: {phase: n(0)}, maps: {edge: 0, tick: 0, limit: 0}, step: {}, pre: all({op: '<=', a: n(1), b: below}, {op: '<=', a: below, b: n(4)}), assume: all({op: '<=', a: n(5), b: x('move')}, {op: '<', a: x('move'), b: n(8)}, {op: 'or', xs: [5, 6, 7].map(i => same(x('move'), n(i)))}), counts: {
    voters: {j: 'row', lo: 'column', key: 'member', base: 4, below, body: {op: 'if', c: all(member, {op: '<', a: get('tick', x('member')), b: get('limit', x('column'))}), then: n(1), else: n(0)}},
    rows: {j: 'row', key: 'member', below, body: {op: 'if', c: member, then: n(1), else: n(0)}}
  }}
  const law: Law = {name: 'two votes bounded by row', forall: 'a', keys: ['b'], holds: {op: 'or', xs: [{op: 'not', x: all({op: '<', a: x('a'), b: below}, {op: '<', a: x('b'), b: below})}, {op: '<=', a: {op: 'mul', k: 2, a: get('voters', key('a', 'b'))}, b: get('rows', x('a'))}]}}
  const phase: Law = {name: 'existing zero phase', forall: 't', holds: {op: 'or', xs: [{op: 'not', x: same(x('phase'), n(0))}, same(get('limit', x('t')), n(0))]}}
  return {m, law, family: [law, phase]}
}
const request = (g: Parameters<typeof certFor>[0], ds: Parameters<typeof certFor>[1]) => certFor(g, ds, false, 0, () => true)
test('all fixed cases compose onto one original operation-domain goal', () => {
  const {m, law, family} = fixture(), context = prepareGuardCountContext(m, law, family)!, before = JSON.stringify(m)
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const until = clock() + 4000, cases: FixedOperationProof[] = []
    for (const value of [5, 6, 7]) {
      const fixed = {...context.machine, assume: all(context.machine.assume!, same(x('move'), n(value)))}
      const seed = value === 6 ? {[law.name]: [n(1), n(2)]} : {}, saved = JSON.stringify(seed)
      const proof = proveFixedCountPhase(fixed, family, law, seed, until, request)
      expect(JSON.stringify(seed)).toBe(saved)
      expect(proof).toBeDefined(); if (!proof) return
      cases.push({value, proof})
    }
    const events: string[] = [], result = composeCountOperationProofs(context, family, law, cases, until, request, stage => events.push(stage))
    if (!result) console.log('COMPOSITION_DIAGNOSTIC', events)
    expect(result).toBeDefined()
    if (result) for (const p of countedObligations(context.machine, family, {[law.name]: result.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, result.certs[p.goal.name]!)).toBe(true)
    const initial = cases[0]!.proof.certs[law.name + ' @start']!
    const reused = composeCountOperationProofs(context, family, law, cases, until, request, undefined, {initial})
    expect(reused).toBeDefined()
    if (reused) for (const p of countedObligations(context.machine, family, {[law.name]: reused.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, reused.certs[p.goal.name]!)).toBe(true)
    expect(composeCountOperationProofs(context, family, law, cases, until, request, undefined, {initial: {...initial, tree: {leaf: []}}})).toBeUndefined()
    expect(composeCountOperationProofs(context, family, law, cases.slice(1), until, request)).toBeUndefined()
    expect(composeCountOperationProofs(context, family, law, [cases[0]!, cases[0]!, cases[2]!], until, request)).toBeUndefined()
    const broken = structuredClone(cases); broken[1]!.proof.certs[law.name + ' @step']!.tree = {leaf: []}
    expect(composeCountOperationProofs(context, family, law, broken, until, request)).toBeUndefined()
  }))
  expect(JSON.stringify(m)).toBe(before)
})
test('operation zero preserves source path identities through transport', () => {
  const {m, law, family} = fixture(); m.assume = all({op: '<', a: x('move'), b: n(3)}, {op: 'or', xs: [0, 1, 2].map(i => same(x('move'), n(i)))})
  const context = prepareGuardCountContext(m, law, family)!
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const until = clock() + 4000, cases: FixedOperationProof[] = []
    for (const value of [0, 1, 2]) {
      const fixed = {...context.machine, assume: all(context.machine.assume!, same(x('move'), n(value)))}, proof = proveFixedCountPhase(fixed, family, law, {}, until, request)
      expect(proof).toBeDefined(); if (!proof) return
      cases.push({value, proof})
    }
    const events: string[] = [], result = composeCountOperationProofs(context, family, law, cases, until, request, stage => events.push(stage))
    if (!result) console.log('COMPOSITION_DIAGNOSTIC', events)
    expect(result).toBeDefined()
    if (result) for (const p of countedObligations(context.machine, family, {[law.name]: result.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, result.certs[p.goal.name]!)).toBe(true)
  }))
})

test('unchecked case proposals need the final assembled checker', () => {
  const {m, law, family} = fixture(), context = prepareGuardCountContext(m, law, family)!
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const until = clock() + 4000, events: Record<string, unknown>[] = []
    const cases = proveFixedCountOperations(context, family, law, until, request, e => events.push(e), {deferToComposition: true})!
    expect(cases).toHaveLength(3)
    expect(events.filter(e => e.stage === 'operation')).toHaveLength(3)
    expect(events.filter(e => e.stage === 'operation').every(e => e.proposed === true && e.checked === false)).toBe(true)
    expect(cases.every(c => !c.proof.certs[law.name + ' @start'])).toBe(true)
    const result = composeCountOperationProofs(context, family, law, cases, until, request)
    expect(result).toBeDefined()
    if (result) for (const p of countedObligations(context.machine, family, {[law.name]: result.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, result.certs[p.goal.name]!)).toBe(true)
    const broken = structuredClone(cases); broken[0]!.proof.certs[law.name + ' @step']!.tree = {leaf: []}
    expect(composeCountOperationProofs(context, family, law, broken, until, request)).toBeUndefined()
  }))
})
test('case composition respects an expired shared allowance', () => {
  const {m, law, family} = fixture(), context = prepareGuardCountContext(m, law, family)!
  expect(composeCountOperationProofs(context, family, law, [], clock() - 1, request)).toBeUndefined()
})
