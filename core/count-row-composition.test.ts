import {expect, test} from 'bun:test'
import {type Law, n, same, x} from './machine.ts'
import {rowCompositionFixture as fixture} from './count-row-composition.fixture.ts'
import {certFor} from './counts.ts'
import {proveCountRowComposition} from './count-row-composition.ts'
import {checkMC, countedObligations} from '../kernel/kernel.ts'
import {clock, counted, fullRate, withWall} from '../kernel/prove.ts'

const request = (g: Parameters<typeof certFor>[0], ds: Parameters<typeof certFor>[1]) => certFor(g, ds, false, 0)
test('a renamed row portfolio accepts only one assembled original-goal proof', () => {
  const {m, law, family} = fixture(), before = JSON.stringify(m)
  counted(fullRate, () => withWall(performance.now() + 8000, () => {
    const events: Record<string, unknown>[] = [], result = proveCountRowComposition(m, family, law, clock() + 4000, request, e => events.push(e), {framePremisesOnly: true})
    expect(result).toBeDefined()
    const operations = events.filter(e => e.stage === 'operation')
    expect(operations).toHaveLength(3)
    expect(operations.every(e => e.proposed === true && e.checked === false)).toBe(true)
    if (result) for (const p of countedObligations(m, family, {[law.name]: result.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, result.certs[p.goal.name]!)).toBe(true)
  }))
  expect(JSON.stringify(m)).toBe(before)
})
test('a broken row write declines at its first attempted case', () => {
  const {m, law, family} = fixture()
  const bad = {op: 'if' as const, c: same(x('cell'), n(0)), then: n(1), else: n(0)}
  m.step.maps!.edge = {each: 'cell', value: {op: 'if', c: {op: 'flag', name: 'copy'}, then: bad, else: bad}}
  m.step.maps!.marker = {each: 'mark', value: n(1)}
  counted(fullRate, () => withWall(performance.now() + 8000, () => {
    const events: Record<string, unknown>[] = []
    expect(proveCountRowComposition(m, family, law, clock() + 1500, request, e => events.push(e))).toBeUndefined()
    const operations = events.filter(e => e.stage === 'operation')
    expect(operations).toHaveLength(1)
    expect(operations[0]?.proposed).toBe(false)
  }))
})
test('deferred row leaves remain explicit proposals and final native checks remain mandatory', () => {
  const {m, law, family} = fixture(), results: unknown[] = []
  counted(fullRate, () => withWall(performance.now() + 12000, () => {
    for (const deferRowChecks of [false, true]) {
      const events: Record<string, unknown>[] = []
      const proof = proveCountRowComposition(m, family, law, clock() + 4000, request, e => events.push(e), {framePremisesOnly: true, deferRowChecks})
      expect(proof).toBeDefined(); expect(proof?.status).toBeUndefined()
      expect(events.some(e => e.part === 'native-step-check')).toBe(true)
      expect(events.some(e => e.part === 'native-init-check')).toBe(true)
      const leafChecks = events.filter(e => ['row-leaf-check', 'row-scoped-check', 'row-symmetry-check'].includes(String(e.part)))
      expect(leafChecks.length > 0).toBe(!deferRowChecks)
      const operations = events.filter(e => e.stage === 'operation')
      expect(operations.every(e => e.checked === false && (deferRowChecks ? e.status === 'unchecked' : !('status' in e)))).toBe(true)
      if (proof) for (const p of countedObligations(m, family, {[law.name]: proof.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof.certs[p.goal.name]!)).toBe(true)
      results.push(proof)
    }
  }))
  expect(results[1]).toEqual(results[0])
}, 16000)

test('unsupported and expired row portfolios leave ordinary search available', () => {
  const {m, law, family} = fixture(), events: unknown[] = []
  expect(proveCountRowComposition(m, family, law, clock() - 1, request, e => events.push(e))).toBeUndefined()
  const unrelated: Law = {name: 'unrelated', holds: same(n(0), n(0))}
  expect(proveCountRowComposition(m, [unrelated], unrelated, clock() + 100, request, e => events.push(e))).toBeUndefined()
  expect(events).toHaveLength(0)
})
