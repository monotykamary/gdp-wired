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
test('unsupported and expired row portfolios leave ordinary search available', () => {
  const {m, law, family} = fixture(), events: unknown[] = []
  expect(proveCountRowComposition(m, family, law, clock() - 1, request, e => events.push(e))).toBeUndefined()
  const unrelated: Law = {name: 'unrelated', holds: same(n(0), n(0))}
  expect(proveCountRowComposition(m, [unrelated], unrelated, clock() + 100, request, e => events.push(e))).toBeUndefined()
  expect(events).toHaveLength(0)
})
