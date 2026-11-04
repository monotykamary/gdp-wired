import {expect, test} from 'bun:test'
import {type C, get, n, x, same, not} from '../../core/machine.ts'
import type {Fact} from '../../kernel/cyclic.ts'
import {tuple} from '../../kernel/kernel.ts'
import {certify} from './certify.ts'
import {EGraph, Meter} from './match.ts'
const fn = (v: ReturnType<typeof x>) => get('F', v)
const rel = (a: ReturnType<typeof x>, b: ReturnType<typeof x>) => get('R', tuple([a, b]))

test('nested congruence uses checked split hints; forged e-class merges remain rejected', () => {
  const fact: Fact = {name: 'diagonal rule', keys: ['u'], holds: {op: 'or', xs: [not(same(rel(x('u'), x('u')), n(1))), same(x('goal'), n(1))]}}
  for (const legitimate of [true, false]) {
    const hyps: C[] = [same(rel(fn(x('a')), fn(x('b'))), n(1))]
    if (legitimate) hyps.push(same(x('a'), x('b')))
    const meter = new Meter(100_000), g = new EGraph(meter)
    g.seed(hyps)
    if (!legitimate) { g.merge(g.add(x('a')), g.add(x('b'))); g.rebuild() }
    const found = g.match([rel(x('u'), x('u'))], ['u'])
    expect(found).toHaveLength(1)
    const target = {name: 'congruence replay', hyps, concl: same(x('goal'), n(1)), rank: [n(1)], insts: found.map(s => ({fact: 0, at: [s.u!]})), uses: []}
    // The current tree search does not invent this intermediate nested-read
    // equality. Keep that failed direct control, then supply a CHECKED bridge.
    const direct = certify([fact], [target], meter.used)
    expect(direct.checked).toBe(false)
    const bridgeOnly = certify([fact], [
      {name: 'intermediate F equality', hyps, concl: same(fn(x('a')), fn(x('b'))), rank: [n(0)], insts: [], uses: []},
      {...target, uses: [{node: 0, subst: {}, guard: same(n(0), n(0))}]},
    ], meter.used)
    expect(bridgeOnly.checked).toBe(false)
    // The kernel consults the PATH for key equality, not just hypothesis rows.
    // Split hints cover both sides; they are not assumed equality facts.
    const result = certify([fact], [target], meter.used, 2_000_000, [], [
      [x('a'), x('b')], [fn(x('a')), fn(x('b'))],
    ])
    expect({checked: result.checked, reason: result.reason}).toMatchObject({checked: legitimate})
  }
})
test('combined budget exhaustion and invalid bounds never produce a certificate', () => {
  expect(certify([], [], 2, 2).checked).toBe(false)
  expect(certify([], [], 0, Infinity).checked).toBe(false)
  expect(() => new EGraph(new Meter(100), Infinity)).toThrow()
  expect(() => new Meter(100, NaN)).toThrow()
})
