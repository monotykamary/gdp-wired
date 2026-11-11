import {expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, all, get, n, same, x} from './machine.ts'
import {certFor} from './counts.ts'
import {proveCountRowCopyLinear} from './count-row-copy-linear.ts'
import {checkMC, countedObligations} from '../kernel/kernel.ts'
import {clock, counted, fullRate, withWall} from '../kernel/prove.ts'
function fixture() {
  const product = (k: number, a: E): E => ({op: 'mul', k, a}), plus = (a: E, b: E): E => ({op: 'add', a, b}), minus = (a: E, b: E): E => ({op: 'sub', a, b})
  const key = (a: string, b: string) => plus(product(16, x(a)), x(b)), below = x('size'), active: C = {op: 'flag', name: 'transfers'}
  const row = same(get('links', key('row', 'member')), n(1)), inTarget = all({op: '<=', a: product(16, x('target')), b: x('cell')}, {op: '<', a: x('cell'), b: plus(product(16, x('target')), n(16))})
  const moved: E = {op: 'if', c: {op: '<=', a: x('target'), b: x('source')}, then: get('links', plus(x('cell'), product(16, minus(x('source'), x('target'))))), else: get('links', minus(x('cell'), product(16, minus(x('target'), x('source')))))}
  const m: Machine = {name: 'independent row-transfer fixture', params: ['size'], inputs: ['action', 'source', 'target'], state: {phase: n(1)}, maps: {links: 0, clocks: 0, limits: 0}, pre: all({op: '<=', a: n(1), b: below}, {op: '<=', a: below, b: n(16)}), assume: all(same(x('action'), n(6)), {op: 'or', xs: [6, 7, 8].map(i => same(x('action'), n(i)))}, {op: '<', a: x('source'), b: below}, {op: '<', a: x('target'), b: below}), counts: {
    votes: {j: 'row', lo: 'column', key: 'member', base: 16, below, body: {op: 'if', c: all(row, {op: '<', a: get('clocks', x('member')), b: get('limits', x('column'))}), then: n(1), else: n(0)}},
    rows: {j: 'row', key: 'member', below, body: {op: 'if', c: row, then: n(1), else: n(0)}}
  }, step: {flags: {transfers: all(same(x('action'), n(6)), same(x('phase'), n(1)))}, maps: {
    limits: {each: 'index', value: {op: 'if', c: all(active, same(x('index'), x('target'))), then: get('limits', x('source')), else: get('limits', x('index'))}},
    links: {each: 'cell', value: {op: 'if', c: all(active, inTarget), then: moved, else: get('links', x('cell'))}}
  }}}
  const law: Law = {name: 'row cardinality majority bound', forall: 'a', keys: ['b'], holds: {op: 'or', xs: [{op: 'not', x: all({op: '<', a: x('a'), b: below}, {op: '<', a: x('b'), b: below})}, {op: '<=', a: product(2, get('votes', key('a', 'b'))), b: get('rows', x('a'))}]}}
  return {m, law, family: [law]}
}
const request = (g: Parameters<typeof certFor>[0], ds: Parameters<typeof certFor>[1]) => certFor(g, ds, false, 0, () => true)
test('pointwise row-copy cuts yield an ordinarily checked INIT/STEP proof', () => {
  const {m, law, family} = fixture(), seed = {[law.name]: [x('a#'), x('b')]}, before = JSON.stringify(seed)
  counted(fullRate, () => withWall(performance.now() + 7000, () => {
    const proof = proveCountRowCopyLinear(m, family, law, seed, clock() + 6000, request)
    expect(proof).toBeDefined()
    if (proof) {
      expect(proof.certs[law.name + ' @step']!.insts).toEqual([])
      expect(proof.certs[law.name + ' @step']!.lins?.length).toBe(6)
      for (const p of countedObligations(m, family, {[law.name]: proof.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof.certs[p.goal.name]!)).toBe(true)
    }
  }))
  expect(JSON.stringify(seed)).toBe(before)
})
test('inactive copy frames exclude writes guarded by other operation values', () => {
  const {m, law, family} = fixture(), write = m.step.maps!.links!
  if (!('each' in write)) throw Error('expected row update')
  write.value = {op: 'if', c: same(x('action'), n(7)), then: n(0), else: write.value}
  counted(fullRate, () => withWall(performance.now() + 7000, () => {
    const proof = proveCountRowCopyLinear(m, family, law, {}, clock() + 6000, request)
    expect(proof).toBeDefined()
    if (proof) for (const p of countedObligations(m, family, {[law.name]: proof.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof.certs[p.goal.name]!)).toBe(true)
  }))
})

test('copy proof refuses a membership-clock update that invalidates inclusion', () => {
  const {m, law, family} = fixture()
  m.step.maps!.clocks = {each: 'clockCell', value: {op: 'if', c: all({op: 'flag', name: 'transfers'}, same(x('clockCell'), x('target'))), then: n(0), else: get('clocks', x('clockCell'))}}
  expect(() => countedObligations(m, family, {[law.name]: {}}, 0)).not.toThrow()
  counted(fullRate, () => withWall(performance.now() + 7000, () => expect(proveCountRowCopyLinear(m, family, law, {}, clock() + 6000, request)).toBeUndefined()))
})
