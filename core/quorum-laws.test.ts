import {expect, test} from 'bun:test'
import {quorumLaws} from './quorum-laws.ts'
import {type C, type E, type Machine, all, any, atMost, get, ite, less, minus, n, not, plus, same, times, walk, x} from './machine.ts'
import {scope} from '../kernel/kernel.ts'
const bit = (c: C) => ite(c, n(1), n(0))
const fixture = (base = 8): Machine => {
  const cell = (r: E, k: E) => same(get('Rows', plus(times(base, r), k)), n(1)), member = (k: E) => atMost(n(1), get('Proposal', k))
  const cnt = (body: (k: E) => C) => ({j: 'j', key: 'k', below: x('size'), body: bit(body(x('k')))})
  const read = (name: string) => get(name, n(0))
  return {name: 'row-election fixture', params: ['size'], inputs: ['row', 'left', 'right'], state: {}, maps: {Rows: 0, Epoch: 0, Written: 0, Version: 0}, inputMaps: ['Proposal'],
    counts: {rowCount: cnt(k => cell(x('row'), k)), members: cnt(member), diff: cnt(k => all(cell(x('row'), k), not(member(k)))), reverse: cnt(k => all(member(k), not(cell(x('row'), k)))), meet: cnt(k => all(cell(x('row'), k), member(k)))},
    assume: all(less(x('row'), x('size')), less(read('rowCount'), times(2, read('members'))), atMost(times(2, x('left')), read('rowCount')), less(read('rowCount'), plus(times(2, x('left')), n(2))), atMost(times(2, x('right')), read('members')), less(read('members'), plus(times(2, x('right')), n(2)))),
    step: {flags: {
      eligible: {op: 'all', key: 'voter', c: any(not(member(x('voter'))), all(less(get('Epoch', x('voter')), plus(get('Epoch', x('row')), n(1))), atMost(get('Version', x('voter')), get('Version', x('row')))))},
      elect: {op: 'flag', name: 'eligible'},
      change: less(read('meet'), plus(minus(plus(x('left'), n(1)), read('diff')), minus(plus(x('right'), n(1)), read('reverse')))),
    }, maps: {
      Written: {each: 'z', value: ite(all({op: 'flag', name: 'elect'}, same(x('z'), x('row'))), plus(get('Epoch', x('row')), n(1)), get('Written', x('z')))},
      Rows: {each: 'z', value: ite(all({op: 'flag', name: 'change'}, atMost(times(base, x('row')), x('z')), less(x('z'), plus(times(base, x('row')), n(base)))), bit(member(minus(x('z'), times(base, x('row'))))), get('Rows', x('z')))},
    }},
  }
}
test('row-majority lifting uses syntax, substitutes the written target, and scopes all proposals', () => {
  const m = fixture(), g = quorumLaws(m), mm = {...m, counts: {...m.counts, ...g.counts}}
  expect(g.laws.filter(l => l.name.includes('no quorum'))).toHaveLength(3)
  expect(g.laws.filter(l => l.name.includes('stored guard'))).toHaveLength(2)
  expect(Object.keys(g.counts)).toHaveLength(6) // size, three bodies, difference, intersection
  expect(() => scope(mm, g.laws)).not.toThrow()
  const full = g.laws.find(l => l.name.endsWith('eligible/3'))!
  expect(full.keys).toHaveLength(1)
  const reads = new Set<string>(); walk(g.counts, o => { if (o.op === 'get') reads.add(o.map as string) })
  expect(reads.has('Written')).toBe(true)
  expect(reads.has('Proposal')).toBe(false)
  expect(JSON.stringify(g)).not.toContain('"name":"row"')
  // Reversed row difference is a read at swapped keys, not another definition.
  expect(Object.keys(g.counts).filter(s => s.includes('rows$'))).toHaveLength(2)
  expect(quorumLaws(m)).toEqual(g)
})
test('parameter-majorities and unreferenced quantified flags do not trigger', () => {
  const m = fixture()
  expect(quorumLaws({...m, assume: less(x('size'), times(2, get('members', n(0))))}).laws).toEqual([])
  expect(quorumLaws({...m, step: {...m.step, flags: {eligible: m.step.flags!.eligible!}}}).laws).toEqual([])
})
test('fresh names avoid state/request capture and the packed base is read from syntax', () => {
  const m = fixture(16); m.state['a$quorum'] = n(0); m.inputs.push('member$quorum')
  const g = quorumLaws(m)
  expect(g.laws[0]!.forall).not.toBe('a$quorum')
  expect(Object.values(g.counts).filter(c => c.base).every(c => c.base === 16)).toBe(true)
  expect(() => scope({...m, counts: {...m.counts, ...g.counts}}, g.laws)).not.toThrow()
})
