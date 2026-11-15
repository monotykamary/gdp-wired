import {expect, test} from 'bun:test'
import {quorumLaws} from './quorum-laws.ts'
import {type C, type E, type Machine, all, any, atMost, get, ite, less, minus, n, not, plus, same, times, tuple, walk, x} from './machine.ts'
import {countedObligations, scope, substC} from '../kernel/kernel.ts'
const bit = (c: C) => ite(c, n(1), n(0))
const fixture = (base = 8, native = false): Machine => {
  const cell = (r: E, k: E) => same(get('Rows', native ? tuple([r, k]) : plus(times(base, r), k)), n(1)), member = (k: E) => atMost(n(1), get('Proposal', k))
  const cnt = (body: (k: E) => C) => ({j: 'j', key: 'k', below: x('size'), body: bit(body(x('k')))})
  const read = (name: string) => get(name, n(0))
  const first: E = {op: 'proj', k: 0, a: x('z')}, second: E = {op: 'proj', k: 1, a: x('z')}
  return {name: 'row-election fixture', ...(native ? {relations: {Rows: ['Node', 'Node']}} : {}), params: ['size'], inputs: ['row', 'left', 'right'], state: {}, maps: {Rows: 0, Epoch: 0, Written: 0, Version: 0}, inputMaps: ['Proposal'],
    counts: {rowCount: cnt(k => cell(x('row'), k)), members: cnt(member), diff: cnt(k => all(cell(x('row'), k), not(member(k)))), reverse: cnt(k => all(member(k), not(cell(x('row'), k)))), meet: cnt(k => all(cell(x('row'), k), member(k)))},
    assume: all(less(x('row'), x('size')), less(read('rowCount'), times(2, read('members'))), atMost(times(2, x('left')), read('rowCount')), less(read('rowCount'), plus(times(2, x('left')), n(2))), atMost(times(2, x('right')), read('members')), less(read('members'), plus(times(2, x('right')), n(2)))),
    step: {flags: {
      eligible: {op: 'all', key: 'voter', c: any(not(member(x('voter'))), all(less(get('Epoch', x('voter')), plus(get('Epoch', x('row')), n(1))), atMost(get('Version', x('voter')), get('Version', x('row')))))},
      elect: {op: 'flag', name: 'eligible'},
      change: less(read('meet'), plus(minus(plus(x('left'), n(1)), read('diff')), minus(plus(x('right'), n(1)), read('reverse')))),
    }, maps: {
      Written: {each: 'z', value: ite(all({op: 'flag', name: 'elect'}, same(x('z'), x('row'))), plus(get('Epoch', x('row')), n(1)), get('Written', x('z')))},
      Rows: {each: 'z', value: ite(native ? all({op: 'flag', name: 'change'}, same(first, x('row'))) : all({op: 'flag', name: 'change'}, atMost(times(base, x('row')), x('z')), less(x('z'), plus(times(base, x('row')), n(base)))), bit(member(native ? second : minus(x('z'), times(base, x('row'))))), get('Rows', native ? tuple([first, second]) : x('z')))},
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
test('native tuple row proposals match packed rows after pair-key normalization', () => {
  const packed = quorumLaws(fixture()), nativeMachine = fixture(8, true), native = quorumLaws(nativeMachine)
  const normal = (t: any): any => {
    if (Array.isArray(t)) return t.map(normal)
    if (!t || typeof t !== 'object') return t
    if (t.op === 'tup') return plus(times(8, normal(t.a)), normal(t.b))
    if (t.op === 'proj' && t.a.op === 'var' && t.a.name === 'row$quorum') return x(t.k === 0 ? 'row$quorum' : 'other$quorum')
    const o = Object.fromEntries(Object.entries(t).map(([k, v]) => [k, normal(v)])) as any
    if (o.j === 'row$quorum' && JSON.stringify(o.body).includes('other$quorum')) { o.lo = 'other$quorum'; o.base = 8 }
    return o
  }
  // Single-row laws normalize directly. Pair laws use a single quantified
  // natural, with fst/snd projections and separate reversed count bodies.
  expect(native.laws.map(l => l.name)).toEqual(packed.laws.map(l => l.name))
  const pairs = new Map<string, {name: string, swap: boolean}>()
  const canonical = (v: any): string => JSON.stringify(v, (_k, q) => q?.op === 'and' ? {...q, xs: [...q.xs].sort((a: unknown, b: unknown) => JSON.stringify(a).localeCompare(JSON.stringify(b)))} : q)
  const swap = (v: any): any => Array.isArray(v) ? v.map(swap) : v && typeof v === 'object' ? v.op === 'var' && ['row$quorum', 'other$quorum'].includes(v.name) ? x(v.name === 'row$quorum' ? 'other$quorum' : 'row$quorum') : Object.fromEntries(Object.entries(v).map(([k, q]) => [k, swap(q)])) : v
  for (const [name, d] of Object.entries(native.counts)) {
    if (!JSON.stringify(d.body).includes('proj')) continue
    const body = normal(d.body)
    const found = Object.entries(packed.counts).flatMap(([key, p]) => !p.base ? [] : canonical(body) === canonical(p.body) ? [{name: key, swap: false}] : canonical(body) === canonical(swap(p.body)) ? [{name: key, swap: true}] : [])[0]
    expect(found).toBeDefined(); pairs.set(name, found!)
  }
  expect(pairs.size).toBeGreaterThan(0)
  // Asymmetric row-minus-row bodies must retain both orientations.
  expect([...pairs.values()].some(p => p.swap)).toBe(true)
  expect([...pairs.values()].some(p => !p.swap)).toBe(true)
  const lawNormal = (v: any): any => {
    if (Array.isArray(v)) return v.map(lawNormal)
    if (!v || typeof v !== 'object') return v
    if (v.op === 'proj' && v.a.op === 'tup') return lawNormal(v.k === 0 ? v.a.a : v.a.b)
    if (v.op === 'get' && pairs.has(v.map)) {
      const p = pairs.get(v.map)!
      return get(p.name, plus(times(8, x(p.swap ? 'b$quorum' : 'a$quorum')), x(p.swap ? 'a$quorum' : 'b$quorum')))
    }
    return Object.fromEntries(Object.entries(v).filter(([, q]) => q !== undefined).map(([k, q]) => [k, lawNormal(q)]))
  }
  for (const law of native.laws) {
    const expected = packed.laws.find(l => l.name === law.name)!
    const isPair = expected.keys?.includes('b$quorum')
    const instantiated = isPair ? {...law, holds: substC(law.holds, {vars: {'a$quorum': tuple([x('a$quorum'), x('b$quorum')])}, maps: {}, flags: {}})} : law
    const normalized = lawNormal(instantiated)
    if (isPair) normalized.keys = ['b$quorum', ...(normalized.keys ?? [])]
    expect(normalized).toEqual(expected)
  }
  expect(Object.values(native.counts).some(d => JSON.stringify(d.body).includes('\"op\":\"proj\"'))).toBe(true)
  expect(native.laws.some(l => l.name.includes('no quorum eligible/3'))).toBe(true)
  expect(native.laws.some(l => l.name.includes('stored guard change') && l.name.includes('disabled'))).toBe(true)
  const checkedShape = {...nativeMachine, counts: {...nativeMachine.counts, ...native.counts}}
  expect(() => scope(checkedShape, native.laws)).not.toThrow()
  expect(() => countedObligations(checkedShape, native.laws)).not.toThrow()
  const boolean = fixture(8, true), write = boolean.step.maps!.Rows!
  write.value = bit(atMost(n(1), write.value))
  expect(quorumLaws(boolean).laws.map(l => l.name)).toEqual(native.laws.map(l => l.name))
  const unrelated = fixture(8, true), wrong = unrelated.step.maps!.Rows!
  if (wrong.value.op !== 'if') throw Error('fixture row write')
  wrong.value.c = all({op: 'flag', name: 'change'}, same({op: 'proj', k: 0, a: x('z')}, x('left')))
  expect(quorumLaws(unrelated).laws.some(l => l.name.includes('stored guard'))).toBe(false)
  const other = fixture(8, true); other.relations = {Rows: ['Node', 'Other']}
  expect(quorumLaws(other).laws).toEqual([])
})
