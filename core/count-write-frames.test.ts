import {expect, test} from 'bun:test'
import {type C, type E, type Machine, all, get, ite, less, n, not, plus, same, x} from './machine.ts'
import {type CountCert, type CountDecl, type CountInst, checkCounted, countHyp, countedGoal, countedOk} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'
import {countsForReads} from './count-facts.ts'
import {proposeWriteCountFrames} from './count-write-frames.ts'

const bit = (c: C): E => ite(c, n(1), n(0))
const packed = (a: E, b: E): E => plus({op: 'mul', k: 64, a}, b)
const vector = (terms: CountInst['terms']) => JSON.stringify([...terms].sort((a, b) => a[1].localeCompare(b[1])))
const signature = (inst: CountInst) => vector(inst.terms)
const directions = (a: string, b: string) => [vector([[1, a], [-1, b]]), vector([[-1, a], [1, b]])]

function fixture(prefix = '') {
  const stored = `${prefix}Roster`, carried = `${prefix}Parcel`, other = `${prefix}Unrelated`
  const member = (map: string, key: E) => same(get(map, key), n(1))
  const at = (row: E) => member(stored, packed(row, x('k')))
  const source = member(carried, x('k')), old = at(x('actor'))
  const m: Machine = {name: 'renamable copy', params: ['limit'], inputs: ['actor', 'copy'], state: {},
    maps: {[stored]: 0}, inputMaps: [carried, other], step: {maps: {
      [stored]: {each: 'cell', value: ite(same(x('copy'), n(1)), get(carried, x('cell')), get(stored, x('cell')))},
    }}}
  const binary = (map: string, body: E): CountDecl => ({map, j: 'a', lo: 'b', base: 64, key: 'k', below: x('limit'), body})
  const incoming = (map: string, body: E): CountDecl => ({map, j: 'unused', key: 'k', below: x('limit'), body})
  const ds: CountDecl[] = [
    binary(`${prefix}meet`, bit(all(at(x('a')), at(x('b'))))),
    binary(`${prefix}minus`, bit(all(at(x('a')), not(at(x('b')))))),
    incoming(`${prefix}both`, bit(all(old, source))),
    incoming(`${prefix}oldOnly`, bit(all(old, not(source)))),
    incoming(`${prefix}newOnly`, bit(all(source, not(old)))),
    incoming(`${prefix}noise`, bit(all(old, member(other, x('k'))))),
  ]
  // Post bodies need not retain their PRE shape. The proposal must not normalize
  // this expansion (or mistake its absence of membership syntax for no match).
  for (const d of ds.slice(0, 2)) ds.push({...d, map: `${d.map}#`, body: plus(x('expandedWrite'), n(7))})
  const cert: Pick<CountCert, 'reads' | 'insts'> = {reads: [
    ['joined', `${prefix}meet#`, packed(x('actor'), x('peer'))],
    ['left', `${prefix}minus#`, packed(x('actor'), x('peer'))],
    ['right', `${prefix}minus#`, packed(x('peer'), x('actor'))],
    ['inBoth', `${prefix}both`, n(0)], ['inOld', `${prefix}oldOnly`, n(0)],
    ['inNew', `${prefix}newOnly`, n(0)], ['noise', `${prefix}noise`, n(0)],
    ['preOnly', `${prefix}meet`, packed(x('actor'), x('peer'))],
  ], insts: []}
  return {m, ds, cert, stored, carried, other, demand: new Set(['joined', 'left', 'right'])}
}

test('generic renamed writers propose the missing 2/4/4 directional frames', () => {
  for (const prefix of ['', 'arbitrary/renamed$']) {
    const f = fixture(prefix), insts = proposeWriteCountFrames(f.m, f.ds, f.cert, f.demand)
    expect(insts.map(signature)).toEqual([
      ...directions('joined', 'inBoth'), ...directions('left', 'inOld'), ...directions('left', 'inNew'),
      ...directions('right', 'inOld'), ...directions('right', 'inNew'),
    ])
    expect(insts.every(i => i.unit === 0 && i.terms.length === 2 && JSON.stringify(i.below) === JSON.stringify(x('limit')))).toBe(true)
  }
})

test('copied row sizes and intersections of two overwritten rows get source-size bridges', () => {
  const f = fixture(), below = x('limit')
  f.ds.push({map: 'sourceSize', j: 'unused', key: 'k', below, body: bit(same(get(f.carried, x('k')), n(1)))},
    {map: 'rowSize', j: 'row', key: 'k', below, body: bit(same(get(f.stored, packed(x('row'), x('k'))), n(1)))},
    {map: 'rowSize#', j: 'row', key: 'k', below, body: x('expanded')})
  f.cert.reads.push(['sourceN', 'sourceSize', n(0)], ['rowN', 'rowSize#', x('actor')])
  f.demand.add('rowN')
  const out = proposeWriteCountFrames(f.m, f.ds, f.cert, f.demand).map(signature)
  expect(out).toEqual(expect.arrayContaining([...directions('rowN', 'sourceN'), ...directions('joined', 'sourceN')]))
  expect(out).not.toContain(vector([[1, 'left'], [-1, 'sourceN']]))
})
test('only demanded post heads participate, never unrelated carried sets or pre heads', () => {
  const f = fixture()
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, new Set(['joined'])).map(signature)).toEqual(directions('joined', 'inBoth'))
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, new Set(['preOnly', 'inBoth', 'missing']))).toEqual([])
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, new Set())).toEqual([])
  expect(proposeWriteCountFrames({...f.m, step: {}}, f.ds, f.cert, f.demand)).toEqual([])
  expect(proposeWriteCountFrames({...f.m, inputMaps: [f.other]}, f.ds, f.cert, f.demand)).toEqual([])
})

test('a carried map read only in the write guard or arithmetic is not a copied source', () => {
  const f = fixture(), write = f.m.step.maps![f.stored]!
  f.m.step.maps![f.stored] = {each: 'cell', value: ite(same(get(f.other, x('cell')), n(1)), write.value, n(0))}
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, f.demand)).toHaveLength(10)
  f.m.step.maps![f.stored] = {key: n(0), value: ite(same(get(f.carried, n(0)), n(1)), n(2), n(0))}
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, f.demand)).toEqual([])
  f.m.step.maps![f.stored] = {key: n(0), value: plus(get(f.carried, n(0)), n(1))}
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, f.demand)).toEqual([])
})

test('point writes and Boolean membership-copy values are supported without reading guard sources', () => {
  const f = fixture()
  f.m.step.maps![f.stored] = {key: n(0), value: bit(same(n(1), get(f.carried, n(0))))}
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, f.demand)).toHaveLength(10)
})

test('lowered Boolean copy values preserve guarded membership arms', () => {
  const f = fixture(), copying = same(x('copy'), n(1))
  f.m.step.maps![f.stored] = {each: 'cell', value: bit({op: 'or', xs: [
    all(copying, same(get(f.carried, x('cell')), n(1))),
    all(not(copying), same(get(f.stored, x('cell')), n(1))),
  ]})}
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, f.demand)).toHaveLength(10)
})
test('membership syntaxes, conjunction order and double negation do not change pair selection', () => {
  const f = fixture()
  for (const d of f.ds) {
    if (d.map.endsWith('#') || d.body.op !== 'if' || d.body.c.op !== 'and') continue
    d.body = bit(all(...d.body.c.xs.reverse().map((c): C => {
      if (c.op !== '=' || c.a.op !== 'get') return c
      return not(not({op: d.map === 'both' ? '<' : '<=', a: n(d.map === 'both' ? 0 : 1), b: c.a}))
    })))
  }
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, f.demand)).toHaveLength(10)
})

test('non-membership predicates and malformed binary regions are not frame shapes', () => {
  for (const bad of [
    bit(all(less(get('Age', x('k')), get('Term', x('k'))), same(get('Roster', x('k')), n(1)))),
    bit(all(same(get('Roster', x('k')), n(2)), same(get('Roster', x('actor')), n(1)))),
    bit(all(not(same(get('Roster', x('k')), n(1))), not(same(get('Roster', x('actor')), n(1))))),
    bit(all(same(get('Roster', x('k')), n(1)), same(get('Roster', x('k')), n(1)))),
  ]) {
    const f = fixture()
    f.ds.find(d => d.map === 'meet')!.body = bad
    expect(proposeWriteCountFrames(f.m, f.ds, f.cert, new Set(['joined']))).toEqual([])
  }
})

test('incoming, PRE and actual post bounds must match exactly; unsupported packed reads are skipped', () => {
  const f = fixture()
  f.ds.find(d => d.map === 'both')!.below = n(6)
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, new Set(['joined']))).toEqual([])
  f.ds.find(d => d.map === 'both')!.below = x('limit')
  f.ds.find(d => d.map === 'meet#')!.below = n(6)
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, new Set(['joined']))).toEqual([])
  f.ds.find(d => d.map === 'meet#')!.below = x('limit')
  f.cert.reads[0]![2] = n(0)
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, new Set(['joined']))).toEqual([])
})

test('existing coefficient vectors, including reordered reverse directions, are deduplicated independently', () => {
  const f = fixture()
  f.cert.insts.push({wit: 'existing', below: x('limit'), unit: 0, terms: [[1, 'inBoth'], [-1, 'joined']]})
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, new Set(['joined'])).map(signature)).toEqual([directions('joined', 'inBoth')[0]!])
  f.cert.insts.push({wit: 'other', below: x('limit'), unit: 0, terms: [[-1, 'inBoth'], [2, 'joined'], [-1, 'joined'], [0, 'noise']]})
  expect(proposeWriteCountFrames(f.m, f.ds, f.cert, new Set(['joined']))).toEqual([])
})

test('caps are stable, at most 32, with fresh witnesses and no input mutation', () => {
  const f = fixture()
  f.m.state['writeFrame$0'] = x('writeFrame$1')
  f.m.step.flags = {'writeFrame$2': same(x('writeFrame$3'), n(0))}
  f.ds.push({map: 'unused', j: 'writeFrame$4', key: 'writeFrame$5', below: x('writeFrame$6'), body: x('writeFrame$7')})
  f.cert.reads.push(['writeFrame$8', 'unused', x('writeFrame$9')])
  f.cert.insts.push({wit: 'writeFrame$10', below: x('writeFrame$11'), terms: [[1, 'writeFrame$12']], unit: 1})
  for (let i = 0; i < 20; i++) {
    f.cert.reads.push([`extra${i}`, 'meet#', packed(n(i), n(0))]); f.demand.add(`extra${i}`)
  }
  const before = JSON.stringify(f), run = (cap?: number) => proposeWriteCountFrames(f.m, f.ds, f.cert, f.demand, cap)
  const insts = run()
  expect(insts).toHaveLength(32)
  expect(run(200)).toEqual(insts)
  expect(run(3)).toEqual(insts.slice(0, 3))
  expect(run(1)).toHaveLength(1)
  for (const cap of [0, -1, Number.NaN, Number.POSITIVE_INFINITY, 0.5]) expect(run(cap)).toEqual([])
  expect(run()).toEqual(insts)
  expect(insts[0]!.wit).toBe('writeFrame$13')
  expect(new Set(insts.map(i => i.wit)).size).toBe(insts.length)
  expect(JSON.stringify(f)).toBe(before)
  expect([...f.demand]).toEqual(['joined', 'left', 'right', ...Array.from({length: 20}, (_, i) => `extra${i}`)])
})

test('false frames stay untrusted: a witness survives without the copying guard', () => {
  const m: Machine = {name: 'guarded copy', params: [], inputs: ['copy'], state: {}, maps: {Stored: 0}, inputMaps: ['Packet'],
    step: {maps: {Stored: {key: n(0), value: ite(same(x('copy'), n(1)), get('Packet', n(0)), n(1))}}}}
  const a = same(get('Stored', n(0)), n(1)), b = same(get('Packet', n(0)), n(1)), incoming = bit(all(a, b))
  const ds: CountDecl[] = [
    {map: 'pair', j: 'j', key: 'k', below: n(2), body: bit(all(a, same(get('Stored', n(1)), n(1))))},
    {map: 'pair#', j: 'j', key: 'k', below: n(2), body: ite(same(x('copy'), n(1)), incoming, n(1))},
    {map: 'incoming', j: 'j', key: 'k', below: n(2), body: incoming},
  ]
  const cert: Pick<CountCert, 'reads' | 'insts'> = {reads: [['after', 'pair#', n(0)], ['before', 'incoming', n(0)]], insts: []}
  const inst = proposeWriteCountFrames(m, ds, cert, new Set(['after']))[0]!
  expect(inst).toBeDefined()
  const counts = countsForReads(ds, cert.reads)!, h = countHyp(counts, inst)!
  expect(h.op).toBe('or')
  if (h.op === 'or') expect(h.xs[1]!.op).toBe('and')
  const refute = (hyps: C[]) => {
    expect(countedOk(hyps, counts, [inst])).toBe(true)
    const g = {name: 'only guarded frame is provable', counts, hyps}, goal = countedGoal(g, [inst])!
    return {g, proof: grow(goal, new Map(), {nodes: 0, until: clock() + 2000})}
  }
  // With the guard, the two bodies agree; count-instance checking proves the
  // requested direction. Without it, forcing false counts cannot be refuted:
  // the original count witness is satisfiable, rather than an asserted equality.
  const valid = refute([same(x('copy'), n(1)), less(x('before'), x('after'))])
  expect('tree' in valid.proof).toBe(true)
  if ('tree' in valid.proof) expect(checkCounted(valid.g, {insts: [inst], tree: valid.proof.tree})).toBe(true)
  const invalid = refute([same(x('copy'), n(0)), same(get('Stored', n(0)), n(0)), same(x('after'), n(2)), same(x('before'), n(0))])
  expect('tree' in invalid.proof).toBe(false)
  expect('stuck' in invalid.proof && invalid.proof.stuck).toBe('sat')
})
