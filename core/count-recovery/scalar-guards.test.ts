import {expect, test} from 'bun:test'
import {type C, type E, type Machine, all, any, get, ite, less, n, not, same, x} from '../machine.ts'
import {type CountCert, type CountDecl, type CountInst, type Path, canon, facts} from '../../kernel/kernel.ts'
import {countScalarGuards} from './scalar-guards.ts'

const bit = (c: C): E => ite(c, n(1), n(0))
function assume(path: Path, c: C): Path {
  const out = new Map(path)
  for (const lin of facts(c, path)) out.set(canon(lin), {lin, holds: true})
  return out
}
function fixture(prefix = '') {
  const name = (s: string) => prefix + s
  const actor = x(name('actor')), row = x(name('row')), member = x(name('member'))
  const epoch = (key: E) => get(name('Era'), key), version = (key: E) => get(name('Revision'), key)
  const gate = name('aligned'), flagKey = name('participant'), fk = x(flagKey)
  const ds: CountDecl[] = [
    {map: name('Earlier'), j: name('rowParameter'), key: name('member'), below: n(12), body: bit(all(
      same(get(name('Membership'), member), n(1)), any(
        less(epoch(x(name('rowParameter'))), epoch(member)),
        all(same(epoch(x(name('rowParameter'))), epoch(member)), less(version(x(name('rowParameter'))), version(member))))))},
    {map: name('Incoming'), j: name('unused'), key: name('rawMember'), below: n(12), body: get(name('Parcel'), x(name('rawMember')))},
  ]
  const reads: CountCert['reads'] = [[name('before'), name('Earlier'), row], [name('incoming'), name('Incoming'), n(0)]]
  const inst: CountInst = {wit: name('sourceWitness'), below: n(12), terms: [[1, name('before')], [1, name('incoming')]], unit: 0}
  const m: Machine = {name: 'renamed lex counts', params: [name('limit')], inputs: [name('actor'), name('otherActor')], state: {},
    maps: {[name('Era')]: 0, [name('Revision')]: 0, [name('Membership')]: 0}, inputMaps: [name('Parcel'), name('OtherParcel')], step: {flags: {
      [gate]: {op: 'all', key: flagKey, c: any(not(same(get(name('Parcel'), fk), n(1))), all(
        same(epoch(actor), epoch(fk)), same(version(fk), version(actor))))},
    }}}
  const root = assume(new Map(), same(x(`?${gate}`), n(1)))
  const run = (goal?: {name: string, hyps: C[]}, at = root) => countScalarGuards(m, ds, reads, inst, at, goal)
  return {m, ds, reads, inst, root, run, gate, actor, row, epoch, version, name}
}

for (const prefix of ['', 'renamed_']) test(`lexicographic candidates use field anchors, not row aliases (${prefix || 'plain'})`, () => {
  const f = fixture(prefix), before = JSON.stringify([f.m, f.ds, f.reads, f.inst, [...f.root]])
  const scopes = f.run(), term = less(f.epoch(f.row), f.epoch(f.actor)), eq = same(f.epoch(f.row), f.epoch(f.actor))
  expect(scopes).toContainEqual([term])
  expect(scopes).toContainEqual([eq, less(f.version(f.row), f.version(f.actor))])
  expect(scopes.length).toBeLessThanOrEqual(8)
  expect(f.run()).toEqual(scopes)
  expect(JSON.stringify([f.m, f.ds, f.reads, f.inst, [...f.root]])).toBe(before)
  for (const scope of scopes) for (const c of scope) {
    expect(['<', '<=', '=']).toContain(c.op)
    expect('a' in c && c.a.op === 'get' && c.b.op === 'get').toBe(true)
    const text = JSON.stringify(c)
    for (const forbidden of ['member', 'participant', 'rawMember', 'sourceWitness', '?aligned', 'scalar$member']) expect(text).not.toContain(forbidden)
  }
})

test('only active relevant forall flags supply anchors, preferring the positive carried count', () => {
  const f = fixture(), q = x('unrelatedKey'), other = x('otherActor')
  const unrelated: C = {op: 'all', key: 'unrelatedKey', c: any(not(same(get('OtherParcel', q), n(1))), all(
    same(f.epoch(q), f.epoch(other)), same(f.version(q), f.version(other))))}
  f.m.step.flags = {unrelated, ...f.m.step.flags}
  expect(f.run(undefined, new Map())).toEqual([])
  const unrelatedOnly = assume(new Map(), same(x('?unrelated'), n(1)))
  expect(f.run(undefined, unrelatedOnly)).toEqual([])
  const both = assume(f.root, same(x('?unrelated'), n(1)))
  expect(f.run(undefined, both)).toEqual(f.run())
  // An unrelated carried map occurring only on the negative side is not preferred.
  f.ds.push({map: 'Negative', j: 'u', key: 'negativeMember', below: n(12), body: get('OtherParcel', x('negativeMember'))})
  f.reads.push(['negative', 'Negative', n(0)])
  f.inst.terms.push([-1, 'negative'])
  expect(f.run(undefined, both)).toEqual(f.run())
})

for (const encoded of [false, true]) test(`raw and encoded flag references are traversed (${encoded})`, () => {
  const f = fixture(), ref: C = encoded ? same(x('?parcelAlias'), n(1)) : {op: 'flag', name: 'parcelAlias'}
  f.m.step.flags!.parcelAlias = {op: 'flag', name: 'parcelLeaf'}
  f.m.step.flags!.parcelLeaf = same(get('Parcel', x('participant')), n(1))
  const q = f.m.step.flags![f.gate]!
  if (q.op !== 'all') throw new Error('fixture')
  // The relevant carried map is reachable only through an alias chain here.
  q.c = all(ref, same(f.epoch(x(q.key)), f.epoch(f.actor)), same(f.version(x(q.key)), f.version(f.actor)))
  f.ds[0]!.body = bit(all(ref, less(f.epoch(x('rowParameter')), f.epoch(x('member')))))
  expect(f.run()).toContainEqual([less(f.epoch(f.row), f.epoch(f.actor))])
})

test('known root comparisons are not re-proposed and false scopes are dropped', () => {
  const f = fixture(), term = less(f.epoch(f.row), f.epoch(f.actor))
  const yes = f.run(undefined, assume(f.root, term))
  expect(yes.every(scope => !scope.some(c => JSON.stringify(c) === JSON.stringify(term)))).toBe(true)
  const no = f.run(undefined, assume(f.root, not(term)))
  expect(no.every(scope => !scope.some(c => JSON.stringify(c) === JSON.stringify(term)))).toBe(true)
  const eq = same(f.epoch(f.row), f.epoch(f.actor)), version = less(f.version(f.row), f.version(f.actor))
  expect(f.run(undefined, assume(f.root, eq))).toContainEqual([version])
})

test('optional source comparisons retain only known row/input/parameter scalar cells', () => {
  const f = fixture(), good = less(get('Extra', f.row), get('Extra', f.actor))
  const goal = {name: 'frame source', hyps: [good,
    less(get('Earlier', f.row), get('Earlier', f.actor)),
    less(get('Extra', x('sourceWitness')), get('Extra', f.actor)),
    less(get('Extra', x('foreignWitness')), get('Extra', f.actor)),
    less(get('Extra', x('before')), get('Extra', f.actor)),
    less(get('Extra', x('participant')), get('Extra', f.actor)),
    less(get('Extra', get('Nested', f.row)), get('Extra', f.actor)),
  ]}
  const scopes = f.run(goal)
  expect(scopes).toContainEqual([good])
  expect(JSON.stringify(scopes)).not.toMatch(/foreignWitness|sourceWitness|participant|Earlier|Nested|before/)
})

test('goal hints use only the candidate row pair, and lex conjunctions use distinct fields', () => {
  const f = fixture(), stranger = less(get('Foreign', f.row), get('Foreign', x('otherActor')))
  const scopes = f.run({name: 'other pair', hyps: [stranger]})
  expect(scopes).not.toContainEqual([stranger])
  expect(scopes.filter(scope => scope.length > 1).every(scope => !scope.includes(stranger))).toBe(true)
  for (const scope of scopes) if (scope.length > 1) {
    expect(scope[0]!.op).toBe('=')
    expect(scope[1]!.op).toBe('<')
  }
})

test('two-term post/pre frames use candidate-row field equalities, including their conjunction', () => {
  const f = fixture(), body = bit(same(get('Membership', x('member')), n(1)))
  f.ds[0]!.body = body
  f.ds.push({...f.ds[0]!, map: 'Earlier#'})
  f.reads.push(['after', 'Earlier#', f.actor])
  f.inst.terms = [[1, 'after'], [-1, 'before']]
  const epoch = same(f.epoch(f.row), f.epoch(f.actor)), version = same(f.version(f.row), f.version(f.actor))
  const unrelated = same(f.epoch(f.row), f.epoch(x('otherActor')))
  const goal = {name: 'equal fields imply equal member sets', hyps: [any(not(all(epoch, version)), same(get('Membership', f.row), get('Membership', f.actor))), unrelated]}
  const scopes = f.run(goal)
  expect(scopes).toContainEqual([epoch])
  expect(scopes).toContainEqual([version])
  expect(scopes).toContainEqual([epoch, version])
  expect(scopes).not.toContainEqual([unrelated])
  expect(scopes.length).toBeLessThanOrEqual(8)
})

for (const source of ['body', 'anchor']) test(`keyless frame finds its actor only in the ${source}`, () => {
  const f = fixture(), member = x('member')
  const body = source === 'body' ? bit(all(same(get('Membership', member), n(1)), same(member, f.actor))) : bit(same(get('Membership', member), n(1)))
  f.ds.push({...f.ds[0]!, map: 'Earlier#', body})
  f.reads.push(['after', 'Earlier#', f.row])
  f.inst.terms = [[1, 'incoming'], [-1, 'after']]
  const eq = same(f.epoch(f.row), f.epoch(f.actor)), version = same(f.version(f.row), f.version(f.actor))
  const unrelated = same(f.epoch(f.row), f.epoch(x('otherActor')))
  const scopes = f.run({name: 'frame source', hyps: [eq, version, unrelated]}, source === 'body' ? new Map() : f.root)
  expect(scopes).toContainEqual([eq, version])
  expect(scopes).not.toContainEqual([unrelated])
})

test('primitive Boolean partitions do not rescan or propose broad goal fields', () => {
  const f = fixture()
  f.ds[0]!.body = bit(same(get('Membership', x('member')), n(1)))
  const broad = {name: 'irrelevant scalar goal', hyps: [less(f.epoch(f.row), f.epoch(f.actor))]}
  expect(f.run(broad)).toEqual([])
})

test('an oversized or cyclic source tail does not suppress the selected count guards', () => {
  const f = fixture(), cycle: C = {op: 'and', xs: []}
  if (cycle.op === 'and') cycle.xs.push(cycle)
  const goal = {name: 'large source', hyps: [cycle, ...Array.from({length: 22000}, () => same(n(0), n(0)))]}
  expect(f.run(goal)).toEqual(f.run())
  expect(f.run(goal)).toEqual(f.run())
})

test('large candidate families stay bounded and deterministic', () => {
  const f = fixture(), hypotheses = Array.from({length: 100}, (_, i) => less(get(`Field${i}`, f.row), get(`Field${i}`, f.actor)))
  const goal = {name: 'many scalar cells', hyps: hypotheses}, scopes = f.run(goal)
  expect(scopes.length).toBe(8)
  expect(f.run(goal)).toEqual(scopes)
})

test('unknown reads, malformed ASTs, cyclic ASTs and recursive flag aliases fail conservatively', () => {
  const f = fixture()
  expect(countScalarGuards(f.m, f.ds, [['before', 'Missing', f.row]], f.inst, f.root)).toEqual([])
  const malformed = {...f.ds[0]!, body: {op: 'unexpected'} as unknown as E}
  expect(countScalarGuards(f.m, [malformed, f.ds[1]!], f.reads, f.inst, f.root)).toEqual([])
  const cycle: E = {op: 'get', map: 'Loop', key: n(0)}
  if (cycle.op === 'get') cycle.key = cycle
  expect(countScalarGuards(f.m, [{...f.ds[0]!, body: cycle}, f.ds[1]!], f.reads, f.inst, f.root)).toEqual([])
  f.m.step.flags = {a: {op: 'flag', name: 'b'}, b: same(x('?a'), n(1))}
  f.ds[0]!.body = bit({op: 'flag', name: 'a'})
  expect(f.run()).toEqual([])
})

test('packed read keys contribute only their row variables; unsupported packing is refused', () => {
  const f = fixture(), first = f.ds[0]!
  first.lo = first.j; first.j = 'high'; first.base = 32
  f.reads[0]![2] = {op: 'add', a: {op: 'mul', k: 32, a: x('highRow')}, b: f.row}
  expect(f.run()).toContainEqual([less(f.epoch(f.row), f.epoch(f.actor))])
  f.reads[0]![2] = f.row
  expect(f.run()).toEqual([])
})
