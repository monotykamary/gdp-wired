import {expect, test} from 'bun:test'
import {fieldLaws, weakensField} from './field-laws.ts'
import {type Machine, all, get, less, n, same, times, plus, tuple, x} from './machine.ts'
import {trueSmall} from './exists.ts'
import {proveLaws} from '../kernel/prove.ts'
import {scope} from '../kernel/kernel.ts'

const machine = (broken = false): Machine => ({
  name: 'replicated fields', params: ['size'], inputs: ['i', 'value'], state: {},
  maps: {Role: 0, Epoch: 0, Copy: 0}, assume: less(x('i'), x('size')),
  step: {
    flags: {equal: same(get('Epoch', x('i')), get('Copy', x('i'))), active: same(get('Role', x('i')), n(1))},
    maps: {Role: {key: x('i'), value: n(1)}, Epoch: {key: x('i'), value: x('value')}, Copy: {key: x('i'), value: broken ? n(0) : x('value')}},
  },
})
const selected = (m: Machine) => fieldLaws(m).find(l => l.name === 'fields: Role[a]=1 -> Copy[a]=Epoch[a]')!

test('field equality is proposed from structure and proven by the ordinary kernel', () => {
  const m = machine(), law = selected(m)
  expect(law).toBeDefined()
  expect(trueSmall(m, [law])).toBe(true)
  const result = proveLaws(m, [law])
  expect(result.proven).toBe(true)
  expect(result.checked).toBe(true)
})

test('the same candidate on a broken write is filtered and not proven', () => {
  const m = machine(true), law = selected(m)
  expect(law).toBeDefined()
  expect(trueSmall(m, [law])).toBe(false)
  expect(proveLaws(m, [law]).proven).toBe(false)
})

test('cross-record field equality can guard an ordering, without input leakage', () => {
  const m = machine(), laws = fieldLaws(m)
  expect(laws.some(l => l.name === 'fields: Role[a]=1 -> Copy[a]=Copy[b] -> Epoch[b]<=Epoch[a]')).toBe(true)
  expect(() => scope(m, laws)).not.toThrow()
  expect(new Set(laws.map(l => l.name)).size).toBe(laws.length)
  expect(fieldLaws(m)).toEqual(laws)
})

test('ambiguous domains and a single numeric field are not guessed', () => {
  const m = machine()
  expect(fieldLaws({...m, params: ['size', 'other'], assume: all(m.assume!, less(x('i'), x('other')))})).toEqual([])
  expect(fieldLaws({...m, step: {...m.step, flags: {self: same(get('Epoch', x('i')), get('Epoch', x('i')))}}})).toEqual([])
})

test('two equal fields can identify a tuple-keyed row, with an independent member', () => {
  const base = machine(), m: Machine = {...base, maps: {...base.maps, Contents: 0}, relations: {Contents: ['Item', 'Item']}}
  const row = fieldLaws(m).find(l => l.name === 'fields: Copy[a]=Copy[b] and Epoch[a]=Epoch[b] -> Contents rows agree')!
  expect(row).toBeDefined()
  expect(row.keys).toHaveLength(2)
  expect(() => scope(m, [row])).not.toThrow()
  expect(trueSmall(m, [row])).toBe(true)
  // The same metadata does not let numeric field equality prove mutable content.
  const broken: Machine = {...m, step: {...m.step, maps: {...m.step.maps, Contents: {key: tuple([x('i'), x('i')]), value: n(1)}}}}
  expect(proveLaws(broken, [row]).proven).toBe(false)
})

test('composed-key rows use their encoded base and still require induction', () => {
  const base = machine(), packed = (a: ReturnType<typeof x>, b: ReturnType<typeof x>) => plus(times(8, a), b)
  const m: Machine = {...base, inputs: [...base.inputs, 'k'], maps: {...base.maps, Contents: 0}, step: {...base.step,
    flags: {...base.step.flags, read: same(get('Contents', packed(x('i'), x('k'))), n(1))},
    maps: {...base.step.maps, Contents: {key: packed(x('i'), x('k')), value: n(1)}}}}
  const rows = fieldLaws(m).filter(l => l.name.endsWith('Contents rows agree'))
  expect(rows).toHaveLength(1)
  expect(fieldLaws(m, false).some(l => l.name.endsWith('Contents rows agree'))).toBe(false)
  expect(JSON.stringify(rows[0])).toContain('"k":8')
  expect(() => scope(m, rows)).not.toThrow()
  expect(proveLaws(m, rows).proven).toBe(false)
})

test('generated binders do not capture state, request or flag variables', () => {
  const m = machine()
  m.state['a$field'] = n(0)
  m.step.flags!.collision = same(x('a$field'), x('b$field'))
  m.inputs.push('b$field')
  const law = selected(m)
  expect(law.forall).not.toBe('a$field')
  expect(() => scope(m, fieldLaws(m))).not.toThrow()
})

test('a row loaded from a plain-key map under a marker proposes the load law and the marker-guarded row agreement', () => {
  const base = machine(), row = (r: ReturnType<typeof x>, k: ReturnType<typeof x>) => plus(times(8, r), k), z = x('z$w')
  const inRow = all({op: '<=', a: times(8, x('i')), b: z}, less(z, plus(times(8, x('i')), n(8))))
  const m: Machine = {...base, inputs: [...base.inputs, 'k'], state: {open: n(1)}, maps: {...base.maps, Contents: 0, Source: 0, Loaded: 0}, step: {...base.step,
    flags: {...base.step.flags, read: same(get('Contents', row(x('i'), x('k'))), n(1)), loads: all(same(x('value'), n(7)), same(x('open'), n(1)))},
    maps: {...base.step.maps,
      Contents: {each: 'z$w', value: {op: 'if', c: {op: 'and', xs: [{op: 'and', xs: [{op: 'flag', name: 'loads'}, inRow]}, same(get('Source', {op: 'sub', a: z, b: times(8, x('i'))}), n(1))]}, then: n(1), else: get('Contents', z)}},
      Loaded: {key: x('i'), value: {op: 'if', c: {op: 'flag', name: 'loads'}, then: n(1), else: get('Loaded', x('i'))}}}}}
  const laws = fieldLaws(m), names = laws.map(l => l.name)
  const whole = laws.find(l => l.name === 'fields: Loaded[a]=1 -> Contents row is Source')!, phased = laws.find(l => l.name === 'fields: Loaded[a]=1 and open=1 -> Contents row is Source')!
  expect(whole).toBeDefined()
  expect(phased).toBeDefined()
  expect(weakensField.get(phased)).toBe(whole)
  const guarded = laws.filter(l => l.name.includes('and Loaded[a]=Loaded[b]=1 -> Contents rows agree'))
  expect(guarded.length).toBeGreaterThan(0)
  for (const l of guarded) expect(weakensField.get(l)?.name).toBe(l.name.replace(' and Loaded[a]=Loaded[b]=1', ''))
  expect(() => scope(m, laws)).not.toThrow()
  expect(new Set(names).size).toBe(names.length)
  // Without the marker write nothing of the family is proposed; the earlier candidates keep their order.
  const plain: Machine = {...m, step: {...m.step, maps: {...m.step.maps, Loaded: {key: x('i'), value: n(0)}}}}
  expect(fieldLaws(plain).some(l => l.name.includes('row is Source') || l.name.includes('Loaded[a]=Loaded[b]'))).toBe(false)
  expect(laws.slice(0, fieldLaws(plain).length).map(l => l.name)).toEqual(fieldLaws(plain).map(l => l.name))
})
