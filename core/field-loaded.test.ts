import {expect, test} from 'bun:test'
import {type C, type E, type Machine, all, any, atMost, get, interpret, less, n, not, same, times, plus, x} from './machine.ts'
import {fieldLaws, selectFieldLaws, weakensField} from './field-laws.ts'
import {scope} from '../kernel/kernel.ts'

function fixture(prefix = '', stride = 8): Machine {
  const i = prefix + 'i', j = prefix + 'j', size = prefix + 'size', z = prefix + 'cell'
  const rows = prefix + 'Rows', source = prefix + 'Source', marker = prefix + 'Marker', f = prefix + 'Version', g = prefix + 'Term'
  const phase = prefix + 'phase', ready = prefix + 'ready', flag = prefix + 'load'
  const lo = times(stride, x(i)), window = all(atMost(lo, x(z)), less(x(z), plus(lo, n(stride))))
  const column: E = {op: 'sub', a: x(z), b: lo}
  return {name: prefix + 'loaded rows', params: [size], inputs: [i, j], state: {[phase]: n(0), [ready]: n(1)},
    maps: {[rows]: 0, [source]: 0, [marker]: 0, [f]: 0, [g]: 0}, assume: less(x(i), x(size)),
    step: {flags: {[flag]: all(same(x(phase), n(0)), same(x(ready), n(1))),
      fields: same(get(f, x(i)), get(g, x(i))), read: same(get(rows, plus(times(stride, x(i)), x(j))), n(1))},
      maps: {[rows]: {each: z, value: {op: 'if', c: all({op: 'flag', name: flag}, window), then: get(source, column), else: get(rows, x(z))}},
        [marker]: {key: x(i), value: {op: 'if', c: {op: 'flag', name: flag}, then: n(1), else: get(marker, x(i))}}}}}
}
const loadLaws = (m: Machine) => fieldLaws(m).filter(law => law.name.includes(' row is '))
const rowWrite = (m: Machine) => {
  const write = m.step.maps!.Rows!
  if (!('each' in write) || write.value.op !== 'if') throw Error('fixture row shape')
  return write.value
}
const markerWrite = (m: Machine) => {
  const write = m.step.maps!.Marker!
  if ('each' in write || write.value.op !== 'if') throw Error('fixture marker shape')
  return write.value
}

test('loaded row families are structural under renaming and multiple strides', () => {
  for (const prefix of ['', 'other_']) for (const stride of [4, 8]) {
    const m = fixture(prefix, stride), laws = fieldLaws(m), loads = loadLaws(m)
    expect(loads).toHaveLength(3)
    expect(laws.filter(law => law.name.includes('and ' + prefix + 'Marker[a]=' + prefix + 'Marker[b]=1'))).toHaveLength(1)
    expect(new Set(laws.map(law => JSON.stringify(law.holds))).size).toBe(laws.length)
    expect(() => scope(m, laws)).not.toThrow()
    expect(fieldLaws(m)).toEqual(laws)
  }
})

test('a minimal admitted singleton suppresses later load guards, not prior families', () => {
  const m = fixture(), laws = fieldLaws(m), loads = laws.filter(law => law.name.includes(' row is ')), whole = loads[0]!, first = loads[1]!, second = loads[2]!
  expect(weakensField.get(first)).toBe(whole)
  expect(weakensField.get(second)).toBe(whole)
  expect(selectFieldLaws(laws, law => loads.includes(law))).toEqual([whole])
  const visited: string[] = []
  expect(selectFieldLaws(laws, law => { visited.push(law.name); return law === first || law === second })).toEqual([first])
  expect(visited).not.toContain(second.name)
  expect(selectFieldLaws(laws, law => law === second)).toEqual([second])
  const prior = laws.filter(law => !law.name.includes(' row is ') && !law.name.includes('and Marker[a]=Marker[b]'))
  expect(selectFieldLaws(prior, () => true)).toEqual(prior)
})

test('compiled Boolean marker muxes retain the direct load shape', () => {
  const direct = fixture(), compiled = fixture(), flag: C = {op: 'flag', name: 'load'}
  const marker = markerWrite(compiled)
  marker.c = any(all(flag, atMost(n(0), n(0))), all(not(flag), same(get('Marker', x('i')), n(1))))
  marker.then = n(1); marker.else = n(0)
  expect(loadLaws(compiled)).toEqual(loadLaws(direct))
  const a = interpret(direct), b = interpret(compiled)
  for (const phase of [0, 1]) for (const ready of [0, 1]) for (const old of [0, 1]) {
    const state = {scalars: {phase, ready}, maps: {Rows: new Map(), Source: new Map(), Marker: new Map([[0, old]]), Version: new Map(), Term: new Map()}}
    expect(a.step({size: 1}, state, {i: 0, j: 0}).maps.Marker?.get(0) ?? 0).toBe(b.step({size: 1}, state, {i: 0, j: 0}).maps.Marker?.get(0) ?? 0)
  }
})

test('negated or merely disjunctive marker flags do not establish a load marker', () => {
  for (const condition of [not({op: 'flag', name: 'load'}), any({op: 'flag', name: 'load'}, same(x('ready'), n(0)))]) {
    const m = fixture(); markerWrite(m).c = condition
    expect(loadLaws(m)).toEqual([])
  }
})

test('the load read must share a positive flag and both exact row-window bounds', () => {
  const flag: C = {op: 'flag', name: 'load'}, lo = times(8, x('i')), z = x('cell')
  const invalid: C[] = [flag, all(flag, atMost(lo, z)), all(flag, less(z, plus(lo, n(8)))),
    all(flag, atMost(lo, z), less(z, plus(lo, n(4)))),
    all(not(flag), atMost(lo, z), less(z, plus(lo, n(8))))]
  for (const condition of invalid) {
    const m = fixture(); rowWrite(m).c = condition
    expect(loadLaws(m)).toEqual([])
  }
  const m = fixture(), value = rowWrite(m), previous = value.then
  value.then = value.else; value.else = previous
  expect(loadLaws(m)).toEqual([])
})

test('mismatched marker keys and source strides are not guessed', () => {
  const keyed = fixture(), marker = keyed.step.maps!.Marker!
  if ('each' in marker) throw Error('fixture marker shape')
  marker.key = x('j')
  expect(loadLaws(keyed)).toEqual([])
  const shifted = fixture()
  rowWrite(shifted).then = get('Source', {op: 'sub', a: x('cell'), b: times(4, x('i'))})
  expect(loadLaws(shifted)).toEqual([])
})

test('nested conjunctions expose singleton guards without capturing binder names', () => {
  const m = fixture()
  m.state['a$field'] = n(0); m.inputs.push('b$field')
  m.step.flags!.load = {op: 'and', xs: [{op: 'and', xs: [same(x('phase'), n(0))]}, same(x('ready'), n(1))]}
  const laws = loadLaws(m)
  expect(laws).toHaveLength(3)
  expect(laws[0]!.forall).not.toBe('a$field')
  expect(() => scope(m, laws)).not.toThrow()
})
