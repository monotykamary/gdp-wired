import {expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, all, any, get, n, not, same, x} from './machine.ts'
import {discoverRowAgreement} from './row-agreement-shape.ts'
function fixture() {
  const at = (row: string): E => ({op: 'add', a: {op: 'mul', k: 8, a: x(row)}, b: x('column')})
  const copied = (map: string, flag = 'transfer'): E => ({op: 'if', c: all({op: 'flag', name: flag}, same(x('key'), x('destination'))), then: get(map, x('source')), else: get(map, x('key'))})
  const m: Machine = {name: 'renamed versioned rows', params: ['size'], inputs: ['source', 'destination'], state: {}, maps: {cells: 0, version: 0, epoch: 0, marker: 0, unrelated: 0}, step: {maps: {
    cells: {each: 'key', value: copied('cells')}, version: {each: 'key', value: copied('version')}, epoch: {each: 'key', value: copied('epoch')}, unrelated: {each: 'key', value: copied('unrelated', 'other')}
  }}}
  const guard = all(same(get('version', x('first')), get('version', x('second'))), same(get('epoch', x('first')), get('epoch', x('second'))), same(get('marker', x('first')), n(1)), same(get('marker', x('second')), n(1)))
  const law: Law = {name: 'arbitrary label', forall: 'first', keys: ['second', 'column'], holds: any(not(guard), same(get('cells', at('first')), get('cells', at('second'))))}
  return {m, law, at, guard}
}
test('versioned row agreement is selected by syntax, not names', () => {
  const {m, law} = fixture(), before = JSON.stringify([m, law]), found = discoverRowAgreement(m, law)
  expect(found).toMatchObject({map: 'cells', width: 8, left: 'first', right: 'second', column: 'column', fields: ['epoch', 'version'], markers: [{map: 'marker', value: 1}]})
  expect(JSON.stringify([m, law])).toBe(before)
})
test('a sibling field not moved with the row is not the versioned-row strategy', () => {
  const {m, law} = fixture(); law.holds = JSON.parse(JSON.stringify(law.holds).replaceAll('epoch', 'unrelated')) as C
  expect(discoverRowAgreement(m, law)).toBeUndefined()
})
test('wrong stride, unmatched marker and count-valued rows decline', () => {
  const {m, law, at, guard} = fixture(), wrong: E = {op: 'add', a: {op: 'mul', k: 9, a: x('second')}, b: x('column')}
  expect(discoverRowAgreement(m, {...law, holds: any(not(guard), same(get('cells', at('first')), get('cells', wrong)))})).toBeUndefined()
  const unmatched = JSON.parse(JSON.stringify(law).replace('"value":1', '"value":2')) as Law
  expect(discoverRowAgreement(m, unmatched)).toBeUndefined()
  m.counts = {cells: {j: 'row', key: 'member', below: x('size'), body: n(0)}}
  expect(discoverRowAgreement(m, law)).toBeUndefined()
})
