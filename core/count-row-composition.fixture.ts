import {type Law, type Machine, all, any, get, n, not, same, x} from './machine.ts'
export function rowCompositionFixture() {
  const packed = (a: string, b: string) => ({op: 'add' as const, a: {op: 'mul' as const, k: 4, a: x(a)}, b: x(b)}), below = x('size')
  const member = same(get('edge', packed('countrow', 'countmember')), n(1))
  const m: Machine = {name: 'renamed deferred rows', params: ['size'], inputs: ['mode', 'src', 'dst'], state: {}, maps: {edge: 0, tick: 0, limit: 0, marker: 0}, pre: all({op: '<=', a: n(1), b: below}, {op: '<=', a: below, b: n(4)}), assume: any(...[0, 1, 2].map(i => same(x('mode'), n(i)))), counts: {
    votes: {j: 'countrow', lo: 'countother', key: 'countmember', base: 4, below, body: {op: 'if', c: all(member, {op: '<', a: get('tick', x('countmember')), b: get('limit', x('countother'))}), then: n(1), else: n(0)}},
    rows: {j: 'countrow', key: 'countmember', below, body: {op: 'if', c: member, then: n(1), else: n(0)}}
  }, step: {flags: {copy: same(x('mode'), n(2))}, maps: {
    edge: {each: 'cell', value: {op: 'if', c: {op: 'flag', name: 'copy'}, then: get('edge', x('cell')), else: get('edge', x('cell'))}},
    limit: {each: 'r', value: {op: 'if', c: all({op: 'flag', name: 'copy'}, same(x('r'), x('dst'))), then: get('limit', x('src')), else: get('limit', x('r'))}}
  }}}
  const guard = all(same(get('limit', x('a')), get('limit', x('b'))), same(get('marker', x('a')), n(1)), same(get('marker', x('b')), n(1)))
  const law: Law = {name: 'same-version marked rows agree', forall: 'a', keys: ['b', 'c'], holds: any(not(guard), same(get('edge', packed('a', 'c')), get('edge', packed('b', 'c'))))}
  const count: Law = {name: 'existing guarded row count', forall: 'a', keys: ['b'], holds: {op: '<=', a: {op: 'mul', k: 2, a: get('votes', packed('a', 'b'))}, b: get('rows', x('a'))}}
  const marker: Law = {name: 'existing inactive marker', forall: 'r', holds: same(get('marker', x('r')), n(0))}
  return {m, law, family: [law, count, marker]}
}
