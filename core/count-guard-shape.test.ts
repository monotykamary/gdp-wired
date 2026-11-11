import {expect, test} from 'bun:test'
import {type Law, type Machine, all, get, n, same, x} from './machine.ts'
import {discoverCountGuardShape} from './count-guard-shape.ts'
import {discoverCountRowCopy} from './count-copy-shape.ts'
import {discoverCountThresholdWrite} from './count-write-shape.ts'
import {prepareGuardCountContext} from './count-guard-context.ts'
function fixture(prefix: string) {
  const name = (suffix: string) => prefix + suffix, key = (a: string, b: string) => ({op: 'add' as const, a: {op: 'mul' as const, k: 16, a: x(a)}, b: x(b)})
  const row = same(get(name('members'), key('r', 'k')), n(1)), below = x('n')
  const m: Machine = {name: 'unrelated spelling', params: ['n'], inputs: [], state: {[name('phase')]: n(0)}, maps: {[name('members')]: 0, [name('clock')]: 0, [name('epoch')]: 0}, step: {}, counts: {
    [name('votes')]: {j: 'r', lo: 'q', key: 'k', base: 16, below, body: {op: 'if', c: all(row, {op: '<', a: get(name('clock'), x('k')), b: get(name('epoch'), x('q'))}), then: n(1), else: n(0)}},
    [name('rows')]: {j: 'r', key: 'k', below, body: {op: 'if', c: row, then: n(1), else: n(0)}}
  }}
  const law: Law = {name: 'arbitrary claim', forall: 'a', keys: ['b'], holds: {op: '<=', a: {op: 'mul', k: 2, a: get(name('votes'), key('a', 'b'))}, b: get(name('rows'), x('a'))}}
  const phase: Law = {name: 'arbitrary existing premise', forall: 't', holds: {op: 'or', xs: [{op: 'not', x: same(x(name('phase')), n(0))}, same(get(name('epoch'), x('t')), n(0))]}}
  return {m, law, phase, name}
}
test('guard shape discovery is independent of protocol and field names', () => {
  for (const prefix of ['alpha_', 'different_']) {
    const {m, law, phase, name} = fixture(prefix), before = JSON.stringify(m), shape = discoverCountGuardShape(m, law, [law, phase])
    expect(shape?.voteMap).toBe(name('votes')); expect(shape?.rowMap).toBe(name('rows')); expect(shape?.membershipMap).toBe(name('members'))
    expect(shape?.memberField).toBe(name('clock')); expect(shape?.thresholdField).toBe(name('epoch'))
    expect(shape?.phase).toEqual({name: name('phase'), laws: [phase]}); expect(JSON.stringify(m)).toBe(before)
  }
})
test('a different coefficient or missing row predicate is outside this strategy', () => {
  const {m, law, phase, name} = fixture('renamed_'), changed = structuredClone(law)
  if(changed.holds.op!=='<=')throw Error('fixture shape')
  changed.holds.a = {op: 'mul', k: 3, a: get(name('votes'), {op: 'add', a: {op: 'mul', k: 16, a: x('a')}, b: x('b')})}
  expect(discoverCountGuardShape(m, changed, [phase])).toBeUndefined()
  const bad = structuredClone(m); bad.counts![name('rows')]!.body = n(1)
  expect(discoverCountGuardShape(bad, law, [phase])).toBeUndefined()
})
test('row-copy discovery follows renamed writes and rejects the wrong operation', () => {
  for (const prefix of ['copy_', 'renamed_']) {
    const {m, law, phase, name} = fixture(prefix), flag = name('transfer'), from = name('source'), to = name('destination')
    m.inputs = ['op', from, to]
    m.step.flags = {[flag]: all(same(x('op'), n(6)), same(x(name('phase')), n(1)))}
    m.step.maps = {
      [name('epoch')]: {each: 'index', value: {op: 'if', c: all({op: 'flag', name: flag}, same(x('index'), x(to))), then: get(name('epoch'), x(from)), else: get(name('epoch'), x('index'))}},
      [name('members')]: {each: 'cell', value: {op: 'if', c: {op: 'flag', name: flag}, then: n(1), else: n(0)}}
    }
    const shape = discoverCountGuardShape(m, law, [law, phase])!
    expect(discoverCountRowCopy(m, shape, {name: 'op', value: 6})).toEqual({from, to, guard: flag})
    expect(discoverCountRowCopy(m, shape, {name: 'op', value: 5})).toBeUndefined()
    delete m.step.maps[name('members')]
    expect(discoverCountRowCopy(m, shape, {name: 'op', value: 6})).toBeUndefined()
  }
})

test('threshold-write discovery identifies renamed input and committed sets', () => {
  for (const increment of [0, 1] as const) {
    const {m, law, phase, name} = fixture('write_' + increment + '_'), source = name('source'), selected = name('set'), committed = name('quorum'), guard = name('act')
    m.inputs = ['op', source]; m.inputMaps = [selected, committed]
    const member = (map: string, key: string) => ({op: '<=' as const, a: n(1), b: get(map, x(key))})
    m.counts![name('selectedSize')] = {j: 'r', key: 'k', below: x('n'), body: {op: 'if', c: member(selected, 'k'), then: n(1), else: n(0)}}
    m.counts![name('committedSize')] = {j: 'r', key: 'k', below: x('n'), body: {op: 'if', c: member(committed, 'k'), then: n(1), else: n(0)}}
    m.step.flags = {[guard]: all(same(x('op'), n(5)), member(selected, source), {op: 'flag', name: name('committed')}), [name('committed')]: {op: 'all', key: 'member', c: member(committed, 'member')}}
    const value = get(name('clock'), x(source))
    m.step.maps = {[name('epoch')]: {each: 'index', value: {op: 'if', c: all({op: 'flag', name: guard}, same(x('index'), x(source))), then: increment ? {op: 'add', a: value, b: n(1)} : value, else: get(name('epoch'), x('index'))}}}
    const shape = discoverCountGuardShape(m, law, [law, phase])!
    expect(discoverCountThresholdWrite(m, shape, {name: 'op', value: 5})).toEqual({source, guard, increment, input: selected, inputCount: name('selectedSize'), committedInput: committed, committedCount: name('committedSize')})
    const context = prepareGuardCountContext(m, law, [law, phase])!
    expect(context).toBeDefined()
    expect(discoverCountThresholdWrite(context.machine, shape, {name: 'op', value: 5})).toEqual(discoverCountThresholdWrite(m, shape, {name: 'op', value: 5}))
    expect(discoverCountThresholdWrite(m, shape, {name: 'op', value: 4})).toBeUndefined()
    m.counts![name('ambiguous')] = structuredClone(m.counts![name('selectedSize')]!)
    expect(discoverCountThresholdWrite(m, shape, {name: 'op', value: 5})).toBeUndefined()
  }
})

test('guard context is a fresh conservative extension and rejects ambiguous carried counts', () => {
  const {m, law, phase, name} = fixture('context_'), input = name('selected')
  m.inputMaps = [input]
  m.counts![name('selectedSize')] = {j: 'r', key: 'k', below: x('n'), body: {op: 'if', c: {op: '<=', a: n(1), b: get(input, x('k'))}, then: n(1), else: n(0)}}
  const saved = JSON.stringify(m), context = prepareGuardCountContext(m, law, [law, phase])
  expect(context).toBeDefined(); expect(context?.original).toBe(m)
  expect(JSON.stringify(m)).toBe(saved)
  expect(Object.keys(context!.machine.counts!).length).toBe(Object.keys(m.counts!).length + 6)
  for (const [map, count] of Object.entries(m.counts!)) expect(context!.machine.counts![map]).toEqual(count)
  expect(context!.machine.step).toBe(m.step)
  m.counts![name('ambiguous')] = structuredClone(m.counts![name('selectedSize')]!)
  expect(prepareGuardCountContext(m, law, [law, phase])).toBeUndefined()
})
test('guard context does not allocate a count over a declared parameter name', () => {
  const {m, law, phase, name} = fixture('collision_'), input = name('selected')
  m.inputMaps = [input]
  m.counts![name('selectedSize')] = {j: 'r', key: 'k', below: x('n'), body: {op: 'if', c: {op: '<=', a: n(1), b: get(input, x('k'))}, then: n(1), else: n(0)}}
  m.params.push(name('votes') + '$restricted$' + input)
  expect(prepareGuardCountContext(m, law, [law, phase])).toBeUndefined()
})
test('ambiguous zero phases are resolved only by a unique common write guard', () => {
  const {m, law, phase, name} = fixture('gated_'), other = name('selection')
  m.state[other] = n(0)
  const otherLaw: Law = {name: 'other existing zero phase', forall: 't', holds: {op: 'or', xs: [{op: 'not', x: same(x(other), n(0))}, same(get(name('epoch'), x('t')), n(0))]}}
  const family = [law, phase, otherLaw]
  expect(discoverCountGuardShape(m, law, family)?.phase).toBeUndefined()
  m.step.flags = {advance: same(x(name('phase')), n(1))}
  m.step.maps = {[name('epoch')]: {each: 'cell', value: {op: 'if', c: {op: 'flag', name: 'advance'}, then: n(1), else: get(name('epoch'), x('cell'))}}}
  expect(discoverCountGuardShape(m, law, family)?.phase).toEqual({name: name('phase'), laws: [phase]})
  m.step.flags.reset = same(x(other), n(1))
  m.step.maps[name('epoch')] = {each: 'cell', value: {op: 'if', c: {op: 'flag', name: 'advance'}, then: n(1), else: {op: 'if', c: {op: 'flag', name: 'reset'}, then: n(0), else: get(name('epoch'), x('cell'))}}}
  expect(discoverCountGuardShape(m, law, family)?.phase).toBeUndefined()
})
test('discovery does not invent a phase premise', () => {
  const {m, law} = fixture('plain_')
  expect(discoverCountGuardShape(m, law, [law])?.phase).toBeUndefined()
})
