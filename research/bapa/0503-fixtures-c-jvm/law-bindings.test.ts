// Source-name lowering controls only: these inspect builder expressions, not native proofs.
import {expect, test} from 'bun:test'
import {Int, bool, int, nat, no, oneOf, rule} from '../../../core/dsl.ts'
import type {Extraction, Name} from '../../../core/extract.ts'
import {buildLaw, namesWithClock} from '../../../core/laws.ts'

const r = rule('method-specific answers').inputs({method: oneOf('hit', 'soft', 'other'), hitRaised: bool, softRaised: bool, genericRaised: bool}).state({field: false})
const answers: Name[] = [
  {code: 'method', rule: 'method', role: 'method'},
  {code: 'Remote.ping.raises', rule: 'hitRaised', role: 'answer', method: 'hit', native: {kind: 'raises', key: 'Remote.ping'}},
  {code: 'Remote.ping.raises', rule: 'softRaised', role: 'answer', method: 'soft', native: {kind: 'raises', key: 'Remote.ping'}},
]
const extraction = (names = answers): Extraction => ({ok: true, refusals: [], notes: [], rule: r as unknown as Extraction['rule'], names})

for (const method of ['hit', 'soft'] as const) test(`answer lowering selects ${method}, never the first alias`, () => {
  const built = buildLaw(extraction(), {name: method, expr: 'Remote.ping.raises', method})
  const expected = r.stepLaw('expected', b => method === 'hit' ? b.hitRaised : b.softRaised)
  expect(built.kind).toBe('step')
  expect(built.law.then).toEqual(expected.then)
})

test('scalar fixed-list lowering retains before/after values and before indices', () => {
  const lists = rule('fixed list names').inputs({method: oneOf('put'), x: int}).state({head: 0, output: 0}).items({buf: int}, {buf: 4})
  const x: Extraction = {ok: true, refusals: [], notes: [], rule: lists as unknown as Extraction['rule'], names: [
    {code: 'method', rule: 'method', role: 'method'}, {code: 'head', rule: 'head', role: 'state'},
    {code: 'x', rule: 'x', role: 'input', method: 'put'}, {code: 'buf', rule: 'buf', role: 'state', list: {scalar: true, length: 4}},
    {code: 'result.data', rule: 'output', role: 'result', method: 'put'},
  ]}
  const put = buildLaw(x, {name: 'write at old head', expr: 'buf[old(head)] == x', method: 'put'})
  expect(put.law.then).toEqual(lists.stepLaw('expected', (b, a) => a.buf.at(b.head).eq(b.x)).then)
  const out = buildLaw(x, {name: 'return old item', expr: 'result.data == old(buf[head])', method: 'put'})
  expect(out.law.then).toEqual(lists.stepLaw('expected', (b, a) => Int.of(a.output).eq(b.buf.at(b.head))).then)
  // No map-position or object-identity equality is invented for this new name.
  expect(() => buildLaw(x, {name: 'not scalar', expr: 'buf == old(buf)', method: 'put'})).toThrow('a list where a number is read')
})

test('an old index alone marks a scalar-list expression as a step law', () => {
  const lists = rule('list role discovery').state({head: 0}).items({buf: nat}, {buf: 4})
  const x: Extraction = {ok: true, refusals: [], notes: [], rule: lists as unknown as Extraction['rule'], names: [
    {code: 'head', rule: 'head', role: 'state'}, {code: 'buf', rule: 'buf', role: 'state', list: {scalar: true, length: 4}},
  ]}
  expect(buildLaw(x, {name: 'old index', expr: 'buf[old(head)] >= 0'}).kind).toBe('step')
})

test('whole-map nil comparison uses the selected map environment, in either operand direction', () => {
  const maps = rule('map absence').inputs({method: oneOf('Bump')}).state({Seen_nil: false}).maps({Seen: nat})
  const names: Name[] = [
    {code: 'method', rule: 'method', role: 'method'},
    {code: 'Seen', rule: 'Seen', role: 'state', none: 'Seen_nil', map: {fields: ['value']}},
  ]
  const x: Extraction = {ok: true, refusals: [], notes: [], rule: maps as unknown as Extraction['rule'], names}
  for (const old of [false, true]) for (const reversed of [false, true]) for (const unequal of [false, true]) {
    const read = old ? 'old(Seen)' : 'Seen', op = unequal ? '!=' : '=='
    const expr = reversed ? `nil ${op} ${read}` : `${read} ${op} nil`
    const built = buildLaw(x, {name: expr, expr, method: 'Bump'})
    const expected = maps.stepLaw('expected', (b, a) => {
      const absent = old ? b.Seen_nil : a.Seen_nil
      return unequal ? absent.not() : absent
    })
    expect(built.law.then).toEqual(expected.then)
  }
  const refusal = buildLaw(x, {name: 'nil bump is refused', expr: 'old(Seen) == nil implies false', method: 'Bump'})
  expect(refusal.law.then).toEqual(maps.stepLaw('expected', b => b.Seen_nil.implies(no)).then)
  // No structural equality between two non-null model maps is introduced.
  expect(() => buildLaw(x, {name: 'map equality unsupported', expr: 'Seen == old(Seen)', method: 'Bump'})).toThrow('a map where a number is read')
  const withoutNil: Extraction = {...x, names: names.map<Name>(n => n.code === 'Seen' ? {code: 'Seen', rule: 'Seen', role: 'state', map: {fields: ['value']}} : n)}
  expect(() => buildLaw(withoutNil, {name: 'no invented nil flag', expr: 'Seen == nil', method: 'Bump'})).toThrow('is never None here')
})

test('synthetic Date clock names require actual native clock readings without changing explicit inputs', () => {
  const clock = rule('synthetic clock name').inputs({now: nat}).state({n: 0})
  const names: Name[] = [{code: 'n', rule: 'n', role: 'state'}]
  const x: Extraction = {ok: true, refusals: [], notes: [], rule: clock as unknown as Extraction['rule'], names}
  expect(namesWithClock(x)).toEqual([...names, {code: 'now', rule: 'now', role: 'clock', native: {kind: 'clock', key: 'now'}}])
  expect(x.names).toBe(names)
  expect(names).toHaveLength(1)
  const explicit: Name[] = [...names, {code: 'now', rule: 'now', role: 'input', method: 'tick'}]
  expect(namesWithClock({...x, names: explicit})).toBe(explicit)
  expect(explicit[1]!.native).toBeUndefined()
})

test('an unscoped method-specific answer is ambiguous', () => {
  expect(() => buildLaw(extraction(), {name: 'ambiguous', expr: 'Remote.ping.raises'})).toThrow('ambiguous answered call')
})

test('a genuinely generic answer is used only after exact method selection', () => {
  const names: Name[] = [...answers, {code: 'Remote.ping.raises', rule: 'genericRaised', role: 'answer', native: {kind: 'raises', key: 'Remote.ping'}}]
  const built = buildLaw(extraction(names), {name: 'generic', expr: 'Remote.ping.raises', method: 'other'})
  expect(built.law.then).toEqual(r.stepLaw('expected', b => b.genericRaised).then)
  const hit = buildLaw(extraction(names), {name: 'specific', expr: 'Remote.ping.raises', method: 'hit'})
  expect(hit.law.then).toEqual(r.stepLaw('expected', b => b.hitRaised).then)
})

test('a scoped answer cannot bind an unrelated method', () => {
  expect(() => buildLaw(extraction(), {name: 'wrong owner', expr: 'Remote.ping.raises', method: 'other'})).toThrow('no answer belongs to other')
})

test('source state still takes precedence over a same-named answer', () => {
  const x = extraction([...answers, {code: 'Remote.ping.raises', rule: 'field', role: 'state'}])
  const built = buildLaw(x, {name: 'state', expr: 'Remote.ping.raises', method: 'soft'})
  expect(built.law.then).toEqual(r.stepLaw('expected', (_b, a) => a.field).then)
})
