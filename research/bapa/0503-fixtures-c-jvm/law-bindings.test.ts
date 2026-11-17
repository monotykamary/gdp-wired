// Source-name lowering controls only: these inspect builder expressions, not native proofs.
import {expect, test} from 'bun:test'
import {Int, bool, int, nat, oneOf, rule} from '../../../core/dsl.ts'
import type {Extraction, Name} from '../../../core/extract.ts'
import {buildLaw} from '../../../core/laws.ts'

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
