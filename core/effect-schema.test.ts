// Differential runtime and checked state-preservation tests on both pinned Effect versions.
import {expect, test} from 'bun:test'
import {Schema as S4} from 'effect'
import {Schema as S3, Effect as E3} from 'effect3'
import {Choice, Int, Str, Term, int, proveRule, proveSteps, rule, yes, type Kind, type Raw} from './dsl.ts'
import {SchemaError, fromSchema} from './effect.ts'
import {seeded} from './machine.ts'
class C4 extends S4.Class<C4>('SchemaClass4')({n: S4.Int}) { doubled() { return this.n * 2 } }
class C3 extends S3.Class<C3>('SchemaClass3')({n: S3.Int}) { doubled() { return this.n * 2 } }
const versions = [
  {
    name: '4.0.7', integer: S4.Int, bounded: S4.Int.check(S4.isGreaterThanOrEqualTo(5), S4.isLessThanOrEqualTo(7)),
    exclusive: S4.Int.check(S4.isGreaterThan(-3), S4.isLessThan(3)), fractional: S4.Int.check(S4.isBetween({minimum: -2.5, maximum: 2.5})),
    empty: S4.Int.check(S4.isGreaterThan(3), S4.isLessThan(4)), finite: S4.Union([S4.Literal(-2), S4.Literal(4)]),
    nullable: S4.NullOr(S4.Int.check(S4.isBetween({minimum: 5, maximum: 7}))),
    struct: S4.Struct({n: S4.Int.check(S4.isBetween({minimum: 5, maximum: 7})), b: S4.Boolean, status: S4.Literals(['open', 'closed'])}),
    tagged: S4.Union([S4.TaggedStruct('Set', {n: S4.Int.check(S4.isBetween({minimum: 5, maximum: 7}))}), S4.TaggedStruct('Clear', {})]),
    optional: S4.Struct({x: S4.optional(S4.Boolean)}), undefined: S4.UndefinedOr(S4.Int),
    custom: S4.Int.check(S4.makeFilter((n: number) => n !== 6)), regex: S4.String.check(S4.isPattern(/^a/)),
    branded: S4.Int.pipe(S4.brand('SchemaCount')), transform: S4.NumberFromString, cls: C4,
    acceptsInt: S4.is(S4.Int), acceptsBounded: S4.is(S4.Int.check(S4.isBetween({minimum: 5, maximum: 7}))),
    acceptsStruct: S4.is(S4.Struct({n: S4.Int.check(S4.isBetween({minimum: 5, maximum: 7})), b: S4.Boolean, status: S4.Literals(['open', 'closed'])})),
  },
  {
    name: '3.22.4', integer: S3.Int, bounded: S3.Int.pipe(S3.greaterThanOrEqualTo(5), S3.lessThanOrEqualTo(7)),
    exclusive: S3.Int.pipe(S3.greaterThan(-3), S3.lessThan(3)), fractional: S3.Int.pipe(S3.between(-2.5, 2.5)),
    empty: S3.Int.pipe(S3.greaterThan(3), S3.lessThan(4)), finite: S3.Literal(-2, 4),
    nullable: S3.NullOr(S3.Int.pipe(S3.between(5, 7))),
    struct: S3.Struct({n: S3.Int.pipe(S3.between(5, 7)), b: S3.Boolean, status: S3.Literal('open', 'closed')}),
    tagged: S3.Union(S3.TaggedStruct('Set', {n: S3.Int.pipe(S3.between(5, 7))}), S3.TaggedStruct('Clear', {})),
    optional: S3.Struct({x: S3.optional(S3.Boolean)}), undefined: S3.UndefinedOr(S3.Int),
    custom: S3.Int.pipe(S3.filter((n: number) => n !== 6)), regex: S3.String.pipe(S3.pattern(/^a/)),
    branded: S3.Int.pipe(S3.brand('SchemaCount')), transform: S3.NumberFromString, cls: C3,
    acceptsInt: S3.is(S3.Int), acceptsBounded: S3.is(S3.Int.pipe(S3.between(5, 7))),
    acceptsStruct: S3.is(S3.Struct({n: S3.Int.pipe(S3.between(5, 7)), b: S3.Boolean, status: S3.Literal('open', 'closed')})),
  },
] as const
const accepted = (kind: Kind<unknown>, raw: Raw) => { try { kind.encode('v', raw); return true } catch { return false } }
const roundTrip = (kind: Kind<unknown>, raw: Raw) => expect(kind.decode('v', kind.encode('v', raw))).toEqual(raw)
const samples = (kind: Kind<unknown>, accepts: (raw: unknown) => boolean) => {
  const rand = seeded(71)
  for (let i = 0; i < 100; i++) {
    const sample = kind.sample(rand, i % 10)
    expect(accepts(sample)).toBe(true)
    roundTrip(kind, sample)
    expect(accepts(kind.decode('v', kind.random('v', rand, i % 10)))).toBe(true)
    const encoded = kind.encode('v', sample), known = kind.build('v', name => new Term({op: 'const', value: encoded[name]!}, encoded[name]!))
    expect(kind.invariant(known).every(c => c.ok === true)).toBe(true)
    const stored = Object.fromEntries(Object.entries(kind.store('v', known)).map(([name, term]) => [name, typeof term === 'number' ? term : term.val!]))
    expect(kind.decode('v', stored)).toEqual(sample)
  }
}
for (const v of versions) {
  test(`Schema ${v.name}: safe integers, bounds, exclusivity, thresholds and literals`, () => {
    const k = fromSchema(v.integer)
    expect(k.value('n')).toBeInstanceOf(Int)
    for (const n of [Number.MIN_SAFE_INTEGER, Number.MIN_SAFE_INTEGER + 1, -(2 ** 52), -1, 0, 1, 2 ** 52, Number.MAX_SAFE_INTEGER - 1, Number.MAX_SAFE_INTEGER,
      -(2 ** 53), 2 ** 53, Infinity, -Infinity, NaN, 1.5, -1.5, '1', true, null, undefined] as Raw[]) {
      expect(accepted(k, n)).toBe(v.acceptsInt(n))
      if (v.acceptsInt(n)) roundTrip(k, n)
    }
    // -0 and 0 are one mathematical integer (the contract is not Object.is).
    expect(k.decode('n', k.encode('n', -0))).toBe(0)
    expect(k.report).toMatchObject({domain: 'decoded-closed-values', runtime: 'exact-on-decoded-closed-values', losses: []})
    samples(k, v.acceptsInt)
    const bounded = fromSchema(v.bounded)
    for (let n = 2; n <= 10; n++) expect(accepted(bounded, n)).toBe(v.acceptsBounded(n))
    samples(bounded, v.acceptsBounded)
    expect(bounded.empty()).toBe(5)
    for (const s of [v.exclusive, v.fractional]) for (let n = -4; n <= 4; n++) expect(accepted(fromSchema(s), n)).toBe(n >= -2 && n <= 2)
    for (const n of [-3, -2, 0, 3, 4, 5]) expect(accepted(fromSchema(v.finite), n)).toBe(n === -2 || n === 4)
    expect(() => fromSchema(v.empty)).toThrow(/empty/)
    expect(() => bounded.from(4)).toThrow()
    expect(() => bounded.store('n', 8)).toThrow()
    expect(() => bounded.decode('n', {n: 8, 'n$neg': 0})).toThrow()
    expect(() => k.decode('n', {n: 2 ** 53, 'n$neg': 0})).toThrow()
    roundTrip(fromSchema(v.branded), -1)
  })
  test(`Schema ${v.name}: structural and strict nullable codecs`, () => {
    const k = fromSchema(v.struct), raw = {n: 5, b: true, status: 'open'}
    roundTrip(k, raw)
    samples(k, v.acceptsStruct)
    for (const bad of [{...raw, n: 4}, {...raw, b: 1}, {...raw, status: 'other'}, {n: 5, b: false}]) expect(() => k.encode('v', bad)).toThrow()
    // Explicit closed-value qualification: Effect admits extras; this codec refuses instead of dropping them.
    expect(v.acceptsStruct({...raw, extra: 1})).toBe(true)
    expect(() => k.encode('v', {...raw, extra: 1})).toThrow(/undeclared/)
    const nullable = fromSchema(v.nullable)
    for (const value of [null, 5, 7]) roundTrip(nullable, value)
    expect(() => nullable.encode('n', undefined)).toThrow(/undefined is not null/)
    expect(() => nullable.store('n', undefined)).toThrow(/undefined is not null/)
    expect(() => nullable.encode('n', 4)).toThrow()
    expect(nullable.decode('n', nullable.random('n', () => 0, 1))).toBeNull()
    const literal = fromSchema(v.name === '4.0.7' ? S4.Literal(true) : S3.Literal(true))
    roundTrip(literal, true)
    expect(() => literal.encode('x', false)).toThrow()
    expect(() => literal.decode('x', {x: 2})).toThrow()
  })
  test(`Schema ${v.name}: state bounds are checked, never trusted`, () => {
    const k = fromSchema(v.bounded)
    const good = rule('schema bounded state').inputs({n: k}).state({x: k.from(5)}).step(({n}) => ({x: n}))
    expect(good.kindLaws().length).toBe(1)
    expect(proveRule(good, [good.law('at most seven', ({x}) => x.atMost(7))], {search: false})).toMatchObject({proven: true, checked: true})
    const bad = good.step(({x}) => ({x: x.plus(1)}))
    expect(proveRule(bad, [bad.law('trivial law cannot hide bad kind', () => yes)], {search: false}).proven).toBe(false)
    const inputs = rule('schema inputs and params').params({p: k}).inputs({n: k}).state({s: 0}).step(() => ({s: 0}))
    expect(proveSteps(inputs, [], [inputs.stepLaw('range assumptions', ({n, p}) => n.atMost(7).and(p.atLeast(5)))], {search: false})).toMatchObject({proven: true, checked: true})
    expect(() => inputs.encodeParams({p: 4})).toThrow()
    expect(() => inputs.encodeInput({n: 8}, {p: 5})).toThrow()
    const nullable = fromSchema(v.nullable)
    expect(proveRule(rule('nullable clear').state({x: nullable.from(5)}).step(() => ({x: null})), [], {search: false})).toMatchObject({proven: true, checked: true})
    const variant = fromSchema(v.tagged)
    const states = rule('schema tagged clear').inputs({cmd: variant}).state({x: variant.from({_tag: 'Set', n: 5})}).step(({cmd}) => ({x: cmd}))
    expect(proveRule(states, [], {search: false})).toMatchObject({proven: true, checked: true})
    roundTrip(variant, {_tag: 'Clear'})
    expect(() => variant.encode('x', {_tag: 'Set', n: 8})).toThrow()
    const brokenCase = states.step(() => ({x: variant.make({_tag: 'Set', n: Int.of(8)})}))
    expect(proveRule(brokenCase, [], {search: false}).proven).toBe(false)
    const record = fromSchema(v.struct)
    const brokenRecord = rule('schema broken record').state({x: record.from({n: 5, b: true, status: 'open'})}).step(({x}) => ({x: {...x, n: x.n.minus(1)}}))
    expect(proveRule(brokenRecord, [], {search: false}).proven).toBe(false)
  }, 60_000)
  test(`Schema ${v.name}: fail closed or report every approximation`, () => {
    for (const schema of [v.custom, v.regex]) {
      expect(() => fromSchema(schema)).toThrow(SchemaError)
      const k = fromSchema(schema, {mode: 'approximate'})
      expect(k.report).toMatchObject({runtime: 'overapproximation', model: 'overapproximation', counterexamples: 'validate-with-schema'})
      expect(k.report.losses[0]?.code).toBe('unsupported-refinement')
    }
    expect(() => fromSchema(v.optional)).toThrow(/optional/)
    expect(() => fromSchema(v.undefined)).toThrow(/undefined/)
    const optional = fromSchema(v.optional, {mode: 'approximate'})
    expect(optional.report.runtime).toBe('normalized')
    expect(optional.decode('s', optional.encode('s', {}))).toEqual({x: null})
    expect(optional.decode('s', optional.encode('s', {x: undefined}))).toEqual({x: null})
    expect(optional.report.losses.map(l => l.code)).toContain('optional-to-null')
    expect(optional.report.losses.map(l => l.code)).toContain('undefined-to-null')
    expect(() => fromSchema(v.transform, {mode: 'approximate'})).toThrow(/transform/)
    expect(() => fromSchema(v.cls)).toThrow(/Class/)
    const cls = fromSchema(v.cls, {mode: 'approximate'})
    expect(cls.report.runtime).toBe('projection')
    expect(cls.report.losses[0]?.code).toBe('class-fields')
    expect(cls.decode('c', cls.encode('c', {n: 2}))).toEqual({n: 2})
    expect(cls.decode('c', cls.encode('c', {n: 2}))).not.toBeInstanceOf(v.cls)
  })
}
test('exact branded strings, literals, nested fields and tagged payloads match symbolic types on both versions', () => {
  const fixtures = [
    {plain: S4.String.pipe(S4.brand('Name')), label: S4.Literal('ready').pipe(S4.brand('Ready')), nested: S4.Struct({plain: S4.String.pipe(S4.brand('Name')), label: S4.Literal('ready').pipe(S4.brand('Ready'))}), tagged: S4.Union([S4.TaggedStruct('Set', {name: S4.String.pipe(S4.brand('Name'))}), S4.TaggedStruct('Clear', {})])},
    {plain: S3.String.pipe(S3.brand('Name')), label: S3.Literal('ready').pipe(S3.brand('Ready')), nested: S3.Struct({plain: S3.String.pipe(S3.brand('Name')), label: S3.Literal('ready').pipe(S3.brand('Ready'))}), tagged: S3.Union(S3.TaggedStruct('Set', {name: S3.String.pipe(S3.brand('Name'))}), S3.TaggedStruct('Clear', {}))},
  ]
  for (const f of fixtures) {
    const plain = fromSchema(f.plain), label = fromSchema(f.label), nested = fromSchema(f.nested), tagged = fromSchema(f.tagged)
    expect(plain.value('p')).toBeInstanceOf(Str)
    expect(label.value('p')).toBeInstanceOf(Choice)
    expect(nested.value('p').plain).toBeInstanceOf(Str)
    expect(nested.value('p').label).toBeInstanceOf(Choice)
    expect(tagged.value('t').match({Set: ({name}) => name.length, Clear: () => 0})).toBeInstanceOf(Term)
    roundTrip(plain, 'someone')
    roundTrip(label, 'ready')
    roundTrip(nested, {plain:'someone', label:'ready'})
    roundTrip(tagged, {_tag:'Set', name:'someone'})
    expect(label.report.runtime).toBe('exact-on-decoded-closed-values')
    expect(plain.report.model).toBe('overapproximation')
  }
})

test('identity integer codecs agree with Effect decoding and encoding', () => {
  for (const c of [{k: fromSchema(S4.Int), decode: S4.decodeUnknownSync(S4.Int), encode: S4.encodeSync(S4.Int)}, {k: fromSchema(S3.Int), decode: S3.decodeUnknownSync(S3.Int), encode: S3.encodeSync(S3.Int)}]) {
    for (const raw of [Number.MIN_SAFE_INTEGER, -1, 0, 1, Number.MAX_SAFE_INTEGER]) {
      expect(c.k.decode('x', c.k.encode('x', c.decode(raw)))).toBe(c.encode(raw))
    }
  }
})

test('approximation needs an exact explicit opt-in and report arrays cannot mutate the domain', () => {
  expect(() => fromSchema(S4.Int, {mode: 'excat'} as never)).toThrow(/invalid mode/)
  const k = fromSchema(S4.Literals([2, 4]))
  const values = k.report.constraints[0]!.values!
  expect(Object.isFrozen(values)).toBe(true)
  expect(() => (values as number[]).push(3)).toThrow()
  expect(accepted(k, 3)).toBe(false)
})

test('custom predicates are not executed; paths retained; transforms and collections refused', () => {
  let calls = 0
  for (const schema of [S4.Struct({x: S4.Int.check(S4.makeFilter(() => { calls++; return false }))}), S3.Struct({x: S3.Int.pipe(S3.filter(() => { calls++; return false }))})]) {
    expect(() => fromSchema(schema)).toThrow(/custom predicate/)
    expect(fromSchema(schema, {mode: 'approximate'}).report.losses[0]?.path).toBe('x')
  }
  expect(calls).toBe(0)
  const async = S3.transformOrFail(S3.String, S3.Int, {strict: true, decode: () => E3.as(E3.sleep('1 millis'), 1), encode: () => E3.succeed('1')})
  for (const schema of [async, S3.Array(S3.Int), S4.Array(S4.Int), S3.Record({key: S3.String, value: S3.Int}), S4.Record(S4.String, S4.Int), S3.Union(S3.Int, S3.Boolean), S4.Union([S4.Int, S4.Boolean])]) expect(() => fromSchema(schema, {mode: 'approximate'})).toThrow(SchemaError)
  const strings = fromSchema(S4.String), raw = strings.encode('x', 'abc')
  expect(strings.report).toMatchObject({runtime: 'exact-on-decoded-closed-values', model: 'overapproximation'})
  expect(() => strings.decode('x', {...raw, 'x$len': 4})).toThrow(/disagree/)
})
test('single tagged structs and singleton unions stay records; tagged codecs enforce all own keys', () => {
  const singles = [S4.TaggedStruct('Set', {n: S4.Int}), S3.TaggedStruct('Set', {n: S3.Int}), S4.Union([S4.TaggedStruct('Set', {n: S4.Int})]), S3.Union(S3.TaggedStruct('Set', {n: S3.Int}))]
  for (const schema of singles) {
    const k = fromSchema(schema), value = k.value('v')
    expect(value.n).toBeInstanceOf(Int)
    expect(value._tag.is('Set')).toBeInstanceOf(Object)
    expect('match' in value).toBe(false)
    roundTrip(k, {_tag: 'Set', n: 3})
  }
  for (const v of versions) {
    const k = fromSchema(v.tagged)
    for (const raw of [{_tag: 'Clear', extra: 1}, {_tag: 'Set', n: 5, extra: 1}, {_tag: 'Set'}, {n: 5}, {_tag: 'Clear', [Symbol('extra')]: 1}]) {
      expect(() => k.encode('v', raw)).toThrow()
      expect(() => k.store('v', raw)).toThrow()
      expect(() => rule('invalid callback init').state({v: k.from(() => raw)}).machine).toThrow()
    }
  }
  const badTags = [S4.Union([S4.Struct({_tag: S4.optional(S4.Literal('Set')), n: S4.Int}), S4.TaggedStruct('Clear', {})]), S3.Union(S3.Struct({_tag: S3.optional(S3.Literal('Set')), n: S3.Int}), S3.TaggedStruct('Clear', {}))]
  for (const schema of badTags) expect(() => fromSchema(schema)).toThrow(/required literal _tag/)
  // Both property context shapes, not just the one emitted by the current version.
  for (const flag of [{isOptional: true}, {context: {isOptional: true}}]) {
    const tagged = (name: string, extra = {}) => ({_tag: 'Objects', propertySignatures: [{name: '_tag', type: {_tag: 'Literal', literal: name}, ...extra}], indexSignatures: []})
    expect(() => fromSchema({ast: {_tag: 'Union', types: [tagged('Set', flag), tagged('Clear')]}})).toThrow(/required literal _tag/)
  }
})

test('signed migration rejects the old nat handler and proves the explicit signed one', () => {
  const k = fromSchema(S4.Int.check(S4.isGreaterThanOrEqualTo(0)))
  expect(() => new Term({op: 'const', value: 0}).plus(k.value('n') as never)).toThrow(/a natural is expected/)
  const r = rule('signed schema migration').inputs({n: k}).state({total: int.from(0)}).step(({n, total}) => ({total: total.plus(n).min(100)}))
  expect(proveRule(r, [r.law('nonnegative capped', ({total}) => total.atLeast(0).and(total.atMost(100)))], {search: false})).toMatchObject({proven: true, checked: true})
})
