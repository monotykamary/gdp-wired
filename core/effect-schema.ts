// Effect Schema's decoded-value domain as an ordinary Kind. No Effect import (including type imports): the
// optional frontend reads the 3.22.x / 4.0.x AST, never runs a predicate, decoder, encoder, or transformation.
import {Bool, Choice, Cond, Int, Kind, Maybe, Str, Term, any, bool, int, lit, oneOf, str, variant, type Init, type Raw, type RawObject, type TermLike, Variant} from './dsl.ts'
import type {Rand} from './machine.ts'

export type SchemaLike = {readonly ast: unknown}
// Encoded is used only to select representation, not to execute/prove a codec. Transforms are refused;
// unlike Type, this shape does not mistake a nominal string brand for a literal choice.
type Shape<S> = S extends {readonly Encoded: infer A} ? A : unknown
// Class methods/prototype are NOT fields. Erased schemas never promise an inferred value.
type Projected<S> = unknown extends Shape<S> ? unknown : S extends {readonly fields: infer F} ? Pick<Shape<S>, Extract<keyof F, keyof Shape<S>>> : Shape<S>
type IsUnion<A, Whole = A> = A extends Whole ? [Whole] extends [A] ? false : true : never
type CasesOf<A extends {readonly _tag: string}> = {[K in A['_tag']]: {[F in Exclude<Extract<keyof Extract<A, {readonly _tag: K}>, string>, '_tag'>]-?: Kind<SchemaValue<Extract<A, {readonly _tag: K}>[F]>>}}
/** Symbolic values, never Schema.Type cast as a Kind: numbers are signed Int, booleans Bool, strings Str/Choice. */
export type SchemaValue<A> = 0 extends 1 & A ? unknown : unknown extends A ? unknown
  : undefined extends A ? Maybe<SchemaValue<NonNullable<A>>>
  : null extends A ? Maybe<SchemaValue<NonNullable<A>>>
  : [A] extends [number] ? Int : [A] extends [boolean] ? Bool
  : [A] extends [string] ? string extends A ? Str : Choice<A & string>
  : [A] extends [{readonly _tag: string}] ? IsUnion<A> extends true ? Variant<CasesOf<A & {readonly _tag: string}>, '_tag'> : {[K in keyof A]-?: SchemaValue<A[K]>}
  : [A] extends [readonly unknown[]] ? never
  : [A] extends [object] ? {[K in keyof A]-?: SchemaValue<A[K]>} : never
export type SchemaSymbolic<S> = SchemaValue<Projected<S>>
export type SchemaOptions = {readonly mode?: 'exact' | 'approximate'}
export type SchemaDiagnostic = {readonly path: string, readonly code: string, readonly message: string, readonly effect: 'overapproximation' | 'normalization' | 'projection'}
export type SchemaConstraint = {readonly path: string, readonly kind: 'integer' | 'literals', readonly minimum?: number, readonly maximum?: number, readonly values?: readonly (string | number | boolean)[]}
export type SchemaReport = {
  readonly mode: 'exact' | 'approximate'
  /** Equality is on safe integers (including -0 as 0), booleans, strings, null, and closed structural records. */
  readonly domain: 'decoded-closed-values'
  readonly runtime: 'exact-on-decoded-closed-values' | 'overapproximation' | 'normalized' | 'projection'
  readonly model: 'exact' | 'overapproximation'
  readonly counterexamples: 'validate-with-schema'
  readonly losses: readonly SchemaDiagnostic[]
  readonly constraints: readonly SchemaConstraint[]
}
export class SchemaError extends Error {
  constructor(readonly path: string, readonly code: string, message: string) {
    super(`fromSchema: ${path || 'the schema'} is ${message}`)
    this.name = 'SchemaError'
  }
}

/** A regular Kind, with a report that distinguishes runtime conversion from symbolic model precision. */
export class SchemaKind<V> extends Kind<V> {
  constructor(private readonly inner: Kind<V>, readonly report: SchemaReport) { super() }
  vars(name: string) { return this.inner.vars(name) }
  assume(name: string) { return this.inner.assume(name) }
  build(name: string, get: (part: string) => Term) { return this.inner.build(name, get) }
  override invariant(value: V) { return this.inner.invariant(value) }
  encode(name: string, raw: Raw) { return this.inner.encode(name, raw) }
  decode(name: string, vars: Record<string, number>) { return this.inner.decode(name, vars) }
  store(name: string, value: unknown) { return this.inner.store(name, value) }
  empty() { return this.inner.empty() }
  random(name: string, rand: Rand, bound: number) { return this.inner.random(name, rand, bound) }
  override sample(rand: Rand, bound: number) { return this.inner.sample(rand, bound) }
  // Unlike Kind.from's historical callback, no implicit any is handed to a schema callback. Annotate params.
  override from(init: Raw | ((params: never) => unknown)): Init<V> {
    if (typeof init !== 'function') this.encode('initial', init)
    return {kind: this, init}
  }
  /** Build a symbolic value through the same checked store path used by state initialization. */
  make(value: unknown): V {
    const parts = this.store('$schema', value)
    return this.build('$schema', part => { const t = parts[part]!; return typeof t === 'number' ? lit(t) : t })
  }
}

const fail = (path: string, code: string, message: string): never => { throw new SchemaError(path, code, message) }
const badValue = (name: string, message: string): never => { throw new RangeError(`${name}: ${message}`) }
const own = (o: object, key: PropertyKey) => Object.prototype.hasOwnProperty.call(o, key)
const object = (x: unknown): Record<string, unknown> => x !== null && typeof x === 'object' ? x as Record<string, unknown> : {}
const node = (x: unknown, path: string): Ast => typeof object(x)._tag === 'string' ? x as Ast : fail(path, 'invalid-ast', 'not a supported Effect AST')
type Ast = Record<string, unknown> & {_tag: string}
const tags: Record<string, string> = {NumberKeyword: 'Number', BooleanKeyword: 'Boolean', StringKeyword: 'String', TypeLiteral: 'Objects', UndefinedKeyword: 'Undefined'}
const tag = (a: Ast) => tags[a._tag] ?? a._tag
const at = (path: string, field: string) => path ? `${path}.${field}` : field
const symAnnotation = (a: Ast, id: string): unknown => {
  const annotations = object(a.annotations), key = Object.getOwnPropertySymbols(annotations).find(k => k.description === `effect/annotation/${id}`)
  return key === undefined ? undefined : annotations[key as unknown as string]
}
const plainName = (name: string, path: string) => {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name) || name in Object.prototype || name === 'prototype') fail(path, 'field-name', 'a field/case name outside the plain, non-reserved identifier subset')
}

// The range is part of both input assumptions AND the state invariant. A transition is never trusted to keep it.
class IntegerKind extends Kind<Int> {
  constructor(readonly minimum: number, readonly maximum: number, readonly values?: readonly number[]) { super() }
  vars(name: string) { return int.vars(name) }
  build(name: string, get: (part: string) => Term) { return int.build(name, get) }
  override invariant(x: Int) { return [x.atLeast(this.minimum), x.atMost(this.maximum), ...(this.values ? [any(...this.values.map(n => x.eq(n)))] : [])] }
  assume(name: string) { return this.invariant(this.value(name)) }
  private check(name: string, raw: unknown): number {
    if (typeof raw !== 'number' || !Number.isSafeInteger(raw) || raw < this.minimum || raw > this.maximum || (this.values && !this.values.includes(raw))) badValue(name, 'outside the schema integer domain')
    return raw as number
  }
  encode(name: string, raw: Raw) { return int.encode(name, this.check(name, raw)) }
  store(name: string, value: unknown) {
    if (!(value instanceof Int) && !(value instanceof Term)) this.check(name, value)
    return int.store(name, value)
  }
  decode(name: string, vars: Record<string, number>) {
    for (const part of this.vars(name)) if (!Number.isSafeInteger(vars[part]) || vars[part]! < 0) badValue(name, 'invalid natural part of an integer')
    return this.check(name, int.decode(name, vars))
  }
  empty() { return this.values?.[0] ?? Math.min(this.maximum, Math.max(this.minimum, 0)) }
  override sample(rand: Rand, bound: number) {
    if (this.values) return this.values[rand(this.values.length)]!
    const near = this.empty(), span = Math.max(0, Math.min(1_000_000, Math.floor(bound)))
    const lo = Math.max(this.minimum, near - span), hi = Math.min(this.maximum, near + span)
    const edges = [this.minimum, this.maximum, near]
    return rand(4) === 0 ? edges[rand(edges.length)]! : lo + rand(hi - lo + 1)
  }
  random(name: string, rand: Rand, bound: number) { return this.encode(name, this.sample(rand, bound)) }
}
class BooleanKind extends Kind<Bool> {
  constructor(readonly literal?: boolean) { super() }
  vars(name: string) { return bool.vars(name) }
  build(name: string, get: (part: string) => Term) { return bool.build(name, get) }
  override invariant(b: Bool) { return [...bool.invariant(b), ...(this.literal === undefined ? [] : [b.n.eq(Number(this.literal))])] }
  assume(name: string) { return this.invariant(this.value(name)) }
  encode(name: string, raw: Raw) {
    if (typeof raw !== 'boolean' || (this.literal !== undefined && raw !== this.literal)) badValue(name, 'outside the schema boolean domain')
    return bool.encode(name, raw)
  }
  store(name: string, value: unknown) { return value instanceof Cond ? bool.store(name, value) : this.encode(name, value as Raw) }
  decode(name: string, vars: Record<string, number>) {
    if (vars[name] !== 0 && vars[name] !== 1) badValue(name, 'invalid boolean encoding')
    const raw = vars[name] === 1
    this.encode(name, raw)
    return raw
  }
  empty() { return this.literal ?? false }
  override sample(rand: Rand) { return this.literal ?? rand(2) === 1 }
  random(name: string, rand: Rand) { return this.encode(name, this.sample(rand)) }
}
class ChoiceKind extends Kind<Choice<string>> {
  private readonly inner: Kind<Choice<string>>
  constructor(readonly values: string[]) { super(); this.inner = oneOf(...values) }
  vars(name: string) { return this.inner.vars(name) }
  build(name: string, get: (part: string) => Term) { return this.inner.build(name, get) }
  override invariant(x: Choice<string>) { return this.inner.invariant(x) }
  assume(name: string) { return this.inner.assume(name) }
  encode(name: string, raw: Raw) { return this.inner.encode(name, raw) }
  store(name: string, value: unknown) {
    if (value instanceof Choice && (value.values.length !== this.values.length || value.values.some((v, i) => v !== this.values[i]))) badValue(name, 'a choice from another schema')
    return this.inner.store(name, value)
  }
  decode(name: string, vars: Record<string, number>) {
    if (!Number.isInteger(vars[name]) || vars[name]! < 0 || vars[name]! >= this.values.length) badValue(name, 'invalid choice encoding')
    return this.inner.decode(name, vars)
  }
  empty() { return this.inner.empty() }
  override sample(rand: Rand, bound: number) { return this.inner.sample(rand, bound) }
  random(name: string, rand: Rand, bound: number) { return this.inner.random(name, rand, bound) }
}
class StringKind extends Kind<Str> {
  private readonly inner = str()
  vars(name: string) { return this.inner.vars(name) }
  assume(name: string) { return this.inner.assume(name) }
  build(name: string, get: (part: string) => Term) { return this.inner.build(name, get) }
  override invariant(s: Str) { return [s.id.eq(0).iff(s.length.eq(0))] }
  encode(name: string, raw: Raw) { return this.inner.encode(name, raw) }
  store(name: string, value: unknown) {
    if (typeof value !== 'string' && !(value instanceof Str)) badValue(name, 'a schema string is expected')
    return this.inner.store(name, value)
  }
  decode(name: string, vars: Record<string, number>) {
    const text = this.inner.decode(name, vars)
    if (typeof text !== 'string') return badValue(name, 'invalid string encoding')
    if (vars[`${name}$len`] !== text.length) badValue(name, 'string id and length disagree (validate symbolic counterexamples)')
    return text
  }
  empty() { return '' }
  override sample(rand: Rand, bound: number) { return this.inner.sample(rand, bound) }
  random(name: string, rand: Rand, bound: number) { return this.inner.random(name, rand, bound) }
}
class NullableKind extends Kind<Maybe<unknown>> {
  constructor(readonly inner: Kind<unknown>, readonly normalizeUndefined = false) { super() }
  private has(name: string) { return `${name}$some` }
  vars(name: string) { return [this.has(name), ...this.inner.vars(name)] }
  build(name: string, get: (part: string) => Term) { return new Maybe(get(this.has(name)), this.inner.build(name, get)) }
  override invariant(m: Maybe<unknown>) { return [m.present.atMost(1), ...this.inner.invariant(m.inner).map(c => m.isSome.implies(c))] }
  assume(name: string) { const m = this.value(name); return [m.present.atMost(1), ...this.inner.assume(name).map(c => m.isSome.implies(c))] }
  encode(name: string, raw: Raw) {
    if (raw === undefined && !this.normalizeUndefined) badValue(name, 'undefined is not null')
    return raw === null || raw === undefined ? {[this.has(name)]: 0, ...this.inner.encode(name, this.inner.empty())} : {[this.has(name)]: 1, ...this.inner.encode(name, raw)}
  }
  store(name: string, value: unknown) {
    if (value instanceof Maybe) return {[this.has(name)]: value.present, ...this.inner.store(name, value.inner)}
    if (value === null || value === undefined) return this.encode(name, value)
    return {[this.has(name)]: 1, ...this.inner.store(name, value)}
  }
  decode(name: string, vars: Record<string, number>) {
    if (vars[this.has(name)] !== 0 && vars[this.has(name)] !== 1) badValue(name, 'invalid presence bit')
    return vars[this.has(name)] === 0 ? null : this.inner.decode(name, vars)
  }
  empty() { return null }
  override sample(rand: Rand, bound: number) { return rand(4) === 0 ? null : this.inner.sample(rand, bound) }
  random(name: string, rand: Rand, bound: number) { return this.encode(name, this.sample(rand, bound)) }
}

type Fields = Record<string, Kind<unknown>>
class StructKind extends Kind<Record<string, unknown>> {
  constructor(readonly fields: Fields, readonly optional: ReadonlySet<string> = new Set()) { super() }
  private each<T>(name: string, f: (kind: Kind<unknown>, path: string, key: string) => T) { return Object.entries(this.fields).map(([key, k]) => f(k, at(name, key), key)) }
  vars(name: string) { return this.each(name, (k, p) => k.vars(p)).flat() }
  assume(name: string) { return this.each(name, (k, p) => k.assume(p)).flat() }
  build(name: string, get: (part: string) => Term) { return Object.fromEntries(this.each(name, (k, p, key) => [key, k.build(p, get)])) }
  override invariant(value: Record<string, unknown>) { return this.each('', (k, _, key) => k.invariant(value[key])).flat() }
  private check(name: string, value: unknown): Record<string, unknown> {
    if (value === null || typeof value !== 'object' || Array.isArray(value)) return badValue(name, 'a closed structural object is expected')
    const o = value as Record<string, unknown>
    for (const key of Reflect.ownKeys(o)) if (typeof key !== 'string' || !own(this.fields, key)) badValue(name, 'an object has an undeclared field')
    for (const key of Object.keys(this.fields)) if (!own(o, key) && !this.optional.has(key)) badValue(at(name, key), 'a required field is absent')
    return o
  }
  encode(name: string, raw: Raw) { const o = this.check(name, raw); return Object.assign({}, ...this.each(name, (k, p, key) => k.encode(p, o[key] as Raw))) as Record<string, number> }
  store(name: string, value: unknown) { const o = this.check(name, value); return Object.assign({}, ...this.each(name, (k, p, key) => k.store(p, o[key]))) as Record<string, TermLike> }
  decode(name: string, vars: Record<string, number>) { return Object.fromEntries(this.each(name, (k, p, key) => [key, k.decode(p, vars)])) as RawObject }
  empty() { return Object.fromEntries(this.each('', (k, _, key) => [key, k.empty()])) as RawObject }
  override sample(rand: Rand, bound: number) { return Object.fromEntries(this.each('', (k, _, key) => [key, k.sample(rand, bound)])) as RawObject }
  random(name: string, rand: Rand, bound: number) { return this.encode(name, this.sample(rand, bound)) }
}
class TaggedKind extends Kind<Variant<Record<string, Fields>, '_tag'>> {
  private readonly inner
  private readonly names: string[]
  constructor(readonly cases: Record<string, Fields>) { super(); this.inner = variant(cases, {tag: '_tag'}); this.names = Object.keys(cases) }
  vars(name: string) { return this.inner.vars(name) }
  build(name: string, get: (part: string) => Term) { return this.inner.build(name, get) }
  assume(name: string) { const x = this.value(name); return [x.tag.lt(this.names.length), ...this.names.flatMap(k => new StructKind(this.cases[k]!).assume(at(name, k)).map(c => x.is(k).implies(c)))] }
  override invariant(x: Variant<Record<string, Fields>, '_tag'>) { return [x.tag.lt(this.names.length), ...this.names.flatMap(k => new StructKind(this.cases[k]!).invariant(x.cases[k]!).map(c => x.is(k).implies(c)))] }
  private raw(name: string, value: unknown) {
    if (value === null || typeof value !== 'object' || Array.isArray(value)) return badValue(name, 'a closed tagged object is expected')
    const o = value as Record<string, unknown>, tag = own(o, '_tag') ? o._tag : undefined
    if (typeof tag !== 'string' || !own(this.cases, tag)) return badValue(name, 'a required known _tag is expected')
    const fields = this.cases[tag]!
    for (const key of Reflect.ownKeys(o)) if (typeof key !== 'string' || (key !== '_tag' && !own(fields, key))) badValue(name, 'a tagged object has an undeclared field')
    for (const key of Object.keys(fields)) if (!own(o, key)) badValue(at(name, key), 'a required field is absent')
  }
  encode(name: string, raw: Raw) { this.raw(name, raw); return this.inner.encode(name, raw) }
  store(name: string, value: unknown) {
    if (!(value instanceof Variant)) this.raw(name, value)
    return this.inner.store(name, value)
  }
  decode(name: string, vars: Record<string, number>) {
    if (!Number.isInteger(vars[name]) || !this.names[vars[name]!]) badValue(name, 'invalid schema tag')
    return this.inner.decode(name, vars)
  }
  empty() { return this.inner.empty() }
  override sample(rand: Rand, bound: number) { return this.inner.sample(rand, bound) }
  random(name: string, rand: Rand, bound: number) { return this.encode(name, this.sample(rand, bound)) }
}

type Filter = {id: string, payload: Record<string, unknown>}
/** Exact by default. Approximation is opt-in and every discarded constraint/normalization has a path in report.losses. */
export function fromSchema<const S extends SchemaLike>(schema: S, options?: {readonly mode?: 'exact'}): SchemaKind<SchemaSymbolic<S>>
export function fromSchema(schema: SchemaLike, options: SchemaOptions | undefined): SchemaKind<unknown>
export function fromSchema(schema: SchemaLike, options: SchemaOptions = {}): SchemaKind<unknown> {
  const mode = options.mode ?? 'exact', losses: SchemaDiagnostic[] = [], constraints: SchemaConstraint[] = []
  if (mode !== 'exact' && mode !== 'approximate') fail('', 'invalid-mode', 'given an invalid mode (expected exact or approximate)')
  let abstractStrings = false
  const lose = (path: string, code: string, message: string, effect: SchemaDiagnostic['effect'] = 'overapproximation') => {
    if (mode === 'exact') fail(path, code, message)
    losses.push({path, code, message, effect})
  }
  const transformed = (a: Ast) => a._tag === 'Transformation' || (Array.isArray(a.encoding) && a.encoding.length > 0)
  const filtersOf = (a: Ast, path: string): {base: Ast, filters: Filter[]} => {
    if (transformed(a)) fail(path, 'transformation', 'a transform/encoding (only decoded domains without transforms are read)')
    const filters: Filter[] = []
    while (a._tag === 'Refinement') {
      const id = symAnnotation(a, 'SchemaId')
      filters.push({id: typeof id === 'symbol' ? id.description ?? '' : '', payload: object(symAnnotation(a, 'JSONSchema'))})
      a = node(a.from, path)
      if (transformed(a)) fail(path, 'transformation', 'a transform under a refinement')
    }
    if (Array.isArray(a.checks)) for (const x of a.checks) {
      const c = object(x), r = object(object(c.annotations).representation)
      filters.push({id: c._tag === 'Filter' && typeof r.id === 'string' ? r.id : '', payload: object(r.payload)})
    }
    return {base: a, filters}
  }
  const integers = (fs: Filter[], path: string, literals?: number[]): Kind<Int> => {
    let integral = !!literals, minimum = Number.MIN_SAFE_INTEGER, maximum = Number.MAX_SAFE_INTEGER
    const bound = (payload: Record<string, unknown>, key: string): number => typeof payload[key] === 'number' && Number.isFinite(payload[key]) ? payload[key] as number : fail(path, 'invalid-bound', 'an unrecognized or non-finite integer bound')
    for (const f of fs) {
      switch (f.id) {
        case 'effect/SchemaId/Int': case 'effect/schema/isInt': integral = true; break
        case 'effect/SchemaId/GreaterThan': case 'effect/schema/isGreaterThan': minimum = Math.max(minimum, Math.floor(bound(f.payload, 'exclusiveMinimum')) + 1); break
        case 'effect/SchemaId/GreaterThanOrEqualTo': case 'effect/schema/isGreaterThanOrEqualTo': minimum = Math.max(minimum, Math.ceil(bound(f.payload, 'minimum'))); break
        case 'effect/SchemaId/LessThan': case 'effect/schema/isLessThan': maximum = Math.min(maximum, Math.ceil(bound(f.payload, 'exclusiveMaximum')) - 1); break
        case 'effect/SchemaId/LessThanOrEqualTo': case 'effect/schema/isLessThanOrEqualTo': maximum = Math.min(maximum, Math.floor(bound(f.payload, 'maximum'))); break
        case 'effect/SchemaId/Between': case 'effect/schema/isBetween': minimum = Math.max(minimum, Math.ceil(bound(f.payload, 'minimum'))); maximum = Math.min(maximum, Math.floor(bound(f.payload, 'maximum'))); break
        case 'effect/SchemaId/Finite': case 'effect/schema/isFinite': case 'effect/SchemaId/NonNaN': break // implied by safe integer, checked below
        default: lose(path, 'unsupported-refinement', `an unsupported numeric refinement (${f.id || 'custom predicate'}); no predicate is executed`)
      }
    }
    if (!integral) fail(path, 'fractional-number', 'a number that may be fractional (use Schema.Int)')
    if (minimum > maximum || (literals && (!literals.length || literals.some(n => !Number.isSafeInteger(n))))) fail(path, 'empty-integer-domain', 'an empty or non-safe integer domain')
    const values = literals?.filter(n => n >= minimum && n <= maximum)
    if (values?.length === 0) fail(path, 'empty-integer-domain', 'an empty integer domain')
    constraints.push({path, kind: 'integer', minimum, maximum, ...(values ? {values} : {})})
    return new IntegerKind(minimum, maximum, values)
  }
  const fieldsOf = (a: Ast, path: string, tagged = false): {fields: Fields, optional: Set<string>} => {
    if (!Array.isArray(a.propertySignatures) || (Array.isArray(a.indexSignatures) && a.indexSignatures.length)) fail(path, 'index-signature', 'an object with an index signature or unknown fields')
    const fields: Fields = {}, optional = new Set<string>()
    for (const raw of a.propertySignatures as unknown[]) {
      const p = object(raw), name = p.name
      if (typeof name !== 'string') fail(path, 'field-name', 'a symbol/numeric property (plain named fields are read)')
      plainName(name as string, path)
      if (tagged && name === '_tag') continue
      const field = name as string, location = at(path, field), child = node(p.type, location)
      const absent = p.isOptional === true || object(p.context).isOptional === true || object(child.context).isOptional === true
      if (absent) { lose(location, 'optional-to-null', 'an optional property; missing and undefined would normalize to null', 'normalization'); optional.add(field) }
      let k = go(child, location)
      if (absent && !(k instanceof NullableKind)) k = new NullableKind(k, true)
      if (absent && k instanceof NullableKind && !k.normalizeUndefined) k = new NullableKind(k.inner, true)
      if (own(fields, field)) fail(location, 'duplicate-field', 'a duplicate field')
      fields[field] = k
    }
    return {fields, optional}
  }
  const go = (source: Ast, path: string): Kind<unknown> => {
    const {base: a, filters} = filtersOf(source, path), t = tag(a)
    if (t === 'Number') return integers(filters, path)
    if (t === 'Literal' && typeof a.literal === 'number') return integers(filters, path, [a.literal])
    for (const f of filters) lose(path, 'unsupported-refinement', `an unsupported ${t} refinement (${f.id || 'custom predicate'}); no predicate is executed`)
    if (t === 'Boolean') return new BooleanKind()
    if (t === 'String') { abstractStrings = true; return new StringKind() }
    if (t === 'Literal') {
      if (typeof a.literal === 'string') { constraints.push({path, kind: 'literals', values: [a.literal]}); return new ChoiceKind([a.literal]) }
      if (typeof a.literal === 'boolean') return new BooleanKind(a.literal)
    }
    if (t === 'Objects') { const {fields, optional} = fieldsOf(a, path); return new StructKind(fields, optional) }
    if (t !== 'Union') return fail(path, 'unsupported-schema', `a ${a._tag} schema (arrays, dynamic collections, standalone null/undefined and declarations are not ordinary Kinds)`)
    if (!Array.isArray(a.types) || !a.types.length) return fail(path, 'empty-union', 'an empty union')
    const types = a.types.map(x => node(x, path))
    if (types.length === 1) return go(types[0]!, path)
    for (const member of types) {
      const inspected = filtersOf(member, path)
      if (['Literal', 'Null', 'Undefined'].includes(tag(inspected.base))) for (const f of inspected.filters) lose(path, 'unsupported-refinement', `a refined union alternative (${f.id || 'custom predicate'})`)
    }
    const missing = types.filter(x => tag(x) === 'Null' || tag(x) === 'Undefined' || (x._tag === 'Literal' && x.literal === null))
    const rest = types.filter(x => !missing.includes(x))
    if (missing.length) {
      const hasUndefined = missing.some(x => tag(x) === 'Undefined')
      if (hasUndefined) lose(path, 'undefined-to-null', 'a union with undefined; undefined would normalize to null', 'normalization')
      if (rest.length !== 1) fail(path, 'unsupported-union', 'a nullable union without exactly one value domain')
      const inner = go(rest[0]!, path)
      return inner instanceof NullableKind ? new NullableKind(inner.inner, hasUndefined || inner.normalizeUndefined) : new NullableKind(inner, hasUndefined)
    }
    if (types.every(x => x._tag === 'Literal' && typeof x.literal === 'string')) { const values = [...new Set(types.map(x => x.literal as string))]; constraints.push({path, kind: 'literals', values}); return new ChoiceKind(values) }
    if (types.every(x => x._tag === 'Literal' && typeof x.literal === 'number')) return integers([], path, [...new Set(types.map(x => x.literal as number))])
    if (types.every(x => x._tag === 'Literal' && typeof x.literal === 'boolean')) return new BooleanKind(types.every(x => x.literal === types[0]!.literal) ? types[0]!.literal as boolean : undefined)
    const cases: Record<string, Fields> = {}
    for (const x of types) {
      // Do not discard checks/transformations attached to a union member while reading its fields.
      const member = filtersOf(x, path)
      if (tag(member.base) !== 'Objects') fail(path, 'unsupported-union', 'a union other than literals, NullOr, or distinct _tag structs')
      for (const f of member.filters) lose(path, 'unsupported-refinement', `a refined union member (${f.id || 'custom predicate'})`)
      const props = member.base.propertySignatures
      if (!Array.isArray(props)) fail(path, 'unsupported-union', 'a tagged member without declared fields')
      const p = (props as unknown[]).map(object).find(p => p.name === '_tag'), litTag = p && node(p.type, path)
      if (!litTag || litTag._tag !== 'Literal' || typeof litTag.literal !== 'string' || p?.isOptional || object(p?.context).isOptional || object(litTag.context).isOptional) return fail(path, 'unsupported-union', 'a member without a required literal _tag')
      const name = litTag.literal as string
      plainName(name, path)
      if (own(cases, name)) fail(path, 'duplicate-tag', 'a union with duplicate _tag values')
      // Tag predicates are not field metadata.
      go(litTag, at(path, '_tag'))
      const fields = fieldsOf(member.base, at(path, name), true)
      if (fields.optional.size) fail(path, 'optional-variant', 'an optional field in a variant (normalization is supported only for records)')
      cases[name] = fields.fields
    }
    return new TaggedKind(cases)
  }
  let ast = node(schema.ast, '')
  const fields = (schema as SchemaLike & {readonly fields?: Record<string, SchemaLike>}).fields
  if (fields && tag(ast) !== 'Objects') {
    lose('', 'class-fields', 'a Schema.Class/declaration: only declared fields, not instances, methods or prototype, are projected', 'projection')
    // A class can carry additional predicates; projection does not silently discard those either.
    let outer = ast
    while (outer._tag === 'Refinement') { lose('', 'unsupported-refinement', 'an additional class refinement is not modeled'); outer = node(outer.from, '') }
    if (Array.isArray(outer.checks)) for (const _check of outer.checks) lose('', 'unsupported-refinement', 'an additional class check is not modeled')
    ast = {_tag: 'Objects', propertySignatures: Object.entries(fields).map(([name, f]) => ({name, type: f.ast})), indexSignatures: []}
  }
  const inner = go(ast, '')
  const runtime = losses.some(l => l.effect === 'projection') ? 'projection' : losses.some(l => l.effect === 'normalization') ? 'normalized' : losses.length ? 'overapproximation' : 'exact-on-decoded-closed-values'
  const report: SchemaReport = Object.freeze({mode, domain: 'decoded-closed-values', runtime, model: abstractStrings || losses.length ? 'overapproximation' : 'exact', counterexamples: 'validate-with-schema', losses: Object.freeze(losses.map(l => Object.freeze(l))), constraints: Object.freeze(constraints.map(c => Object.freeze({...c, ...(c.values ? {values: Object.freeze([...c.values])} : {})})))})
  // The exact overload follows the supported structural shape. Approximation never promises a narrowed Type.
  return new SchemaKind(inner, report)
}
