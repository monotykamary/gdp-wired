// Compile-only inference tests. An unused @ts-expect-error is a regression, not a success.
import {Schema as S4} from 'effect'
import {Schema as S3} from 'effect3'
import {Bool, Choice, Int, Maybe, Str, Term, int, rule} from './dsl.ts'
import {fromSchema, type SchemaLike, type SchemaOptions, type SchemaSymbolic} from './effect.ts'
type IsAny<T> = 0 extends 1 & T ? true : false
type NoAny<T> = IsAny<T> extends false ? true : never
const k4 = fromSchema(S4.Struct({n: S4.Int, flag: S4.Boolean, state: S4.Literals(['on', 'off']), text: S4.String, opt: S4.NullOr(S4.Int)}))
const k3 = fromSchema(S3.Struct({n: S3.Int, flag: S3.Boolean, state: S3.Literal('on', 'off'), text: S3.String, opt: S3.NullOr(S3.Int)}))
class C extends S4.Class<C>('TypesClass')({n: S4.Int}) { method() { return this.n } }
export function schemaTypeChecks(erased: SchemaLike, options: SchemaOptions) {
  for (const k of [k4, k3]) {
    const value = k.value('v')
    const noAny: NoAny<typeof value> = true, childNoAny: NoAny<typeof value.n> = true
    const n: Int = value.n, b: Bool = value.flag, c: Choice<'on' | 'off'> = value.state, s: Str = value.text, m: Maybe<Int> = value.opt
    // @ts-expect-error runtime numbers are not symbolic integers
    const raw: number = value.n
    // @ts-expect-error a signed Int is not a natural Term
    const nat: Term = value.n
    // @ts-expect-error raw labels are not symbolic choices
    const label: 'on' | 'off' = value.state
    // @ts-expect-error unknown choice label
    value.state.is('missing')
    // @ts-expect-error a nullable integer must be matched
    value.opt.plus(1)
    // @ts-expect-error no undeclared field or any leakage
    value.missing.arbitrary()
    const r = rule('typed').inputs({value: k}).state({n: int.from(0)})
    r.step(({n, value}) => ({n: n.plus(value.n)}))
    // @ts-expect-error signed input cannot go to Term.plus; migrate to signed state
    new Term({op: 'const', value: 0}).plus(value.n)
    // @ts-expect-error string is not an integer update
    r.step(() => ({n: 'oops'}))
    void [noAny, childNoAny, n, b, c, s, m, raw, nat, label]
  }
  const single4 = fromSchema(S4.TaggedStruct('Set', {n:S4.Int})).value('v')
  const single3 = fromSchema(S3.TaggedStruct('Set', {n:S3.Int})).value('v')
  for (const single of [single4, single3]) {
    const tag: Choice<'Set'> = single._tag
    const n: Int = single.n
    // @ts-expect-error a direct TaggedStruct is a record, not a Variant
    single.match({Set: () => n})
    // @ts-expect-error a direct TaggedStruct has no Variant.is
    single.is('Set')
    void tag
  }
  const singleton = fromSchema(S4.Union([S4.TaggedStruct('Set', {n:S4.Int})])).value('v')
  const singletonN: Int = singleton.n
  void singletonN
  const tagged4 = fromSchema(S4.Union([S4.TaggedStruct('Add', {n: S4.Int}), S4.TaggedStruct('Clear', {})]))
  const tagged3 = fromSchema(S3.Union(S3.TaggedStruct('Add', {n: S3.Int}), S3.TaggedStruct('Clear', {})))
  for (const k of [tagged4, tagged3]) {
    k.value('cmd').match({Add: ({n}) => n.plus(1), Clear: () => Int.of(0)})
    // @ts-expect-error every variant case must be covered
    k.value('cmd').match({Add: ({n}) => n.plus(1)})
    // @ts-expect-error no unknown variant labels
    k.value('cmd').is('Missing')
  }
  const cls = fromSchema(C, {mode: 'approximate'}).value('c')
  // @ts-expect-error approximation cannot promise the class's narrowed structural fields
  cls.n
  // @ts-expect-error structural projection has no promised class methods
  cls.method()
  const r = rule('raw nullable').inputs({x: fromSchema(S4.NullOr(S4.Int))})
  r.encodeInput({x: null})
  r.encodeInput({x: 1})
  // encodeInput is the DSL's low-level Raw boundary; rejection of undefined is checked at runtime.
  r.encodeInput({x: undefined})
  const unknownKind = fromSchema(erased)
  // @ts-expect-error erased AST means unknown, never any
  unknownKind.value('x').anything()
  const branded = [
    {plain: fromSchema(S4.String.pipe(S4.brand('Name'))), label: fromSchema(S4.Literal('ready').pipe(S4.brand('Ready'))), nested: fromSchema(S4.Struct({plain:S4.String.pipe(S4.brand('Name')), label:S4.Literal('ready').pipe(S4.brand('Ready'))}))},
    {plain: fromSchema(S3.String.pipe(S3.brand('Name'))), label: fromSchema(S3.Literal('ready').pipe(S3.brand('Ready'))), nested: fromSchema(S3.Struct({plain:S3.String.pipe(S3.brand('Name')), label:S3.Literal('ready').pipe(S3.brand('Ready'))}))},
  ]
  for (const k of branded) {
    const plain: Str = k.plain.value('s'), label: Choice<'ready'> = k.label.value('l')
    const nestedPlain: Str = k.nested.value('o').plain, nestedLabel: Choice<'ready'> = k.nested.value('o').label
    // @ts-expect-error a branded broad string is not a finite Choice
    const wrongChoice: Choice<string> = k.plain.value('s')
    // @ts-expect-error a branded literal is not an arbitrary Str
    const wrongString: Str = k.label.value('l')
    void [plain, label, nestedPlain, nestedLabel, wrongChoice, wrongString]
  }
  const brandedTag4 = fromSchema(S4.Union([S4.TaggedStruct('Set', {name:S4.String.pipe(S4.brand('Name'))}), S4.TaggedStruct('Clear', {})]))
  const brandedTag3 = fromSchema(S3.Union(S3.TaggedStruct('Set', {name:S3.String.pipe(S3.brand('Name'))}), S3.TaggedStruct('Clear', {})))
  for (const k of [brandedTag4, brandedTag3]) k.value('v').match({Set: ({name}) => name.length, Clear: () => 0})
  const exact: SchemaSymbolic<typeof S4.Int> = Int.of(-1)
  const noAny: NoAny<typeof exact> = true
  const uncertain = fromSchema(S4.Int, options).value('x')
  // @ts-expect-error options may select approximation, so this is unknown
  const uncertainInt: Int = uncertain
  const approximate = fromSchema(S4.Int, {mode: 'approximate'}).value('x')
  // @ts-expect-error explicit approximation is also unknown
  const approximateInt: Int = approximate
  const exactInt: Int = fromSchema(S4.Int, {mode: 'exact'}).value('x')
  void [noAny, uncertainInt, approximateInt, exactInt]
}
