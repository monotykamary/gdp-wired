import {expect, test} from 'bun:test'
import {all, bool, fun, maybe, nat, oneOf, record, rule, upTo, variant, when} from './dsl.ts'

for (const bits of [2, 7, 5]) test(`finite decision: ${2 ** bits} inputs, not output fields`, () => {
  const kinds: Record<string, typeof bool> = Object.fromEntries(Array.from({length: bits}, (_, i) => [`b${i}`, bool]))
  const f = fun('flags').inputs(kinds).returns(env => ({out: all(...Object.keys(kinds).map(k => env[k]!)), echo: env.b0!}))
  const reference = (values: Record<string, boolean>) => ({out: Object.values(values).every(Boolean), echo: values.b0!})
  expect(f.compare(reference)).toEqual({checked: 2 ** bits, exhaustive: true})
  const wrong = f.compare(values => ({...reference(values), out: false}))
  expect(wrong.checked).toBe(2 ** bits)
  expect(wrong.exhaustive).toBe(false)
  expect(wrong.failure).toContain('"b0":true')
})

test('finite records, active variant cases, optionals, choices and bounded naturals', () => {
  const shape = variant({empty: {}, pair: {x: oneOf('left', 'right'), flag: bool}}, {tag: 'kind'})
  const f = fun('structured').inputs({mode: oneOf('on', 'off'), n: upTo(2), opt: maybe(bool), obj: record({ok: bool}), shape})
    .returns(({obj}) => ({out: obj.ok}))
  expect(f.compare(({obj}) => ({out: obj.ok}))).toEqual({checked: 180, exhaustive: true})
})

test('edges are first and duplicate finite edges are counted once', () => {
  const f = fun('edge').inputs({a: bool, b: bool}).returns(({a}) => ({out: a}))
  const seen: string[] = []
  const result = f.compare(v => { seen.push(JSON.stringify(v)); return {out: v.a} }, {edges: [{a: true, b: true}, {a: true, b: true}]})
  expect(result).toEqual({checked: 4, exhaustive: true})
  expect(seen[0]).toBe('{"a":true,"b":true}')
})

test('unbounded and oversized finite domains sample; custom draws keep their semantics', () => {
  for (const kind of [nat, upTo(Number.MAX_SAFE_INTEGER)]) {
    const f = fun('large').inputs({n: kind}).returns(({n}) => ({out: n}))
    expect(f.compare(({n}) => ({out: n}), {trials: 3})).toEqual({checked: 3, exhaustive: false})
  }
  const f = fun('custom').inputs({a: bool}).returns(({a}) => ({out: a}))
  expect(f.compare(({a}) => ({out: a}), {trials: 3, draw: () => ({a: false})})).toEqual({checked: 3, exhaustive: false})
  expect(f.compare(({a}) => ({out: a}), {trials: 3, maxCases: 1})).toEqual({checked: 3, exhaustive: false})
  const huge: Record<string, typeof bool> = Object.fromEntries(Array.from({length: 60}, (_, i) => [`b${i}`, bool]))
  expect(fun('product').inputs(huge).returns(() => ({out: 0})).compare(() => ({out: 0}), {trials: 1})).toEqual({checked: 1, exhaustive: false})
})

test('skipped assumptions and rejected parameter tuples are not exhaustive claims', () => {
  const f = fun('assumed').inputs({a: bool}).assume(({a}) => a).returns(({a}) => ({out: a}))
  expect(f.compare(({a}) => ({out: a}))).toEqual({checked: 1, exhaustive: false, skipped: 1})
  const denied = fun('none').inputs({a: bool}).assume(({a}) => a.and(a.not())).returns(({a}) => ({out: a}))
  expect(denied.compare(({a}) => ({out: a}))).toEqual({checked: 0, exhaustive: false, skipped: 2})
  const p = fun('pre').params({p: bool}).pre(({p}) => p).inputs({a: bool}).returns(({a}) => ({out: a}))
  expect(p.compare(({a}) => ({out: a}), {params: {p: false}})).toEqual({checked: 0, exhaustive: false, skippedParams: 1})
})

test('rule finite traversal covers every parameter/input pair, with explicit bounded depth', () => {
  const r = rule('switch').params({p: bool}).inputs({a: bool}).state({on: bool.from(false)}).step(({p, a}) => ({on: p.and(a)}))
  const reference = {init: () => ({on: false}), step: (p: {p: boolean}, _s: {on: boolean}, v: {a: boolean}) => ({on: p.p && v.a})}
  expect(r.compare(reference, {depth: 1})).toEqual({checked: 4, exhaustive: true})
  expect(r.compare(reference, {trials: 2, depth: 3, params: () => ({p: true})})).toEqual({checked: 6, exhaustive: false})
  const constrained = r.pre(({p}) => p)
  expect(constrained.compare(reference)).toEqual({checked: 2, exhaustive: false, skippedParams: 1})
})

test('rule diagnostics preserve the first disagreeing trace; initial state is checked', () => {
  const r = rule('counter').inputs({a: bool}).state({n: 0}).step(({n, a}) => ({n: n.plus(when(a, 1, 0))}))
  const wrong = r.compare({init: () => ({n: 0}), step: (_p, st) => st})
  expect(wrong.checked).toBe(2)
  expect(wrong.exhaustive).toBe(false)
  expect(wrong.failure).toContain('trace [{"a":false},{"a":true}]')
  expect(r.compare({init: () => ({n: 99}), step: (_p, st) => st}).failure).toContain('at init')
})

test('reference mutations cannot corrupt canonical finite inputs or fixed parameters', () => {
  const f = fun('isolation').params({p: record({ok: bool})}).inputs({x: record({ok: bool})}).returns(({x, p}) => ({out: x.ok.and(p.ok)}))
  const params = {p: {ok: true}}
  const result = f.compare((v, p) => { const out = v.x.ok && p.p.ok; (v.x as {ok: boolean}).ok = false; (p.p as {ok: boolean}).ok = false; return {out} }, {params})
  expect(result).toEqual({checked: 2, exhaustive: true})
  expect(params).toEqual({p: {ok: true}})
})

test('comparison validates work limits and propagates reference errors', () => {
  const f = fun('limits').inputs({a: bool}).returns(({a}) => ({out: a}))
  expect(() => f.compare(() => ({}), {maxCases: 0})).toThrow('maxCases')
  expect(() => f.compare(() => ({}), {trials: -1})).toThrow('trials')
  expect(() => f.compare(() => { throw Error('reference failed') })).toThrow('reference failed')
  expect(() => f.compare((async () => ({out: true})) as never)).toThrow('synchronous object')
  const r = rule('limits').inputs({a: bool}).state({n: 0}).step(({n}) => ({n}))
  expect(() => r.compare({init: () => ({n: 0}), step: (_p, st) => st}, {depth: 0})).toThrow('depth')
})
