import {expect, test} from 'bun:test'
import {extract} from './extract.ts'
const check = {runs: 4, depth: 2, states: 2, probes: false as const}
const options = {entry: 'f', mode: 'standalone' as const, check}
const requireOk = (source: string, more = {}): any => {
  const e: any = extract(source, {...options, ...more})
  expect({ok: e.ok, refusals: e.refusals, evidence: e.evidence}).toMatchObject({ok: true})
  expect(e.evidence.requests).toBeGreaterThan(0)
  return e
}
const optionalCases = (source: string) => {
  const e = requireOk(source), r = e.rule, i = r.interpreter(), ps = r.encodeParams({}), result = e.model.results.f
  let s = i.init(ps)
  for (const [value, missing, expected] of [[true, false, true], [false, false, false], [false, true, undefined], [false, false, false]] as const) {
    s = i.step(ps, s, r.encodeInput({x: value, x_missing: missing}, {}))
    const d = r.decode(s)
    expect(d[result.missing]).toBe(expected === undefined)
    if (expected !== undefined) expect(d[result.name]).toBe(expected)
  }
}
test('direct return retains present false after falsy branch', () => optionalCases(`export function f(x: boolean | undefined): boolean | undefined { if (x) return true; return x; }`))
test('ternary retains present false after falsy branch', () => optionalCases(`export function f(x: boolean | undefined): boolean | undefined { return x ? true : x; }`))
test('negated branch retains present false', () => optionalCases(`export function f(x: boolean | undefined): boolean | undefined { if (!x) return x; return true; }`))
test('shadowed undefined is explicitly refused before executing conformance', () => {
  const e: any = extract(`export function f(x: boolean | undefined, undefined: boolean): boolean | undefined { if (x === undefined) return x; return false; }`, options)
  expect(e.ok).toBe(false); expect(e.refusals.map((x: any) => x.what).join(' ')).toContain('reserved parameter undefined'); expect(e.evidence).toBeUndefined()
})
test('coverage-helper parameter is explicitly refused before executing conformance', () => {
  const e: any = extract(`export function f(__cov: boolean): number { if (__cov) return 1; return 0; }`, options)
  expect(e.ok).toBe(false); expect(e.refusals.map((x: any) => x.what).join(' ')).toContain('reserved parameter __cov'); expect(e.evidence).toBeUndefined()
})
test('reserved names on named function expressions and default declarations are refused', () => {
  const sources = [
    `export const f = function __cov(x: boolean): number { if (x) return 1; return 0; };`,
    `export const f = function undefined(): boolean { return !!undefined; };`,
    `export default function __cov(x: boolean): number { if (x) return 1; return 0; }`,
  ]
  for (const [i, source] of sources.entries()) {
    const e: any = extract(source, {...options, entry: i === 2 ? 'default' : 'f'})
    expect(e.ok).toBe(false); expect(e.refusals.map((x: any) => x.what).join(' ')).toContain('reserved function name'); expect(e.evidence).toBeUndefined()
  }
})
test('safe function-expression and default-declaration bindings remain supported', () => {
  requireOk(`export const f = function kept(x: boolean): number { if (x) return 1; return 0; };`)
  requireOk(`export const f = function kept(): boolean { return true; };`)
  requireOk(`export default function kept(x: boolean): number { if (x) return 1; return 0; }`, {entry: 'default'})
})
test('true alpha-renaming of a self-referential undefined function is refused as a non-input identifier', () => {
  const e: any = extract(`export const f = function kept(): boolean { return !!kept; };`, options)
  expect(e.ok).toBe(false); expect(e.refusals.map((x: any) => x.what).join(' ')).toContain('non-input identifier'); expect(e.evidence).toBeUndefined()
})
test('erased TypeScript this parameter is explicitly refused before conformance', () => {
  const e: any = extract(`export function f(this: boolean, x: boolean): boolean { return x; }`, options)
  expect(e.ok).toBe(false); expect(e.refusals.map((x: any) => x.what).join(' ')).toContain('reserved parameter this'); expect(e.evidence).toBeUndefined()
  const control = requireOk(`export function f(y: boolean, x: boolean): boolean { return x; }`)
  const r = control.rule, i = r.interpreter(), ps = r.encodeParams({}), out = control.model.results.f
  let s = i.init(ps)
  for (const [y, x] of [[true, false], [false, true]] as const) {
    s = i.step(ps, s, r.encodeInput({y, x}, {})); const d = r.decode(s)
    expect(d[out.missing]).toBe(false); expect(d[out.name]).toBe(x)
  }
})
test('join collision is refused, alpha-renamed control gives the expected values', () => {
  const collision: any = extract(`export function f($join: number, b: boolean): number { return (b ? 1 : 2) + $join; }`, options)
  expect(collision.ok).toBe(false); expect(collision.refusals.map((x: any) => x.what).join(' ')).toContain('reserved parameter $join'); expect(collision.evidence).toBeUndefined()
  const e = requireOk(`export function f(kept: number, b: boolean): number { return (b ? 1 : 2) + kept; }`, {domains: {kept: 'int'}})
  const r = e.rule, i = r.interpreter(), ps = r.encodeParams({}), result = e.model.results.f
  let s = i.init(ps)
  for (const [b, value] of [[true, 4], [false, 5]] as const) {
    s = i.step(ps, s, r.encodeInput({kept: 3, b}, {}))
    const d = r.decode(s); expect(d[result.missing]).toBe(false); expect(d[result.name]).toBe(value)
  }
})
test('generated missing and result names do not alias user parameter names', () => {
  const e = requireOk(`export function f(f_result: number, flag: boolean | undefined, flag_missing: boolean): number | undefined { if (flag === undefined) return f_result; if (flag_missing) return 42; }`, {domains: {f_result: 'int'}})
  const r = e.rule, i = r.interpreter(), ps = r.encodeParams({}), out = e.model.results.f
  expect(out.name).not.toBe('f_result')
  let s = i.init(ps)
  for (const [value, missing, other, expected] of [[false, true, false, 9], [true, false, true, 42], [false, false, false, undefined]] as const) {
    s = i.step(ps, s, r.encodeInput({f_result: 9, flag: value, flag_missing: missing, flag_missing_2: other}, {}))
    const d = r.decode(s); expect(d[out.missing]).toBe(expected === undefined)
    if (expected !== undefined) expect(d[out.name]).toBe(expected)
  }
})
test('default reducer and class modes remain available', () => {
  const reducer: any = extract(`export function sum(state: number, amount: number): number { return state + amount }`, {entry: 'sum', init: 0, check})
  expect({ok: reducer.ok, refusals: reducer.refusals}).toMatchObject({ok: true})
  expect(reducer.model.standalone).toBeUndefined()
  const klass: any = extract(`export class Counter { count = 0; bump(): void { this.count++ } }`, {entry: 'Counter', check})
  expect({ok: klass.ok, refusals: klass.refusals}).toMatchObject({ok: true})
  expect(klass.model.standalone).toBeUndefined(); expect(klass.model.shape).toBe('class')
})
