import {expect, test} from 'bun:test'
import {extract} from './extract.ts'

// Self-authored finite machine; not the third-party function under assessment.
const code = `export function ending(n: number, flag: boolean | undefined): number | undefined {
  switch (n) {
    case 0: case 1: return 2;
    case 3: case 4: if (flag === undefined) return 7; if (flag) return 6; return 5;
  }
}`
const options = {entry: 'ending', mode: 'standalone' as const, domains: {n: 'int' as const}, check: {runs: 8, depth: 4, states: 8, probes: false as const}}
const extractOk = (source = code, opts: any = options): any => {
  const x: any = extract(source, opts)
  expect({ok: x.ok, refusals: x.refusals, evidence: x.evidence}).toMatchObject({ok: true})
  expect(x.evidence.requests).toBeGreaterThan(0)
  return x
}

test('opt-in returns exact scalar or undefined for all finite cases and repeated calls', () => {
  const x = extractOk(), r: any = x.rule, interp = r.interpreter(), ps = r.encodeParams({})
  const result = x.model.results.ending
  expect(result.k).toBe('maybe')
  let state = interp.init(ps)
  const calls = [[0, true], [1, true], [3, undefined], [3, false], [3, true], [2, true], [4, undefined], [5, false], [6, true]] as const
  for (const [n, flag] of calls) {
    const wanted = n === 0 || n === 1 ? 2 : n === 3 || n === 4 ? flag === undefined ? 7 : flag ? 6 : 5 : undefined
    state = interp.step(ps, state, r.encodeInput({n, flag: flag ?? false, flag_missing: flag === undefined}, {}))
    const actual = r.decode(state)
    expect(actual[result.missing]).toBe(wanted === undefined)
    if (wanted !== undefined) expect(actual[result.name]).toBe(wanted)
    else expect(actual[result.name]).toBe(0) // prior present value must not be carried forward
  }
  for (let n = 0; n <= 6; n++) for (const flag of [true, false, undefined]) {
    const wanted = n === 0 || n === 1 ? 2 : n === 3 || n === 4 ? flag === undefined ? 7 : flag ? 6 : 5 : undefined
    state = interp.step(ps, state, r.encodeInput({n, flag: flag ?? false, flag_missing: flag === undefined}, {}))
    const actual = r.decode(state)
    expect(actual[result.missing]).toBe(wanted === undefined)
    if (wanted !== undefined) expect(actual[result.name]).toBe(wanted)
  }
})

test('boolean result present and absent is observable', () => {
  const src = `export function decide(x: boolean | undefined): boolean | undefined { if (x === undefined) return false; if (x) return true; }`
  const x = extractOk(src, {entry: 'decide', mode: 'standalone', check: {runs: 5, depth: 3, states: 3, probes: false}})
  const r: any = x.rule, i = r.interpreter(), ps = r.encodeParams({}), result = x.model.results.decide
  let s = i.init(ps)
  for (const [value, missing, expected] of [[false, true, false], [true, false, true], [false, false, undefined]] as const) {
    s = i.step(ps, s, r.encodeInput({x: value, x_missing: missing}, {}))
    const d = r.decode(s)
    expect(d[result.missing]).toBe(expected === undefined)
    if (expected !== undefined) expect(d[result.name]).toBe(expected)
    else expect(d[result.name]).toBe(false)
  }
})

test('unchanged default is the reducer path, not standalone', () => {
  const x: any = extract(code, {entry: 'ending'})
  expect(x.ok).toBe(false)
  expect(x.model?.standalone).not.toBe(true)
  const r: any = extract('export function count(state: number, n: number): number { return state + n }', {entry: 'count', init: 0, check: {runs: 4, depth: 2, states: 2, probes: false}})
  expect({ok: r.ok, refusals: r.refusals, evidence: r.evidence}).toMatchObject({ok: true})
  expect(r.model.standalone).toBeUndefined()
  expect(r.model.shape).toBe('reducer')
})

test('null, non-scalar types, effects, calls, globals and extra module code are refused', () => {
  const bad = [
    'export function f(x: boolean | null): number { return x ? 1 : 0 }',
    'export function f(x: boolean): number | null { if (x) return null; return 1 }',
    'export function f(x: number | undefined): number { return x ?? 0 }',
    'export function f(x: string): number { return 1 }',
    'export function f(x: number): number { return Math.abs(x) }',
    'export function f(x: number): number { x++; return x }',
    'export function f(x: number): number { return Date.now() }',
    'export function f(x: number): number { throw x }',
    'export function f(x: number): number { return x } console.log("effect")',
    'const y = 1; export function f(x: number): number { return x + y }',
  ]
  for (const source of bad) {
    const x: any = extract(source, {entry: 'f', mode: 'standalone'})
    expect(x.ok).toBe(false)
    expect(x.refusals.length).toBeGreaterThan(0)
    expect(x.evidence).toBeUndefined()
  }
})

test('standalone requires explicit single entry and excludes other shape and ORM options', () => {
  for (const options of [{mode: 'standalone'}, {entry: ['a', 'b'], mode: 'standalone'}, {entry: 'ending', mode: 'standalone', shape: 'functions'}]) {
    const x: any = extract(code, options as any)
    expect(x.ok).toBe(false)
  }
})
