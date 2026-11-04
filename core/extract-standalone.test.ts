import {expect, test} from 'bun:test'
import {extract} from './extract.ts'
import {check as checkSource} from './extract-check.ts'

const check = {runs: 20, depth: 5, states: 20, probes: false as const}
const options = {entry: 'decide', mode: 'standalone' as const, check}
// Owned examples, not an annotation or rewrite of any assessed repository.
const code = `import type {Ignored} from './types';
const LOW = -3;
const HIGH = 9;
type Code = typeof LOW | typeof HIGH;
const labels = ['unused', 'inert'] as const;
export const unrelated = (cb: () => void) => { cb(); };
const answer = (b: boolean | undefined) => b ? HIGH : LOW;
export function decide(n: Code, flag: boolean | undefined): number | undefined {
  switch (n) { case LOW: return answer(flag); case HIGH: if (flag !== undefined) return n; }
}`
const ok = (source = code, extra = {}) => {
  const x = extract(source, {...options, ...extra})
  expect({ok: x.ok, refusals: x.refusals, evidence: x.evidence}).toMatchObject({ok: true})
  expect(x.evidence!.requests).toBeGreaterThan(0)
  return x
}
const refused = (source: string, message?: string) => {
  const x = extract(source, options)
  expect(x.ok).toBe(false)
  expect(x.evidence).toBeUndefined()
  if (message) expect(x.refusals.map(r => r.what).join(' ')).toContain(message)
}

test('closed constants, erased import, pure helper and uncalled callback declaration', () => {
  const x = ok(), r = x.rule!, i = r.interpreter(), ps = r.encodeParams({}), out = x.model!.results!.decide!
  expect(out.k).toBe('maybe')
  if (out.k !== 'maybe') throw new Error('missing optional result')
  expect(x.model!.standaloneBindings).toEqual(['HIGH', 'LOW', 'answer', 'decide'])
  expect(x.model!.standaloneDomains).toEqual({n: [-3, 9]})
  // Both literal-domain values have explicit cases: only the instrumented
  // no-case arm is unreachable. Keep it visible, never suppress it as covered.
  expect(x.evidence!.coverage.arms).toBe(7)
  expect(x.evidence!.coverage.hit).toBe(6)
  expect(x.evidence!.coverage.missed).toEqual([expect.stringContaining('switch: no case')])
  expect(x.notes.join(' ')).toContain('safe integers')
  expect(x.source).toContain('a standalone scalar function')
  expect(x.notes.join(' ')).toContain('other values are outside the claim')
  let st = i.init(ps)
  for (const n of [-3, 9]) for (const flag of [undefined, false, true]) {
    st = i.step(ps, st, r.encodeInput({n, flag: flag ?? false, flag_missing: flag === undefined}))
    const d = r.decode(st), wanted = n === -3 ? flag ? 9 : -3 : flag === undefined ? undefined : 9
    expect(d[out.missing]).toBe(wanted === undefined)
    expect(d[out.name]).toBe(wanted ?? 0)
  }
  expect(() => i.step(ps, st, r.encodeInput({n: 0, flag: false, flag_missing: true}))).toThrow()
  for (const n of [0.25, NaN, Infinity, Number.MAX_SAFE_INTEGER + 1]) expect(() => r.encodeInput({n, flag: false, flag_missing: true})).toThrow()
})

test('helper parameters bind by symbol rather than a same-named module constant', () => {
  const x = ok('const n = 100; function id(n: number) { return n; } export function decide(n: number) { return id(n); }')
  expect(x.model!.standaloneBindings).toEqual(['decide', 'id'])
  const r = x.rule!, i = r.interpreter(), p = r.encodeParams({}), out = x.model!.results!.decide!
  if (out.k !== 'maybe') throw new Error('missing result')
  for (const n of [-15, 0, 15]) expect(r.decode(i.step(p, i.init(p), r.encodeInput({n})))[out.name]).toBe(n)
})

test('multi-return helper retains present false separately from undefined', () => {
  ok('function helper(x: boolean | undefined): boolean | undefined { if (x === undefined) return false; if (x) return true; } export function decide(x: boolean | undefined) { return helper(x); }')
})

test('numeric union works through a supplied erased type module', () => {
  const x = ok("import type {Code} from './types'; export function decide(n: Code) { return n; }", {files: {'types.ts': 'export type Code = -7 | 11;'}})
  expect(x.model!.standaloneDomains).toEqual({n: [-7, 11]})
})

test('prover witnesses replay returns, not prior result fields as source state', () => {
  const x = ok('const A = 4 as const; const helper = (b: boolean | undefined) => b ? A : 2; export function decide(n: -3 | 9, b: boolean | undefined) { return helper(b) satisfies number; }', {check: {...check, probes: 'writes'}})
  expect(x.evidence!.probes.steps).toBeGreaterThan(0)
})

test('empty source state never hides a wrong return or missing bit in prover probes', () => {
  const source = 'export function decide(n: number, x: boolean | undefined): number | undefined { if (x === undefined) return undefined; return x ? n + 1 : n - 1; }'
  const correct = ok(source)
  for (const wrongSource of [
    'export function decide(n: number, x: boolean | undefined): number | undefined { if (x === undefined) return undefined; return x ? n + 2 : n - 2; }',
    'export function decide(n: number, x: boolean | undefined): number | undefined { if (x === undefined) return 0; return x ? n + 1 : n - 1; }',
  ]) {
    const wrong = ok(wrongSource)
    const evidence = checkSource(source, 'input.ts', correct.model!, wrong.rule!, correct.sorts!, {runs: 0, states: 0, probes: 'writes'})
    expect(evidence.probes.steps).toBeGreaterThan(0)
    expect(evidence.mismatch).toContain('returns')
    expect(evidence.mismatch).not.toContain('in the code, undefined in the rule')
  }
})

test('scalar constants may depend on earlier constants', () => {
  ok('const a = 3; const b = a; export function decide(x: boolean) { return x ? b : -a; }')
})

test('module evaluation and imported runtime code are refused before execution', () => {
  for (const src of [
    "import {n} from './runtime'; export function decide() { return 1; }",
    "import './runtime'; export function decide() { return 1; }",
    "export * from './runtime'; export function decide() { return 1; }",
    'const n = Date.now(); export function decide() { return 1; }',
    'const n = (() => 1)(); export function decide() { return 1; }',
    'let n = 1; export function decide() { return n; }',
    'export function decide() { return 1; } console.log(1);',
    'const b = a; const a = 1; export function decide() { return b; }',
  ]) refused(src)
})

test('reachable helper effects, closures, mutation and recursion are refused statically', () => {
  for (const src of [
    'function h() { console.log(1); return 1; } export function decide() { return h(); }',
    'const h = (n: number) => h(n); export function decide(n: number) { return h(n); }',
    'function a(n: number): number { return b(n); } function b(n: number): number { return a(n); } export function decide(n: number) { return a(n); }',
    'function h(n: number) { n++; return n; } export function decide(n: number) { return h(n); }',
    'export function decide(n: number) { const h = () => n; return h(); }',
    'function h() { throw 1; } export function decide() { return h(); }',
    'const h = async () => 1; export function decide() { return h(); }',
    'export function decide(h: () => number) { return h(); }',
    'const xs = [1,2]; export function decide() { return xs[0]; }',
  ]) refused(src)
})

test('invalid modes and contradictory numeric domains are not silently ignored', () => {
  expect(extract(code, {...options, mode: 'typo' as never}).ok).toBe(false)
  const x = extract(code, {...options, domains: {n: 'nat'}})
  expect(x.ok).toBe(false); expect(x.evidence).toBeUndefined()
})

test('nonintegral declared numeric domains and literals cannot be widened silently', () => {
  refused('export function decide(n: 0.25 | 1) { return n; }', 'safe integers')
  refused('export function decide(n: number) { return n + 0.25; }', 'safe integer')
})
