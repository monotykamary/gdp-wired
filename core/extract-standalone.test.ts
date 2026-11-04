import {expect, test} from 'bun:test'
import {extract} from './extract.ts'
import {check as checkSource} from './extract-check.ts'
import {buildLaw} from './laws.ts'
import {proveSteps} from './dsl.ts'
import {evalC} from './machine.ts'

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

test('standalone laws preserve optional boolean truth, absence and hidden payloads', () => {
  const x = ok('export function decide(flag: boolean | undefined): boolean | undefined { return flag; }')
  const verdict = (expr: string) => {
    const built = buildLaw(x, {name: expr, expr, method: 'decide', where: 'owned.ts', line: 1})
    if (built.kind !== 'step') throw new Error('expected step law')
    return proveSteps(x.rule!, x.invariants ?? [], [built.law], {from: 'any', search: false})
  }
  for (const expr of [
    'flag == true implies result == true',
    'flag == false implies result == false',
    'flag is undefined implies result is undefined',
    'flag is undefined implies (flag != true and flag != false)',
    'flag is undefined implies not flag',
    'flag implies result == true',
    'flag == result',
    'result is undefined implies (result != true and result != false)',
  ]) expect({expr, ...verdict(expr)}).toMatchObject({proven: true, checked: true})
  // These were falsely tautological when comparisons discarded the missing bit.
  for (const expr of ['flag == true or flag == false', 'result == true or result == false']) {
    const failed = verdict(expr)
    expect(failed).toMatchObject({proven: false, checked: false})
    expect(failed.witness?.flag_missing).toBe(1)
  }
})

test('standalone laws preserve optional numeric comparisons and refuse absent arithmetic', () => {
  const x = ok('export function decide(flag: boolean): number | undefined { if (flag) return 4; }')
  const law = (expr: string) => buildLaw(x, {name: expr, expr, method: 'decide', where: 'owned.ts', line: 1})
  for (const expr of ['result is undefined implies result != 0', 'result is undefined implies not (result >= 0)', 'flag implies result == 4']) {
    const built = law(expr)
    if (built.kind !== 'step') throw new Error('expected step law')
    expect(proveSteps(x.rule!, x.invariants ?? [], [built.law], {from: 'any', search: false})).toMatchObject({proven: true, checked: true})
  }
  for (const expr of ['result + 1 > 0', '-result < 0', 'abs(result) >= 0', 'max(result, 0) >= 0']) expect(() => law(expr)).toThrow('arithmetic on an optional standalone value is not supported')
})

test('standalone optional predicates check both hidden boolean values and present values', () => {
  const x = ok('export function decide(flag: boolean | undefined): boolean | undefined { return flag; }')
  const r = x.rule!, st = r.interpreter().init(r.encodeParams({}))
  for (const missing of [false, true]) for (const hidden of [false, true]) {
    const env: Record<string, number> = {}
    for (const [key, value] of Object.entries(r.encodeInput({flag: hidden, flag_missing: missing}))) if (typeof value === 'number') env[key] = value
    const cases: [string, boolean][] = [
      ['flag == true', !missing && hidden],
      ['flag == false', !missing && !hidden],
      ['flag != true', missing || !hidden],
      ['flag != false', missing || hidden],
      ['flag is undefined', missing],
      ['not flag or false', missing || !hidden],
      ['flag == true or flag == false', !missing],
    ]
    for (const [expr, expected] of cases) {
      const built = buildLaw(x, {name: expr, expr, method: 'decide'})
      expect({expr, missing, hidden, actual: evalC(built.law.then, env, st, r.machine)}).toEqual({expr, missing, hidden, actual: expected})
    }
  }
})

test('optional floor-division refuses original numerators before comparison rewrites', () => {
  const x = ok('export function decide(flag: boolean): number | undefined { if (flag) return 4; }')
  for (const op of ['==', '!=', '<', '<=', '>', '>=']) for (const expr of [`result // 2 ${op} 0`, `0 ${op} result // 2`]) {
    for (const expression of [expr, `not (${expr})`]) {
      expect(() => buildLaw(x, {name: expression, expr: expression, method: 'decide'})).toThrow('arithmetic on an optional standalone value is not supported')
    }
  }
})

test('nonoptional division rewrites retain standalone and default-reader semantics', () => {
  const standalone = ok('export function decide(n: number): number { return n; }')
  const legacy = extract('export class Counter { value = 0; set(n: number) { this.value = n; } }', {entry: 'Counter', check})
  expect(legacy.ok).toBe(true)
  expect(legacy.model?.standalone).not.toBe(true)
  const comparisons: Record<string, (a: number, b: number) => boolean> = {
    '==': (a, b) => a === b, '!=': (a, b) => a !== b,
    '<': (a, b) => a < b, '<=': (a, b) => a <= b,
    '>': (a, b) => a > b, '>=': (a, b) => a >= b,
  }
  for (const [x, method, values] of [[standalone, 'decide', [-4, -3, -1, 0, 1, 2, 3, 4]], [legacy, 'set', [0, 1, 2, 3, 4]]] as const) {
    const r = x.rule!, st = r.interpreter().init(r.encodeParams({}))
    const inputName = x.names!.find(n => n.role === 'input' && n.code === 'n' && n.method === method)!.rule
    for (const [op, compare] of Object.entries(comparisons)) for (const left of [false, true]) for (const negate of [false, true]) {
      const expr = left ? `n // 2 ${op} 0` : `0 ${op} n // 2`
      const built = buildLaw(x, {name: expr, expr: negate ? `not (${expr})` : expr, method})
      for (const n of values) {
        const env: Record<string, number> = {}
        for (const [key, value] of Object.entries(r.encodeInput({[inputName]: n, method}))) if (typeof value === 'number') env[key] = value
        const expected = left ? compare(Math.floor(n / 2), 0) : compare(0, Math.floor(n / 2))
        expect(evalC(built.law.then, env, st, r.machine)).toBe(negate ? !expected : expected)
      }
    }
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
