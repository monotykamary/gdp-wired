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

test('finite string choices preserve early returns and comparison equivalence', () => {
  const x = ok(`export function decide(a: 'red' | 'blue', b: 'red' | 'green', enabled: boolean): boolean {
    if (!enabled) return false;
    return (a === 'red') === (b === 'red');
  }`)
  const r = x.rule!, i = r.interpreter(), p = r.encodeParams({}), out = x.model!.results!.decide!
  if (out.k !== 'maybe') throw new Error('missing result')
  for (const a of ['red', 'blue']) for (const b of ['red', 'green']) for (const enabled of [false, true]) {
    const d = r.decode(i.step(p, i.init(p), r.encodeInput({a, b, enabled})))
    expect(d[out.missing]).toBe(false)
    expect(d[out.name]).toBe(enabled && ((a === 'red') === (b === 'red')))
  }
  expect(() => r.encodeInput({a: 'other', b: 'red', enabled: true})).toThrow()
})

test('finite choice result preserves each case', () => {
  const x = ok(`export function decide(a: 'red' | 'blue'): 'low' | 'high' {
    if (a === 'red') return 'high';
    return 'low';
  }`)
  const r = x.rule!, i = r.interpreter(), p = r.encodeParams({}), out = x.model!.results!.decide!
  if (out.k !== 'maybe') throw new Error('missing result')
  for (const a of ['red', 'blue']) {
    const d = r.decode(i.step(p, i.init(p), r.encodeInput({a})))
    expect(d[out.missing]).toBe(false)
    expect(d[out.name]).toBe(a === 'red' ? 'high' : 'low')
  }
})

test('nullable choice results distinguish null from undefined in false laws', () => {
  const x = ok('export function decide(flag: boolean): "yes" | "no" | null { if (flag) return null; return "yes"; }')
  const verdict = (expr: string) => {
    const built = buildLaw(x, {name: expr, expr, method: 'decide'})
    if (built.kind !== 'step') throw new Error('expected step law')
    return proveSteps(x.rule!, x.invariants ?? [], [built.law], {from: 'any', search: false})
  }
  expect(verdict('flag implies result is null')).toMatchObject({proven: true, checked: true})
  expect(verdict('flag implies result is undefined').proven).toBe(false)
  expect(verdict('flag implies result is not null').proven).toBe(false)
  const y = ok('export function decide(flag: boolean): boolean | undefined { if (flag) return undefined; return true; }')
  const built = buildLaw(y, {name: 'wrong absence', expr: 'flag implies result is null', method: 'decide'})
  if (built.kind !== 'step') throw new Error('expected step law')
  expect(proveSteps(y.rule!, y.invariants ?? [], [built.law], {from: 'any', search: false}).proven).toBe(false)
  const z = ok('export function decide(flag: boolean | undefined): boolean | null { if (flag === undefined) return null; return flag; }')
  const mismatch = buildLaw(z, {name: 'different absence', expr: 'flag == result', method: 'decide'})
  if (mismatch.kind !== 'step') throw new Error('expected step law')
  expect(proveSteps(z.rule!, z.invariants ?? [], [mismatch.law], {from: 'any', search: false}).proven).toBe(false)
  refused('export function decide(flag: boolean): "yes" | null | undefined { return flag ? "yes" : null; }', 'both null and undefined')
})

test('flat record input and result replay all values', () => {
  const x = ok(`export function decide(facts: {kind: 'red' | 'blue', enabled: boolean}): {allowed: boolean, blocked: boolean} {
    const {kind, enabled} = facts;
    return {allowed: enabled && kind === 'red', blocked: !enabled};
  }`)
  const r = x.rule!, i = r.interpreter(), p = r.encodeParams({}), out = x.model!.results!.decide!
  if (out.k !== 'rec') throw new Error('missing record result')
  const fields = Object.fromEntries(out.fields)
  for (const kind of ['red', 'blue']) for (const enabled of [false, true]) {
    const d = r.decode(i.step(p, i.init(p), r.encodeInput({facts_kind: kind, facts_enabled: enabled})))
    expect(d[fields.allowed!]).toBe(enabled && kind === 'red')
    expect(d[fields.blocked!]).toBe(!enabled)
  }
  const law = buildLaw(x, {name: 'blocked', expr: 'not facts.enabled implies result.blocked', method: 'decide'})
  if (law.kind !== 'step') throw new Error('expected step law')
  expect(proveSteps(r, x.invariants ?? [], [law.law], {from: 'any', search: false})).toMatchObject({proven: true, checked: true})
})

test('destructured record input supports early returns', () => {
  const x = ok(`export function decide({kind, enabled}: {kind: 'red' | 'blue', enabled: boolean}): boolean {
    if (!enabled) return false;
    if (kind === 'red') return true;
    return false;
  }`)
  const r = x.rule!, i = r.interpreter(), p = r.encodeParams({}), out = x.model!.results!.decide!
  if (out.k !== 'maybe') throw new Error('missing result')
  for (const kind of ['red', 'blue']) for (const enabled of [false, true]) {
    const d = r.decode(i.step(p, i.init(p), r.encodeInput({arg_kind: kind, arg_enabled: enabled})))
    expect(d[out.name]).toBe(enabled && kind === 'red')
  }
  const law = buildLaw(x, {name: 'off', expr: 'not enabled implies not result', method: 'decide'})
  if (law.kind !== 'step') throw new Error('expected step law')
  expect(proveSteps(r, x.invariants ?? [], [law.law], {from: 'any', search: false})).toMatchObject({proven: true, checked: true})
})

test('different choice domains compare by string, never encoded index', () => {
  const x = ok('export function decide(a: "red" | "blue", b: "green" | "red"): boolean { return a === b; }')
  const r = x.rule!, i = r.interpreter(), p = r.encodeParams({}), out = x.model!.results!.decide!
  if (out.k !== 'maybe') throw new Error('missing result')
  for (const a of ['red', 'blue']) for (const b of ['green', 'red']) {
    const d = r.decode(i.step(p, i.init(p), r.encodeInput({a, b})))
    expect(d[out.name]).toBe(a === b)
  }
  // The false law holds under index equality but fails for the shared string.
  const law = buildLaw(x, {name: 'different domains', expr: '(a == b) implies (a == "blue" or b == "green")', method: 'decide'})
  if (law.kind !== 'step') throw new Error('expected step law')
  expect(proveSteps(r, x.invariants ?? [], [law.law], {from: 'any', search: false}).proven).toBe(false)
})


test('finite choice support still refuses unrestricted strings and effects', () => {
  refused('export function decide(a: string) { return a === "red"; }', 'finite string choice')
  refused('export function decide(a: "red" | "blue") { console.log(a); return true; }', 'standalone:')
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
