import {expect, test} from 'bun:test'
import {extract} from './extract.ts'
import {buildLaw, parse} from './laws.ts'
import {nativeLaw} from './native-law.ts'
import {all, proveDecision, proveRule, proveSteps, rule} from './dsl.ts'
import {twoRuns} from './relational.ts'
import {inEnv} from './system.ts'
import {type NativeObservation, nativeSame, nativeSnapshot} from './source-check.ts'
import {nativeInputs} from './native-domain.ts'
import {type CheckOptions, sandbox} from './extract-check.ts'

const options = {entry: 'decide', mode: 'standalone' as const, check: {runs: 1, depth: 1, states: 0, probes: false as const}}
const source = 'export function decide(a: boolean, b: boolean): boolean { return a && b; }'
const built = (text: string, check: CheckOptions = options.check) => {
  const x = extract(source, {...options, check})
  expect(x.ok).toBe(true)
  const b = buildLaw(x, {name: text, expr: text, method: 'decide'})
  if (b.kind !== 'step') throw new Error('expected step law')
  return {x, b}
}

test('source law: native finite-domain cross-check is mandatory after a kernel proof', () => {
  const {x, b} = built('result == (a and b)')
  const v = proveSteps(x.rule!, x.invariants ?? [], [b.law], {from: 'any', search: false})
  expect(v).toMatchObject({proven: true, checked: true, translation: 'exhaustive'})
  expect(v.translationChecks).toBeGreaterThanOrEqual(5)
})

test('source law: a faulty law lowering is refused with a native witness', () => {
  const {x, b} = built('result == a')
  // Positive control: corrupt only the translated law, not its source syntax or native code.
  b.law.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const v = proveSteps(x.rule!, x.invariants ?? [], [b.law], {from: 'any', search: false})
  expect(v).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error'})
  expect(v.why).toContain('translation error')
  expect(v.translationWitness).toMatchObject({method: 'decide', bindings: {a: true, b: false}, result: false})
})

test('source law: a hidden numeric payload cannot replace an absent native result', () => {
  const x = extract('export function decide(flag: boolean): number | undefined { if (flag) return 0; }', {...options, check: options.check})
  const b = buildLaw(x, {name: 'faulty optional lowering', expr: 'result == 0', method: 'decide'})
  b.law.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const v = proveSteps(x.rule!, x.invariants ?? [], [b.law], {from: 'any', search: false})
  expect(v).toMatchObject({proven: false, translation: 'error', kernelProven: true})
  expect(v.translationWitness?.result).toBeUndefined()
})

test('source law: disabled source replay cannot yield a source proof', () => {
  const {x, b} = built('result == (a and b)', {runs: 0, states: 0, probes: false})
  expect(proveSteps(x.rule!, x.invariants ?? [], [b.law], {from: 'any', search: false})).toMatchObject({proven: false, checked: false, translation: 'unchecked'})
})

test('source law: explicit law-cross-check disablement cannot yield a source proof', () => {
  const x = extract(source, {...options, check: {...options.check, lawCrossCheck: false}})
  const b = buildLaw(x, {name: 'valid', expr: 'result == (a and b)', method: 'decide'})
  expect(proveSteps(x.rule!, x.invariants ?? [], [b.law], {search: false})).toMatchObject({proven: false, translation: 'unchecked'})
})

test('native law semantics: undefined, NaN, choices and truthiness are not hidden payloads', () => {
  const observation: NativeObservation = {where: 'test', method: 'decide', before: {}, after: {}, params: {}, inputs: {}, bindings: {}, args: [], result: undefined, failed: false}
  const evaluate = (text: string, result?: unknown) => nativeLaw(parse(text), {clock: 1, calendar: {}}, parse)({...observation, result})
  expect(evaluate('result - 0 <= 1 business days')).toBe(false)
  expect(evaluate('1 business days >= result - 0')).toBe(false)
  expect(evaluate('result >= 0')).toBe(false)
  expect(evaluate('result is null')).toBe(false)
  expect(evaluate('result is undefined')).toBe(true)
  expect(evaluate('not result')).toBe(true)
  expect(evaluate('result == "green"', 'green')).toBe(true)
  expect(evaluate('result == "red"', 'green')).toBe(false)
  expect(evaluate('result - 0 <= 1 business days', 86400)).toBe(true)
})

test('native inputs: original TypeScript types determine finite domains', () => {
  const result = nativeInputs('type N = 0 | 1; export function decide(arg: {enabled: boolean}, n: N) { return arg.enabled; }', 'finite.ts', 'decide')
  expect(result.reason).toBeUndefined()
  expect(result.domains?.map(d => d.length)).toEqual([2, 2])
  expect(nativeInputs('export function decide(n: number) { return n; }', 'infinite.ts', 'decide').domains).toBeUndefined()
  const args = Array.from({length: 17}, (_, i) => `a${i}: boolean`).join(', ')
  expect(nativeInputs(`export function decide(${args}) { return a0; }`, 'large.ts', 'decide').reason).toContain('exhaustive bound')
})

test('native bindings: defaults and destructuring are captured after JS binds them', () => {
  const box = sandbox('export function decide({enabled}: {enabled: boolean}, flag: boolean = true) { return enabled && flag; }', 'bindings.ts', ['decide'], {}, undefined, {}, [], ['decide'])
  expect(box.call('decide', undefined, [{enabled: true}, undefined])).toMatchObject({ok: true, value: true})
  expect(box.bindings('decide')).toEqual({enabled: true, flag: true})
})

test('native bindings survive a factory closure snapshot helper', () => {
  const box = sandbox('export function decide(flag: boolean) { return flag; } export function $get() { return {}; }', 'closure.ts', ['decide', '$get'], {}, undefined, {}, [], ['decide'])
  expect(box.call('decide', undefined, [true]).ok).toBe(true)
  expect(box.call('$get', undefined, []).ok).toBe(true)
  expect(box.bindings('decide')).toEqual({flag: true})
})

test('native snapshots preserve identity between before/after while preserving changed fields', () => {
  const item = {value: 1}, before = nativeSnapshot({items: [item]}) as {items: {value: number}[]}
  item.value = 2
  const after = nativeSnapshot({items: [item]}) as {items: {value: number}[]}
  expect(before.items[0]!.value).toBe(1)
  expect(after.items[0]!.value).toBe(2)
  expect(nativeSame(before.items[0], after.items[0])).toBe(true)
  const o: NativeObservation = {where: 'identity', before, after, params: {}, inputs: {}, bindings: {}, args: [], result: undefined, failed: false}
  const holds = nativeLaw(parse('forall x in old(items): x in items'), {}, parse)
  expect(holds(o)).toBe(true)
  expect(holds({...o, after: nativeSnapshot({items: [{value: 2}]})})).toBe(false)
})

test('source-derived rule copies cannot silently become unchecked DSL proofs', () => {
  const {x} = built('result == (a and b)')
  const copied = x.rule!.keep(() => all())
  const v = proveRule(copied, [copied.law('tautology', () => all())], {search: false})
  expect(v).toMatchObject({proven: false, checked: false, translation: 'unchecked'})
})

test('mathematical divisor declarations preserve the original native interpretation', () => {
  const {x, b} = built('result == (a and b)')
  expect(proveSteps(x.rule!.withDivisors(2), x.invariants ?? [], [b.law], {from: 'any', search: false}))
    .toMatchObject({proven: true, checked: true, translation: 'exhaustive'})
})

test('source-derived decisions and composed rules cannot bypass native validation', () => {
  const r = rule('source').state({n: 0}).step(({n}) => ({n}))
  Object.defineProperty(r, Symbol.for('gdp-wired.source-proof.v1'), {value: true})
  expect(proveDecision(r.decide('identity', () => all(), () => all()))).toMatchObject({proven: false, translation: 'unchecked'})
  for (const derived of [twoRuns(r), inEnv(r, {}).rule]) {
    expect(proveRule(derived, [derived.law('identity', () => all())], {search: false}))
      .toMatchObject({proven: false, checked: false, translation: 'unchecked'})
  }
})

test('a source marker without local metadata fails closed across module copies', () => {
  const r = rule('foreign source').state({value: 0}).step(({value}) => ({value}))
  Object.defineProperty(r, Symbol.for('gdp-wired.source-proof.v1'), {value: true})
  expect(proveRule(r, [r.law('nonnegative', ({value}) => value.atLeast(0))], {search: false}))
    .toMatchObject({proven: false, checked: false, translation: 'unchecked'})
})

test('ordinary DSL proofs do not acquire a source-translation requirement', () => {
  const r = rule('plain').state({value: 0}).step(({value}) => ({value}))
  const v = proveRule(r, [r.law('nonnegative', ({value}) => value.atLeast(0))], {search: false})
  expect(v).toMatchObject({proven: true, checked: true})
  expect(v.translation).toBeUndefined()
})
