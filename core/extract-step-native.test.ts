import {expect, test} from 'bun:test'
import {mkdtempSync, writeFileSync, rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {extractPython, type PyOptions} from './extract-py.ts'
import {buildLaw} from './laws.ts'
import {proveSteps} from './dsl.ts'

// Native bindings must come from Python's callable, not from protocol envelopes
// or the symbolic input names. The local write must not change the saved input.
const code = `class Counter:
    def __init__(self):
        self.total = 0
    def credit(self, n: int = 7):
        self.total += n
        n += 1
        return n
`
const extract = (disabled = false, source = code, options: PyOptions = {}) => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-native-bindings-`)
  try {
    const file = `${dir}/counter.py`
    writeFileSync(file, source)
    const x = extractPython(file, {entry: 'Counter', ...options, check: disabled ? {runs: 0, states: 0, probes: false} : {runs: 8, depth: 3, states: 0, probes: false}})
    expect(x.ok).toBe(true)
    expect(x.evidence?.mismatch).toBeUndefined()
    return x
  } finally { rmSync(dir, {recursive: true, force: true}) }
}

test('Python native bindings retain the actual request before local reassignment', () => {
  const x = extract()
  const b = buildLaw(x, {name: 'credit is exact', expr: 'total == old(total) + n and result == n + 1', method: 'credit'})
  if (b.kind !== 'step') throw Error('expected a step law')
  const v = proveSteps(x.rule!, x.invariants ?? [], [b.law], {search: false})
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
})

test('Python native bindings still reject a falsely lowered law with its real input', () => {
  const x = extract()
  const b = buildLaw(x, {name: 'faulty lowering', expr: 'result == n + 2', method: 'credit'})
  if (b.kind !== 'step') throw Error('expected a step law')
  b.law.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const v = proveSteps(x.rule!, x.invariants ?? [], [b.law], {search: false})
  expect(v).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error', stuck: 'translation-error'})
  expect(v.why).toContain('translation error: faulty lowering is false in the native code')
  expect(v.translationWitness?.bindings).toHaveProperty('n')
})

test('Python native bindings capture a genuinely omitted None default', () => {
  const x = extract(false, `class Counter:
    def __init__(self):
        self.total = 0
    def credit(self, n: None = None):
        self.total += 1
        return n is None
`)
  // PArg dflt is omitted by Python fixed_args(), not passed as explicit None.
  expect(x.read?.args.credit).toEqual([['n', {k: 'dflt'}]])
  const correct = buildLaw(x, {name: 'omitted default is None', expr: 'result == true', method: 'credit'})
  if (correct.kind !== 'step') throw Error('expected a step law')
  const accepted = proveSteps(x.rule!, x.invariants ?? [], [correct.law], {search: false})
  expect(accepted).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(accepted.translationChecks).toBeGreaterThan(0)
  const wrong = buildLaw(x, {name: 'wrong default result', expr: 'result == false', method: 'credit'})
  if (wrong.kind !== 'step') throw Error('expected a step law')
  wrong.law.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const rejected = proveSteps(x.rule!, x.invariants ?? [], [wrong.law], {search: false})
  expect(rejected).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error'})
  expect(rejected.translationWitness?.args).toEqual([['n', {dflt: true}]])
  expect(rejected.translationWitness?.bindings).toMatchObject({n: null})
})

for (const [metadata, suffix] of [
  ['__signature__', `import inspect
Counter.credit.__signature__ = inspect.Signature([
    inspect.Parameter('self', inspect.Parameter.POSITIONAL_OR_KEYWORD),
    inspect.Parameter('n', inspect.Parameter.POSITIONAL_OR_KEYWORD, default=999),
])`],
  ['__wrapped__', `def fabricated(self, n=999):
    return n
Counter.credit.__wrapped__ = fabricated`],
  ['__text_signature__', `Counter.credit.__text_signature__ = '($self, n=999)'`],
  ['__dict__ membership-hidden __text_signature__', `class Hidden(dict):
    def __contains__(self, key):
        return False
Counter.credit.__dict__ = Hidden(__text_signature__='($self, n=999)')`],
]) test(`Python native bindings refuse customized ${metadata} on the underlying method`, () => {
  const x = extract(false, `${code}\n${suffix}\n`)
  expect(x.evidence!.requests).toBeGreaterThan(0)
  const b = buildLaw(x, {name: 'credit is exact', expr: 'total == old(total) + n and result == n + 1', method: 'credit'})
  if (b.kind !== 'step') throw Error('expected a step law')
  expect(proveSteps(x.rule!, x.invariants ?? [], [b.law], {search: false})).toMatchObject({
    proven: false, checked: false, kernelProven: true, translation: 'unchecked',
    why: 'source translation unchecked: native observation unavailable: native parameter capture: ValueError: customized native signature metadata is unsupported',
  })
})

test('Python nonordered datetime state explicitly refuses registered native-law admission', () => {
  const x = extract(false, `class Counter:
    def __init__(self, start):
        self.until = start
    def clear(self):
        self.until = None
`, {types: {start: 'datetime-utc', until: 'datetime-utc | None'}})
  expect(x.read?.leaves.some(leaf => leaf.ordered)).toBe(false)
  expect(x.evidence!.requests).toBeGreaterThan(0)
  const b = buildLaw(x, {name: 'clear removes the deadline', expr: 'until is None', method: 'clear'})
  if (b.kind !== 'step') throw Error('expected a step law')
  expect(proveSteps(x.rule!, x.invariants ?? [], [b.law], {search: false})).toMatchObject({
    proven: false, checked: false, kernelProven: true, translation: 'unchecked',
    why: 'source translation unchecked: native observation unavailable: native snapshot: "TypeError: vars() argument must have __dict__ attribute"',
  })
})

test('Python native bindings cannot replace disabled source replay', () => {
  const x = extract(true)
  const b = buildLaw(x, {name: 'credit is exact', expr: 'total == old(total) + n', method: 'credit'})
  if (b.kind !== 'step') throw Error('expected a step law')
  expect(proveSteps(x.rule!, x.invariants ?? [], [b.law], {search: false})).toMatchObject({
    proven: false, checked: false, translation: 'unchecked',
    why: 'source translation unchecked: source replay or native-law cross-check was disabled',
  })
})
