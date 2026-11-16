import {expect, test} from 'bun:test'
import {mkdtempSync, writeFileSync, rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {extractPython} from './extract-py.ts'
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
const extract = (disabled = false) => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-native-bindings-`)
  try {
    const file = `${dir}/counter.py`
    writeFileSync(file, code)
    const x = extractPython(file, {entry: 'Counter', check: disabled ? {runs: 0, states: 0, probes: false} : {runs: 8, depth: 3, states: 0, probes: false}})
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

test('Python native bindings cannot replace disabled source replay', () => {
  const x = extract(true)
  const b = buildLaw(x, {name: 'credit is exact', expr: 'total == old(total) + n', method: 'credit'})
  if (b.kind !== 'step') throw Error('expected a step law')
  expect(proveSteps(x.rule!, x.invariants ?? [], [b.law], {search: false})).toMatchObject({
    proven: false, checked: false, translation: 'unchecked',
    why: 'source translation unchecked: source replay or native-law cross-check was disabled',
  })
})
