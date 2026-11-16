import {expect, test} from 'bun:test'
import {mkdtempSync, writeFileSync, rmSync} from 'node:fs'
import {execFileSync} from 'node:child_process'
import {tmpdir} from 'node:os'
import {extractJava} from './extract-jvm.ts'
import {buildLaw} from './laws.ts'
import {proveSteps} from './dsl.ts'

const code = `public class Counter {
  private int total = 0;
  public int credit(int n) { total += n; n += 1; return n; }
}`
const read = (prebuilt = false, source = code, disabled = false) => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-jvm-native-`)
  try {
    const file = `${dir}/Counter.java`
    writeFileSync(file, source)
    if (prebuilt) execFileSync(process.env.JAVA_HOME ? `${process.env.JAVA_HOME}/bin/javac` : 'javac', ['-d', dir, file])
    const x = extractJava(file, {entry: 'Counter', ...(prebuilt ? {prebuilt: true, classpath: [dir]} : {}), check: disabled ? {runs: 0, states: 0, probes: false} : {runs: 8, depth: 3, states: 0, probes: false}})
    expect(x.ok).toBe(true)
    expect(x.evidence?.mismatch).toBeUndefined()
    return x
  } finally { rmSync(dir, {recursive: true, force: true}) }
}
const law = (x: ReturnType<typeof read>, expr: string) => {
  const b = buildLaw(x, {name: 'credit', expr, method: 'credit'})
  if (b.kind !== 'step') throw Error('expected a step law')
  return b.law
}

test('JVM native bindings capture converted scalar arguments before local reassignment', () => {
  const x = read(), b = law(x, 'n < 2147483647 implies result == n + 1')
  const v = proveSteps(x.rule!, x.invariants ?? [], [b], {search: false})
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
})

test('JVM native state uses source fields even when constructor parameters share their names', () => {
  const x = read(false, `public class Counter {
    private long total;
    public Counter(long total) { this.total = total; }
    public void credit(int n) { total += n; }
  }`)
  const b = law(x, 'total == old(total) + n')
  const v = proveSteps(x.rule!, x.invariants ?? [], [b], {search: false})
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
  const faulty = law(x, 'total == old(total) + n + 1')
  faulty.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const rejected = proveSteps(x.rule!, x.invariants ?? [], [faulty], {search: false})
  expect(rejected).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error', stuck: 'translation-error'})
  expect(rejected.translationWitness?.before).toHaveProperty('total')
  expect(rejected.translationWitness?.after).toHaveProperty('total')
})

test('JVM native bindings reject a falsely lowered law using real callable arguments', () => {
  const x = read(), b = law(x, 'result == n + 2')
  b.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const v = proveSteps(x.rule!, x.invariants ?? [], [b], {search: false})
  expect(v).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error', stuck: 'translation-error'})
  expect(v.why).toContain('translation error: credit is false in the native code')
  expect(v.translationWitness?.bindings).toHaveProperty('n')
})

test('JVM native observations cannot replace disabled source replay', () => {
  const x = read(false, code, true), b = law(x, 'n < 2147483647 implies result == n + 1')
  expect(proveSteps(x.rule!, x.invariants ?? [], [b], {search: false})).toMatchObject({
    proven: false, checked: false, kernelProven: true, translation: 'unchecked',
    why: 'source translation unchecked: source replay or native-law cross-check was disabled',
  })
})

test('JVM prebuilt bytecode without parameter names refuses source-law admission', () => {
  const x = read(true), b = law(x, 'n < 2147483647 implies result == n + 1')
  const v = proveSteps(x.rule!, x.invariants ?? [], [b], {search: false})
  expect(v).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'unchecked'})
  expect(v.why).toBe('source translation unchecked: native observation unavailable: native parameter capture: IllegalArgumentException: native parameter name unavailable: credit')
})
