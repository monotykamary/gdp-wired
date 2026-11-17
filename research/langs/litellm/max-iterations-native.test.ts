// Explicit native integration suite, deliberately outside ordinary core shards.
// Missing prerequisites FAIL, never skip. Run only in the dedicated native job (README.md).
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {writeFileSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {extractPython} from '../../../core/extract-py.ts'
import {buildLaw} from '../../../core/laws.ts'
import {proveSteps} from '../../../core/dsl.ts'
import {PIN, SPECS} from './specs.ts'

const required = (key: string) => {
  const value = process.env[key]
  if (!value) throw new Error(`native LiteLLM integration requires ${key}; see research/langs/litellm/README.md`)
  return value
}

test('pinned LiteLLM MaxIterations: four registered laws, sampled native admission, and refused controls', () => {
  const src = resolve(required('LITELLM_SRC')), python = required('LITELLM_PYTHON')
  // No fixture rewrites the handler, decorator, or cache code. The extractor supplies only the stated boundary.
  expect(execFileSync('git', ['-C', src, 'rev-parse', 'HEAD'], {encoding: 'utf8'}).trim()).toBe(PIN.commit)
  execFileSync('git', ['-C', src, 'diff', '--exit-code', 'HEAD', '--', 'litellm'], {stdio: 'pipe'})
  const spec = SPECS.find(s => s.id === 'rate limit/litellm-py/MaxIterationsHandler')!
  const x = extractPython(join(src, spec.file), {...spec.opts, root: src, python})
  expect(x.ok).toBe(true)
  expect(x.refusals).toEqual([])
  expect(x.evidence?.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(0)
  expect(spec.laws).toHaveLength(4)
  for (const key of ['_get_session_id', '_get_max_iterations']) {
    expect(x.names?.find(n => n.code === key && n.role === 'answer')?.native).toEqual({kind: 'answer', key})
  }
  expect(x.names?.find(n => n.code === 'internal_usage_cache')?.map?.tpl).toBe('{session_iterations:{}}:count')
  // Repairing runtime metadata does not give an old DSL callback a registered source meaning.
  for (const l of spec.laws) {
    const legacy = proveSteps(x.rule!, x.invariants ?? [], [l.law(x.rule as never)], {search: false})
    expect(legacy).toMatchObject({proven: false, checked: false, translation: 'unchecked'})
    expect(legacy.why).toContain('a source proof contains a law with no native interpretation')
  }
  const built = spec.laws.map(l => {
    expect(l.expr).toBeDefined()
    const b = buildLaw(x, {name: l.name, expr: l.expr!, method: 'async_pre_call_hook'})
    if (b.kind !== 'step') throw new Error(`expected step law: ${l.name}`)
    return b.law
  })
  const laws = []
  for (const [i, law] of built.entries()) {
    // Public proof API must repeat native-law admission. A checked kernel model alone is insufficient.
    const v = proveSteps(x.rule!, x.invariants ?? [], [law], {search: false})
    expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
    expect(v.translationChecks).toBeGreaterThan(0)
    laws.push({name: spec.laws[i]!.name, proven: v.proven, checked: v.checked, translation: v.translation, translationChecks: v.translationChecks})
  }
  const broken = () => {
    const b = buildLaw(x, {
      name: 'control: every limited call leaves its count at ZERO (false)', method: 'async_pre_call_hook',
      expr: '_get_session_id(...) is not None and _get_max_iterations(...) is not None implies internal_usage_cache[`{session_iterations:${_get_session_id(...)}}:count`] == 0',
    })
    if (b.kind !== 'step') throw new Error('expected step control law')
    return b.law
  }
  const refused = proveSteps(x.rule!, x.invariants ?? [], [broken()], {search: false})
  expect(refused.proven).toBe(false)
  expect(refused.stuck).toBe('sat')
  // Also require the independent native interpretation to catch a falsely lowered symbolic predicate.
  // The immutable registered text remains false; this mutation cannot supply a native evaluator.
  const mistranslated = broken()
  mistranslated.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const nativeRefusal = proveSteps(x.rule!, x.invariants ?? [], [mistranslated], {search: false})
  expect(nativeRefusal).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error', stuck: 'translation-error'})
  expect(nativeRefusal.translationChecks).toBeGreaterThan(0)
  const witness = nativeRefusal.translationWitness!
  expect(witness.observed?.calls._get_session_id?.kind).toBe('returned')
  expect(witness.observed?.calls._get_max_iterations?.kind).toBe('returned')
  expect(witness.before).toHaveProperty('internal_usage_cache')
  expect(witness.after).toHaveProperty('internal_usage_cache')
  if (process.env.GDP_LITELLM_RESULT) writeFileSync(process.env.GDP_LITELLM_RESULT, `${JSON.stringify({
    pin: PIN, src, python, laws,
    controls: {symbolic: {proven: refused.proven, stuck: refused.stuck}, native: {proven: nativeRefusal.proven, checked: nativeRefusal.checked, translation: nativeRefusal.translation, translationChecks: nativeRefusal.translationChecks, stuck: nativeRefusal.stuck}},
  }, null, 2)}\n`)
}, 180_000)
