// Source-generation controls only. This file never launches Lean and makes no
// claim that a generated certificate has been checked by the Lean kernel.
import {expect, test} from 'bun:test'
import {readFileSync} from 'node:fs'
import {toLean, leanProject, cycMachineToLean} from './emit.ts'
import {asked} from './axiom-audit.ts'
import {actualFixture, auditGenericWordGate, digitFixture, forgedArithmeticFixture, gateOptions,
  generateGenericWordGate, genericWordFixtures, invalidTupleFixtures, reconstructionFixture, reservedDeclarationFixtures} from '../research/kernel-primitives/generic-lean-gate.ts'

let cached: ReturnType<typeof generateGenericWordGate> | undefined
const generated = () => cached ??= generateGenericWordGate()

// Test the actual public machine + Law entry point, never the restricted helper.
test('generic public toLean exports every q/r/c digit at widths 8,16,32,64', () => {
  const result = generated()
  let digits = 0
  for (const width of [8, 16, 32, 64] as const) for (const part of ['q', 'r', 'c'] as const) {
    const f = digitFixture(width, part), count = width === 8 ? 1 : width / 16
    expect(f.laws).toHaveLength(part === 'c' ? 2 * count : count)
    digits += f.laws.length
    expect(result.source).toContain(`def ${f.id}_word : Kern.WordReach.WordSMachine`)
    expect(result.source).toContain(`WordSReach ${f.id}_word`)
    expect(result.source).toContain(`theorem ${f.id}_laws`)
    for (let i = 0; i < f.laws.length; i++) expect(result.claims).toContain(`${f.id}.law${i}`)
  }
  expect(digits).toBe(32)
  expect(result.claims).toContain('Kern.WordSMachine.concrete_smachine_sound')
  for (const f of result.fixtures.filter(f => f.intrinsic)) expect(result.claims).toContain(`${f.id}_word_extra_sound`)
  expect(result.source).not.toContain('native_decide')
  expect(result.source).not.toMatch(/\bsorry\b|^axiom /m)
}, 120_000)

test('irrelevant intrinsic updates retain their source maps and complete helper namespace', () => {
  const fixture = digitFixture(64, 'q')
  fixture.machine.state.kept = {op: 'const', value: 0}
  const source = toLean([{...fixture, laws: [{name: 'kept is framed', holds: {op: '=', a: {op: 'var', name: 'kept'}, b: {op: 'const', value: 0}}}]}], gateOptions)
  expect(source).toContain('worddiv$64$q$0')
  expect(source).toContain('worddiv$64$c$8')
  expect(source).toContain(`def ${fixture.id}_word : Kern.WordReach.WordSMachine`)
})

test('direct cyclic export refuses intrinsic reads confined to a step claim', () => {
  const fixture = digitFixture(8, 'q')
  const native = fixture.machine.step.state!.digit0!
  const machine = {...fixture.machine, step: {state: {digit0: {op: 'const' as const, value: 0}}}}
  const out = cycMachineToLean('claim_only_word', machine, fixture.laws, {
    stepLaws: [{name: 'native claim', then: {op: '<', a: native, b: {op: 'const', value: 256}}}],
  })
  expect(out).toEqual({why: 'word primitives require the concrete SMachine export route'})
})

test('generic gate uses no restricted scalar exporters and preserves its inputs', () => {
  const file = readFileSync(new URL('../research/kernel-primitives/generic-lean-gate.ts', import.meta.url), 'utf8')
  expect(file).not.toContain('wordDigitRangeMachineToLean')
  expect(file).not.toContain('q8RangeMachineToLean')
  const fixture = digitFixture(8, 'q'), before = JSON.stringify(fixture)
  const text = toLean([{id: fixture.id, machine: fixture.machine, laws: fixture.laws}], gateOptions)
  expect(JSON.stringify(fixture)).toBe(before)
  expect(text).toContain(`theorem ${fixture.id}_laws`)
})

test('real DSL wrap carries transparent mod$256 definitions and ordinary arithmetic facts', () => {
  const wrap = actualFixture('wrap'), mixed = actualFixture('wrap_word')
  expect(wrap.machine.fns?.['mod$256']?.lean).toBe('fun x => x % 256')
  expect(wrap.machine.fns?.['div$256']?.lean).toBe('fun x => x / 256')
  expect(wrap.machine.facts?.length).toBeGreaterThanOrEqual(2)
  expect(mixed.machine.fns?.['mod$256']?.lean).toBe('fun x => x % 256')
  expect(mixed.machine.primitiveFailure).toBeDefined()
  const source = generated().source
  expect(source).toContain('generic_actual_wrap_machine')
  expect(source).not.toContain('def generic_actual_wrap_word :')
  expect(source).toContain('def generic_actual_wrap_word_word : Kern.WordReach.WordSMachine')
  expect(source).toContain('generic_actual_division_word')
  expect(source).toContain('(Kern.cpair (ρ «operand0»)')
  expect(source).not.toContain('(Kern.cpair ρ ')
  // Actual divideFixed returns are conditional rollback updates, not an
  // assumption excluding failure. We intentionally prove no exception theorem.
  expect(JSON.stringify(actualFixture('division').machine.step.state)).toContain('"op":"if"')
})

test('mixed mutable maps, carried/frame inputs, and a quantified ordinary map law remain genuine machine laws', () => {
  const result = generated()
  for (const id of ['generic_mixed_map', 'generic_carried_frame', 'generic_quantified_map']) {
    const fixture = result.fixtures.find(f => f.id === id)!
    expect(fixture).toBeDefined()
    expect(result.source).toContain(`def ${id}_word : Kern.WordReach.WordSMachine`)
    for (let i = 0; i < fixture.laws.length; i++) expect(result.claims).toContain(`${id}.law${i}`)
  }
  expect(result.fixtures.find(f => f.id === 'generic_mixed_map')!.machine.step.maps).toHaveProperty('cells')
  expect(result.fixtures.find(f => f.id === 'generic_carried_frame')!.machine.inputMaps).toEqual(['request'])
  expect(result.fixtures.find(f => f.id === 'generic_quantified_map')!.laws[0]!.forall).toBe('j')
})

test('positive guarded u8 reconstruction and all eight u64 arithmetic columns use the generic public bridge', () => {
  const result = generated()
  for (const width of [8, 64] as const) {
    const fixture = reconstructionFixture(width)
    expect(fixture.laws).toHaveLength(width === 8 ? 1 : 8)
    expect(fixture.machine.pre).toBeDefined()
    expect(JSON.stringify(fixture.machine.step.state)).toContain('"op":"prod"')
    expect(result.source).toContain(`def ${fixture.id}_word : Kern.WordReach.WordSMachine`)
    expect(result.claims).toContain(`${fixture.id}_word_extra_sound`)
    for (let i = 0; i < fixture.laws.length; i++) expect(result.claims).toContain(`${fixture.id}.law${i}`)
  }
})

test('leanProject ships the complete generic intrinsic proof modules as source', () => {
  const project = leanProject(generated().source)
  for (const name of ['WordDivision.lean', 'WordDivisionBridge.lean', 'WordFacts.lean', 'WordReach.lean', 'WordSMachine.lean']) {
    expect(project[name]).toBeDefined()
    expect(project[name]).not.toMatch(/\bsorry\b|^axiom /m)
  }
  expect(project['Proofs.lean']).toBe(generated().source)
  expect(project['WordReach.lean']).toContain('WordSReach')
})

test('reserved quotient/remainder/carry declarations and point/bulk writes fail closed', () => {
  for (const f of reservedDeclarationFixtures()) {
    expect(() => toLean([{id: 'reserved_shadow', machine: f.machine, laws: f.laws}], gateOptions)).toThrow()
  }
})

test('malformed word operand tuples fail closed rather than becoming opaque ordinary reads', () => {
  for (const f of invalidTupleFixtures()) {
    expect(() => toLean([{id: f.id, machine: f.machine, laws: f.laws}], gateOptions)).toThrow(/tuple|arity|invalid/i)
  }
})

test('a forged shifted Euclidean arithmetic identity is not exported', () => {
  const f = forgedArithmeticFixture()
  expect(() => toLean([{id: f.id, machine: f.machine, laws: f.laws}], gateOptions)).toThrow()
}, 30_000)

test('audit coverage is derived from exact generated source and rejects source/log tampering', () => {
  const {source, claims} = generated()
  expect(claims).toEqual(asked(source))
  expect(new Set(claims).size).toBe(claims.length)
  const synthetic = claims.map(name => `'${name}' does not depend on any axioms`).join('\n')
  // Parser-only controls, NOT evidence of a Lean execution.
  expect(auditGenericWordGate(source, synthetic).checked).toBe(claims.length)
  expect(() => auditGenericWordGate(source + '-- changed\n', synthetic)).toThrow('source mismatch')
  expect(() => auditGenericWordGate(source, synthetic.split('\n').slice(1).join('\n'))).toThrow()
  expect(() => auditGenericWordGate(source, synthetic.replace('does not depend on any axioms', 'depends on axioms: [Lean.ofReduceBool]'))).toThrow()
  expect(() => auditGenericWordGate(source, synthetic + '\n' + synthetic.split('\n')[0])).toThrow()
}, 120_000)

test('one-step and k-step claims use the concrete-word frame theorem', () => {
  const {source, claims} = generated()
  expect(source).toContain('Kern.WordSMachine.WordSKStepHolds generic_word_steps_word')
  expect(source).toContain('Kern.WordSMachine.word_skstep_sound generic_word_steps_word')
  expect(source).toContain('generic_claim_only_word_word : Kern.WordReach.WordSMachine')
  expect(claims).toContain('generic_word_steps_step0_holds')
  expect(claims).toContain('generic_word_steps_step1_holds')
  expect(claims).toContain('generic_claim_only_word_step0_holds')
  expect(claims).toContain('generic_arbitrary_map_counterexample')
  expect(claims).toContain('generic_reserved_frame_tamper_rejected')
})

test('gate selection covers actual public fixtures and does not silently rename old packaged gates', () => {
  const fixtures = genericWordFixtures()
  expect(fixtures).toHaveLength(22)
  expect(new Set(fixtures.map(f => f.id)).size).toBe(fixtures.length)
  const one = generateGenericWordGate(['generic_q8'])
  expect(one.fixtures.map(f => f.id)).toEqual(['generic_q8'])
  expect(one.claims).toContain('generic_q8_laws')
  expect(() => generateGenericWordGate(['missing'])).toThrow('unknown generic fixture')
})
