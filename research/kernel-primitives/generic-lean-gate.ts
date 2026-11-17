// Generic acceptance gate: ONLY the public toLean(machine + Law) entry point.
// The older lean-machine-gate.ts / packaged21 gate remain independent controls.
// Source generation is not Lean verification. Run --audit only after compiling
// this exact source with leanProject's shipped dependency closure.
import {createHash} from 'node:crypto'
import {readFileSync, writeFileSync} from 'node:fs'
import {fixedInt, rule} from '../../core/dsl.ts'
import type {C, E, Law, Machine} from '../../core/machine.ts'
import type {StepLaw} from '../../kernel/kernel.ts'
import {wordDivisionKey, wordDivisionName, type WordDivisionSpec} from '../../kernel/word-division.ts'
import {toLean, type LeanItem} from '../../lean-kernel/emit.ts'
import {asked, auditLiftLog} from '../../lean-kernel/axiom-audit.ts'

const n = (value: number): E => ({op: 'const', value})
const v = (name: string): E => ({op: 'var', name})
const get = (map: string, key: E): E => ({op: 'get', map, key})
const lt = (a: E, bound: number): C => ({op: '<', a, b: n(bound)})
const eq = (a: E, b: E): C => ({op: '=', a, b})
const and = (...xs: C[]): C => ({op: 'and', xs})
export type GenericWordFixture = {id: string, machine: Machine, laws: Law[], stepLaws?: StepLaw[], intrinsic: boolean, scope: string}
export const gateOptions = {native: false, cyclic: false} as const

/** All 32 valid q/r/c digits, not merely a representative at each width. */
export function digitFixture(width: WordDivisionSpec['width'], part: WordDivisionSpec['part']): GenericWordFixture {
  const count = width === 8 ? 1 : width / 16, radix = width === 8 ? 256 : 65536
  const inputs = Array.from({length: 2 * count}, (_, i) => `limb${i}`)
  const key = wordDivisionKey(inputs.map(v)), indices = Array.from({length: part === 'c' ? 2 * count : count}, (_, i) => i + (part === 'c' ? 1 : 0))
  const id = `generic_${part}${width}`
  const state = Object.fromEntries(indices.map(i => [`digit${i}`, n(0)]))
  const updated = Object.fromEntries(indices.map(i => [`digit${i}`, get(wordDivisionName(width, part, i), key)]))
  const laws: Law[] = indices.map(i => ({name: `${part}${width} digit ${i} range`, holds: part === 'c'
    ? {op: '<=', a: v(`digit${i}`), b: n(count * radix)} : lt(v(`digit${i}`), radix)}))
  return {id, machine: {name: id, params: [], inputs, state, step: {state: updated}}, laws, intrinsic: true,
    scope: 'all reachable states; total intrinsic helpers, including zero and unbounded operands'}
}

/** A real fixedInt DSL rule includes the arithmetic function definitions/facts.
 * A hand-assembled fixedInt expression alone does NOT carry mod$256 semantics.
 * Division's primitiveFailure is already a rollback conditional in the step;
 * these laws concern totalized state transitions, NOT runtime exception behavior.
 */
export function actualFixture(kind: 'wrap' | 'division' | 'wrap_word'): GenericWordFixture {
  const k = fixedInt(8, false), id = `generic_actual_${kind}`
  if (kind === 'wrap') {
    const r = rule(id).inputs({a: k, b: k}).state({out: k.from(0)})
      .step(({a, b}) => ({out: a.plus(b, 'WRAP')}))
    return {id, machine: r.machine, laws: [{name: 'actual wrapped output is u8', holds: lt(v('out$0'), 256)}], intrinsic: false,
      scope: 'actual DSL wrap; ordinary mod$256/div$256 definitions and their proven facts'}
  }
  if (kind === 'division') {
    const r = rule(id).inputs({a: k, b: k}).state({quotient: k.from(0), remainder: k.from(0)})
      .step(({a, b}) => ({quotient: a.div(b, 'EUCLIDEAN', 'TRAP'), remainder: a.rem(b, 'EUCLIDEAN', 'TRAP')}))
    return {id, machine: r.machine, laws: ['quotient', 'remainder'].map(name => ({name: `actual ${name} is u8`, holds: lt(v(`${name}$0`), 256)})), intrinsic: true,
      scope: 'actual divideFixed DSL step including failure rollback; no runtime exception theorem'}
  }
  const r = rule(id).inputs({a: k, b: k}).state({out: k.from(0), quotient: k.from(0), remainder: k.from(0)})
    .step(({a, b}) => ({out: a.plus(b, 'WRAP'), quotient: a.div(b, 'EUCLIDEAN', 'TRAP'), remainder: a.rem(b, 'EUCLIDEAN', 'TRAP')}))
  return {id, machine: r.machine, laws: ['out', 'quotient', 'remainder'].map(name => ({name: `actual mixed ${name} is u8`, holds: lt(v(`${name}$0`), 256)})), intrinsic: true,
    scope: 'actual wrap and divideFixed in one DSL step, ordinary arithmetic facts through intrinsic bridge; no runtime exception theorem'}
}

export function ordinaryMapFixtures(): GenericWordFixture[] {
  const key = wordDivisionKey([v('a'), v('b')]), quotient = get(wordDivisionName(8, 'q', 0), key)
  const common: Machine = {name: 'mixed maps', params: [], inputs: ['a', 'b', 'key'], state: {out: n(0), marker: n(7)},
    maps: {cells: 0, frame: 9}, step: {flags: {enabled: {op: '<=', a: n(0), b: v('key')}},
      state: {out: {op: 'if', c: {op: 'flag', name: 'enabled'}, then: quotient, else: v('out')}},
      maps: {cells: {key: v('key'), value: quotient}}}}
  const mixed: GenericWordFixture = {id: 'generic_mixed_map', machine: common, intrinsic: true,
    laws: [{name: 'quotient beside mutable ordinary map', holds: lt(v('out'), 256)},
      {name: 'omitted scalar is framed', holds: eq(v('marker'), n(7))}], scope: 'mutable ordinary map and flags retained beside intrinsic read'}
  const carried: Machine = {name: 'carried and framed maps', params: ['limit'], inputs: ['b', 'key'],
    pre: {op: '<=', a: n(1), b: v('limit')}, assume: lt(v('b'), 256), inputMaps: ['request'],
    state: {out: n(0), marker: n(7)}, maps: {frame: 9}, step: {state: {out: get(wordDivisionName(8, 'q', 0),
      wordDivisionKey([get('request', v('key')), v('b')]))}}}
  const frame: GenericWordFixture = {id: 'generic_carried_frame', machine: carried, intrinsic: true,
    laws: [{name: 'quotient of carried input is a digit', holds: lt(v('out'), 256)},
      {name: 'ordinary frame input is preserved', forall: 'j', holds: eq(get('frame', v('j')), n(9))}],
    scope: 'whole request-carried map, frame map, params, precondition and request assumption'}
  const quantified: GenericWordFixture = {id: 'generic_quantified_map', machine: {...common, name: 'quantified mutable cells'}, intrinsic: true,
    laws: [{name: 'every written ordinary cell remains a digit', forall: 'j', holds: lt(get('cells', v('j')), 256)}],
    scope: 'unbounded quantified invariant over a mutable ordinary map, not bounded key sampling'}
  return [mixed, frame, quantified]
}

/** The same machine certificate proves claims in one and several request frames.
 * Carried-map frame targets are fresh and cannot shadow native helper IDs. */
export function stepFixtures(): GenericWordFixture[] {
  const carried = ordinaryMapFixtures()[1]!
  const framed: GenericWordFixture = {...carried, id: 'generic_word_steps', stepLaws: [1, 2].map(steps => ({
    name: `word output after ${steps} frames`, steps, then: lt(v("out'"), 256),
  })), scope: 'one/k-step claims over arbitrary carried requests, exact WordSKStepHolds with reserved-target guard'}
  const helper = get(wordDivisionName(8, 'q', 0), wordDivisionKey([v('a'), v('b')]))
  const claimsOnly: GenericWordFixture = {id: 'generic_claim_only_word', intrinsic: true,
    machine: {name: 'words only in a claim', params: [], inputs: ['a', 'b'], state: {out: n(0)}, step: {state: {out: n(0)}}},
    laws: [{name: 'ordinary state is zero', holds: eq(v('out'), n(0))}],
    stepLaws: [{name: 'native claim is a digit', then: lt(helper, 256)}],
    scope: 'word reads confined to a step claim still select concrete world, never the arbitrary-map route'}
  return [framed, claimsOnly]
}

export function genericWordFixtures(): GenericWordFixture[] {
  return [...([8, 16, 32, 64] as const).flatMap(width => (['q', 'r', 'c'] as const).map(part => digitFixture(width, part))),
    actualFixture('wrap'), actualFixture('division'), actualFixture('wrap_word'), ...ordinaryMapFixtures(),
    reconstructionFixture(8), reconstructionFixture(64), ...stepFixtures()]
}

/** Positive guarded arithmetic, not only digit ranges. u8 uses the full
 * Euclidean reconstruction. u64 uses every schoolbook column, avoiding any
 * unsafe Number encoding of a 64-bit weighted product. Neither is a bounded
 * operand sample: immutable parameters range over every valid operand tuple.
 */
export function reconstructionFixture(width: 8 | 64): GenericWordFixture {
  const count = width === 8 ? 1 : 4, radix = width === 8 ? 256 : 65536
  const params = Array.from({length: 2 * count}, (_, i) => `operand${i}`), args = params.map(v)
  const key = wordDivisionKey(args), a = args.slice(0, count), b = args.slice(count)
  const digit = (part: 'q' | 'r' | 'c', index: number): E => get(wordDivisionName(width, part, index), key)
  const add = (xs: E[]): E => xs.reduce<E>((x, y) => ({op: 'add', a: x, b: y}), n(0))
  const pre = and(...args.map(x => lt(x, radix)), {op: 'or', xs: b.map(x => ({op: '<', a: n(0), b: x}))})
  const id = `generic_reconstruct${width}`
  if (width === 8) return {id, intrinsic: true, scope: 'all bounded nonzero operands: quotient*b+remainder=a; uses guarded reconstruction and low-carry-zero facts',
    machine: {name: id, params, inputs: [], pre, state: {out: a[0]!}, step: {state: {out: add([
      {op: 'prod', a: digit('q', 0), b: b[0]!}, digit('r', 0)])}}},
    laws: [{name: 'full u8 Euclidean reconstruction', holds: eq(v('out'), a[0]!)}]}
  const rhs = (i: number): E => add([i < count ? a[i]! : n(0), {op: 'mul', k: radix, a: digit('c', i + 1)}])
  const lhs = (i: number): E => add([i === 0 ? n(0) : digit('c', i), ...(i < count ? [digit('r', i)] : []),
    ...Array.from({length: count}, (_, j) => j).filter(j => i >= j && i - j < count)
      .map((j): E => ({op: 'prod', a: digit('q', j), b: b[i - j]!}))])
  const indices = Array.from({length: 2 * count}, (_, i) => i)
  return {id, intrinsic: true, scope: 'all bounded nonzero u64 operands: all eight exact Q*B+R=A schoolbook columns, including carry; no raw Number-sized u64 product',
    machine: {name: id, params, inputs: [], pre, state: Object.fromEntries(indices.map(i => [`column${i}`, rhs(i)])),
      step: {state: Object.fromEntries(indices.map(i => [`column${i}`, lhs(i)]))}},
    laws: indices.map(i => ({name: `u64 reconstruction column ${i}`, holds: eq(v(`column${i}`), rhs(i))}))}
}

/** A false Euclidean identity, with a concrete counterexample a=7,b=3:
 * q*b+r=7, not 8. Both helper semantics and the valid operand domain are present.
 */
export function forgedArithmeticFixture(): GenericWordFixture {
  const key = wordDivisionKey([v('a'), v('b')]), q = get(wordDivisionName(8, 'q', 0), key), r = get(wordDivisionName(8, 'r', 0), key)
  return {id: 'forged_arithmetic_identity', intrinsic: true, scope: 'negative control, must not export',
    machine: {name: 'forged arithmetic identity', params: ['a', 'b'], inputs: [], state: {out: q}, step: {state: {out: q}},
      pre: and(lt(v('a'), 256), lt(v('b'), 256), {op: '<', a: n(0), b: v('b')})},
    laws: [{name: 'forged shifted Euclidean identity', holds: eq({op: 'add', a: {op: 'prod', a: q, b: v('b')}, b: r}, {op: 'add', a: v('a'), b: n(1)})}]}
}

/** Invalid reserved declarations must fail even when they are unused. */
export function reservedDeclarationFixtures(): {name: string, machine: Machine, laws: Law[]}[] {
  const base = digitFixture(8, 'q'), out: {name: string, machine: Machine, laws: Law[]}[] = []
  for (const part of ['q', 'r', 'c'] as const) {
    const map = wordDivisionName(8, part, part === 'c' ? 1 : 0)
    out.push({name: `${part} state map`, machine: {...base.machine, maps: {[map]: 0}}, laws: base.laws},
      {name: `${part} carried map`, machine: {...base.machine, inputMaps: [map]}, laws: base.laws},
      {name: `${part} function`, machine: {...base.machine, fns: {[map]: {js: 'x => 0', lean: 'fun _ => 0'}}}, laws: base.laws},
      {name: `${part} point write`, machine: {...base.machine, step: {...base.machine.step, maps: {[map]: {key: n(0), value: n(0)}}}}, laws: base.laws},
      {name: `${part} bulk write`, machine: {...base.machine, step: {...base.machine.step, maps: {[map]: {each: 'j', value: n(0)}}}}, laws: base.laws})
  }
  return out
}

export function invalidTupleFixtures(): GenericWordFixture[] {
  const base = digitFixture(64, 'q')
  return [n(0), {op: 'tup', a: n(0), b: n(0)} as E,
    wordDivisionKey(Array.from({length: 9}, () => n(0)))].map((key, i) => ({...base, id: `invalid_tuple_${i}`,
      machine: {...base.machine, step: {state: {...base.machine.step.state, digit0: get(wordDivisionName(64, 'q', 0), key)}}}}))
}

export function generateGenericWordGate(ids?: readonly string[]): {source: string, claims: string[], fixtures: GenericWordFixture[]} {
  const all = genericWordFixtures(), fixtures = ids ? ids.map(id => {
    const fixture = all.find(x => x.id === id)
    if (!fixture) throw Error(`unknown generic fixture ${id}`)
    return fixture
  }) : all
  if (!fixtures.length || new Set(fixtures.map(f => f.id)).size !== fixtures.length) throw Error('empty or duplicate fixture selection')
  const binding = createHash('sha256').update(JSON.stringify(fixtures)).digest('hex')
  const items: LeanItem[] = fixtures.map(({id, machine, laws, stepLaws}) => ({id, machine, laws, ...(stepLaws ? {stepLaws} : {})}))
  const generated = toLean(items, gateOptions)
  const required = fixtures.flatMap(f => [`${f.id}_laws`, ...f.laws.map((_, i) => `${f.id}.law${i}`), ...(f.stepLaws ?? []).map((_, i) => `${f.id}_step${i}_holds`),
    ...(f.intrinsic ? [`${f.id}_word_extra_sound`] : [])])
  if (fixtures.some(f => f.intrinsic)) required.push('Kern.WordSMachine.concrete_smachine_sound')
  if (fixtures.some(f => f.stepLaws?.length)) required.push('Kern.WordSMachine.word_skstep_sound')
  // Negative Lean controls use the actual exported descriptors/checker. They
  // establish that arbitrary maps do not supply the helper facts and that a
  // frame rename cannot redirect a carried map into the reserved namespace.
  const controls: string[] = []
  if (fixtures.some(f => f.id === 'generic_q8')) {
    controls.push(`theorem generic_arbitrary_map_counterexample :
    Kern.evalC (fun _ => 0) (fun _ _ => 300)
      (.lt (WordFacts.Spec.q generic_q8_word_spec0 0) (.const 256)) = false := by decide +kernel`)
    required.push('generic_arbitrary_map_counterexample')
  }
  if (fixtures.some(f => f.id === 'generic_word_steps')) {
    controls.push(`def generic_reserved_frame_tampered : Kern.SKStep :=
  {generic_word_steps_step1 with mren := [[], [(generic_word_steps_machine.carried.head?.getD 0,
    generic_word_steps_word_spec0.qMaps.head?.getD 0)]]}
theorem generic_reserved_frame_tamper_rejected :
    Kern.WordSMachine.checkSKStepWithFacts generic_word_steps_word generic_word_steps_proof
      generic_reserved_frame_tampered generic_word_steps_word_extra = false := by decide +kernel`)
    required.push('generic_reserved_frame_tamper_rejected')
  }
  const printed = new Set(asked(generated))
  const source = `-- Generic public toLean acceptance; exact machine/Law SHA256 ${binding}\n${generated}\n${controls.join('\n\n')}\n` +
    required.filter(name => !printed.has(name)).map(name => `#print axioms ${name}`).join('\n') + '\n'
  const claims = asked(source)
  if (new Set(claims).size !== claims.length || required.some(name => !claims.includes(name))) throw Error('generated claim coverage mismatch')
  return {source, claims, fixtures}
}

export function auditGenericWordGate(source: string, log: string, ids?: readonly string[]) {
  const expected = generateGenericWordGate(ids)
  if (source !== expected.source) throw Error('generated source mismatch: audit must bind to actual current machine/Law input')
  const rows = auditLiftLog(log, [source], expected.claims)
  return {checked: rows.length, strictStandardAxioms: true, publicToLean: true,
    fixtures: expected.fixtures.map(({id, laws, scope}) => ({id, laws: laws.length, scope})),
    runtimeExceptionBehaviorProven: false,
    priorGates: 'separate, unchanged; this result does not implicitly rerun packaged21'}
}

if (import.meta.main) {
  const args = process.argv.slice(2), caseAt = args.indexOf('--case')
  let ids: string[] | undefined
  if (caseAt >= 0) {
    if (caseAt + 2 !== args.length) throw Error('--case must be the final argument, followed by one fixture id')
    ids = [args[caseAt + 1]!]; args.splice(caseAt)
  }
  if (args.length === 1 && args[0] !== '--audit') {
    const result = generateGenericWordGate(ids)
    writeFileSync(args[0]!, result.source)
    console.log(JSON.stringify({output: args[0], claims: result.claims, fixtures: result.fixtures.map(f => f.id),
      note: 'unverified generated source; compile exact packaged project and audit complete target Lean log'}))
  } else if (args.length === 3 && args[0] === '--audit') {
    console.log(JSON.stringify(auditGenericWordGate(readFileSync(args[1]!, 'utf8'), readFileSync(args[2]!, 'utf8'), ids)))
  } else throw Error('usage: generic-lean-gate.ts OUTPUT [--case ID] | --audit OUTPUT LOG [--case ID]')
}
