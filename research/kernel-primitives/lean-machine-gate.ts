// Closed machine-transition recheck, not a universal machine-law certificate.
// Lean evaluates the actual lowered core E under transparent map interpretations.
// Usage: bun research/kernel-primitives/lean-machine-gate.ts OUTPUT
//        bun research/kernel-primitives/lean-machine-gate.ts --audit OUTPUT LOG
import {readFileSync, writeFileSync} from 'node:fs'
import {fixedInt} from '../../core/fixed-integers.ts'
import {wordDivisionKey, wordDivisionName} from '../../kernel/word-division.ts'
import {wordReads, wordMapOverlayLean} from '../../lean-kernel/word-division-export.ts'
import {encode, q8RangeMachineToLean, wordDigitRangeMachineToLean} from '../../lean-kernel/emit.ts'
import {grow} from '../../kernel/prove.ts'
import {check, type Goal, type Tree} from '../../kernel/kernel.ts'
import {leanTerms} from '../../lean-kernel/lean-terms.ts'
import {auditLiftLog} from '../../lean-kernel/axiom-audit.ts'
import type {C, E, Machine} from '../../core/machine.ts'

const c = (value: number): E => ({op: 'const', value})
const v = (name: string): E => ({op: 'var', name})
const u8 = fixedInt(8, false)
const a = u8.value('a'), b = u8.value('b')
const wrap: Machine = {name: 'actual_u8_wrap', params: [], inputs: ['a$0', 'b$0'],
  state: {'out$0': c(0)}, step: {state: {'out$0': a.plus(b, 'WRAP').limbs[0]!.e}}}
const division: Machine = {name: 'actual_u8_division', params: [], inputs: ['a$0', 'b$0'],
  state: {'out$0': c(0)}, step: {state: {'out$0': {op: 'get', map: wordDivisionName(8, 'q', 0),
    key: wordDivisionKey([v('a$0'), v('b$0')])}}}}
// Negative controls: the restricted full-machine lane cannot silently reinterpret
// remainder as quotient or discard a primitive failure observable at runtime.
const rejectLower = (machine: Machine): void => {
  try { q8RangeMachineToLean('forged_q8', machine) } catch { return }
  throw new Error('unsafe q8 machine accepted by restricted Lean lowering')
}
rejectLower({...division, step: {state: {'out$0': {op: 'get', map: wordDivisionName(8, 'r', 0),
  key: wordDivisionKey([v('a$0'), v('b$0')])}}}})
rejectLower({...division, primitiveFailure: {op: '<', a: v('a$0'), b: c(1)}})
// Even empty/undefined metadata or an unknown future semantic field must fail closed.
for (const key of ['counts', 'leasts', 'relations', 'pre', 'assume', 'maps',
  'fns', 'facts', 'inputMaps', 'history', 'sums', 'futureSemanticField'])
  rejectLower({...division, [key]: undefined} as Machine)
for (const key of ['maps', 'flags', 'futureStepEffect'])
  rejectLower({...division, step: {...division.step, [key]: undefined}} as Machine)
const cases: {name: string, machine: Machine, input: [number, number], result: number}[] = [
  {name: 'actual_wrap_step', machine: wrap, input: [250, 10], result: 4},
  {name: 'actual_division_step', machine: division, input: [7, 3], result: 2},
]
const pieces = ['import Kernel', 'import WordDivisionBridge', 'open Kern', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0']
for (const x of cases) {
  const reads = wordReads(x.machine), vars = [...x.machine.inputs, 'out$0']
  const expr = x.machine.step.state!['out$0']!
  const maps = [...new Set([...JSON.stringify(expr).matchAll(/"op":"get","map":"([^"]+)"/g)].map(m => m[1]!))]
  const term = leanTerms(vars, maps, x.name)
  let base = '0'
  for (const [j, mp] of maps.entries()) {
    const m = /^(mod|div)\$(256|65536)$/.exec(mp)
    if (!m && !mp.startsWith('worddiv$')) throw new Error('unexpected opaque map ' + mp)
    if (m) base = `if mp = ${j} then key ${m[1] === 'mod' ? '%' : '/'} ${m[2]} else ${base}`
  }
  const overlay = wordMapOverlayLean(reads, maps, x.name + '_maps')
  const env = `(fun i : Nat => if i = 0 then ${x.input[0]} else if i = 1 then ${x.input[1]} else 0)`
  pieces.push(overlay, `def ${x.name}_base (mp key : Nat) : Nat := ${base}`,
    `def ${x.name}_machine : Kern.Machine := ⟨[0, 1], [(2, .const 0)], [(2, ${term.e(expr)})], .le (.const 0) (.const 0), .le (.const 0) (.const 0)⟩`,
    `theorem ${x.name} : Kern.applyS ${x.name}_machine.step ${env} (${x.name}_maps ${x.name}_base) 2 = ${x.result} := by decide`,
    `#print axioms ${x.name}`)
  // A theorem about *all reachable states* of the same concrete-map machine,
  // not a certificate about arbitrary maps. The step proof reduces its actual E.
  if (x.name === 'actual_wrap_step') pieces.push(`theorem actual_wrap_range (ρ : Nat → Nat)
    (h : Kern.Reach actual_wrap_step_machine (actual_wrap_step_maps actual_wrap_step_base) ρ) : ρ 2 < 256 := by
  induction h with
  | start ρ hp =>
      simp [actual_wrap_step_machine, Kern.applyS, Kern.assoc, Kern.lookup, Kern.evalE]
  | step ρ ι hr ha ih =>
      have hb : (ι 0 + ι 1) % 256 < 256 := Nat.mod_lt _ (by decide)
      simpa [actual_wrap_step_machine, actual_wrap_step_maps, actual_wrap_step_base, Kern.applyS, Kern.assoc, Kern.lookup, Kern.evalE, Kern.withInputs] using hb
#print axioms actual_wrap_range`)
  if (x.name === 'actual_division_step') pieces.push(`theorem actual_division_range (base : Nat → Nat → Nat) (ρ : Nat → Nat)
    (h : Kern.Reach actual_division_step_machine (actual_division_step_maps base) ρ) : ρ 2 < 256 := by
  induction h with
  | start ρ hp =>
      simp [actual_division_step_machine, Kern.applyS, Kern.assoc, Kern.lookup, Kern.evalE]
  | step ρ ι hr ha ih =>
      have hb : WordDivision.value 8 0 0 [ι 0, ι 1] < 256 := by
        simpa [WordDivision.radix] using WordDivision.value_q_lt 8 0 [ι 0, ι 1]
      simpa [actual_division_step_machine, actual_division_step_maps, Kern.applyS, Kern.assoc, Kern.lookup, Kern.evalE, Kern.pickP, Kern.cun_cpair, Kern.withInputs] using hb
#print axioms actual_division_range`)
}
const wrapExpr = wrap.step.state!['out$0']!
if (wrapExpr.op !== 'get' || wrapExpr.map !== 'mod$256') throw new Error('unexpected actual wrap expression')
const wLaw: C = {op: '<', a: v('out$0'), b: c(256)}
const wFact: C = {op: '<', a: wrapExpr, b: c(256)}
const wTrue: C = {op: '<=', a: c(0), b: c(0)}
const wStart: Goal = {name: 'wrap certificate start', hyps: [wTrue, {op: 'not', x: {op: '<', a: c(0), b: c(256)}}]}
const wStep: Goal = {name: 'wrap certificate step', hyps: [wTrue, wTrue, wLaw, wFact, {op: 'not', x: wFact}]}
const wVars = ['a$0','b$0','out$0'], wMaps = ['mod$256'], wTerms = leanTerms(wVars, wMaps, 'wrap cert')
const wProof = (g: Goal) => {
  const r = grow(g)
  if (!('tree' in r) || !check(g, r.tree as Tree)) throw new Error('wrap certificate tree did not check')
  return encode({name: g.name, goal: g, tree: r.tree as Tree}, false, true, wVars, wMaps)
}
const wa = wProof(wStart), wb = wProof(wStep)
pieces.push(`def actual_wrap_cert_entry : WordDivisionBridge.Entry :=
  ⟨${wTerms.c(wLaw)}, [], [${wTerms.c(wFact)}], (${wa.tab}, ${wa.tree}), (${wb.tab}, ${wb.tree})⟩
theorem actual_wrap_cert_check : WordDivisionBridge.checkEntries actual_wrap_step_machine [actual_wrap_cert_entry] = true := by decide +kernel
theorem actual_wrap_certified_range (ρ : Nat → Nat)
    (hr : Kern.Reach actual_wrap_step_machine (actual_wrap_step_maps actual_wrap_step_base) ρ) :
    Kern.evalC ρ (actual_wrap_step_maps actual_wrap_step_base) (${wTerms.c(wLaw)}) = true := by
  have hf : ∀ env p, p ∈ ([actual_wrap_cert_entry] : List WordDivisionBridge.Entry) →
      (∀ f ∈ p.startFacts, Kern.evalC env (actual_wrap_step_maps actual_wrap_step_base) f = true) ∧
      (∀ f ∈ p.stepFacts, Kern.evalC env (actual_wrap_step_maps actual_wrap_step_base) f = true) := by
    intro env p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · intro f h
      change f ∈ ([] : List Kern.C) at h
      simp at h
    · intro f h
      change f ∈ [${wTerms.c(wFact)}] at h
      simp only [List.mem_singleton] at h
      subst f
      have hb : Kern.evalE env (actual_wrap_step_maps actual_wrap_step_base) (${wTerms.e(wrapExpr.key)}) % 256 < 256 := Nat.mod_lt _ (by decide)
      simpa [actual_wrap_step_maps, actual_wrap_step_base, Kern.evalC, Kern.evalE] using hb
  have hs := WordDivisionBridge.checkEntries_sound actual_wrap_step_machine [actual_wrap_cert_entry]
    actual_wrap_cert_check (actual_wrap_step_maps actual_wrap_step_base) hf
  exact hs ρ hr (${wTerms.c(wLaw)}) (by simp [actual_wrap_cert_entry])
#print axioms actual_wrap_certified_range`)
pieces.push(q8RangeMachineToLean('certified_q8_division', division, {fragment: true}))
const limbs64 = Array.from({length: 8}, (_, i) => `limb${i}`)
const division64: Machine = {name: 'actual_u64_quotient_digit', params: [], inputs: limbs64,
  state: {out: c(0)}, step: {state: {out: {op: 'get', map: wordDivisionName(64, 'q', 3),
    key: wordDivisionKey(limbs64.map(v))}}}}
pieces.push(wordDigitRangeMachineToLean('certified_q64_division', division64, {fragment: true}))
const moreDigits = [[8, 'r', 0], [16, 'q', 0], [16, 'r', 0],
  [32, 'q', 1], [32, 'r', 1], [64, 'r', 3],
  [8, 'c', 2], [16, 'c', 2], [32, 'c', 4], [64, 'c', 8]] as const
const moreClaims: string[] = []
for (const [width, part, index] of moreDigits) {
  const n = width === 8 ? 1 : width / 16
  const inputs = Array.from({length: 2 * n}, (_, i) => `word${i}`)
  const name = `certified_${part}${width}_division`
  const machine: Machine = {name, params: [], inputs, state: {out: c(0)},
    step: {state: {out: {op: 'get', map: wordDivisionName(width, part, index),
      key: wordDivisionKey(inputs.map(v))}}}}
  pieces.push(wordDigitRangeMachineToLean(name, machine, {fragment: true}))
  moreClaims.push(`${name}_range`)
}
pieces.push('#print axioms WordDivisionBridge.checkWithFacts_sound',
  '#print axioms WordDivisionBridge.quotient_digit_bound',
  '#print axioms WordDivisionBridge.remainder_digit_bound',
  '#print axioms WordDivisionBridge.carry_digit_bound')
const source = pieces.join('\n\n') + '\n'
const args = process.argv.slice(2)
if (args.length === 2 && args[0] === '--standalone') {
  const one = wordDigitRangeMachineToLean('public_q64', division64)
  writeFileSync(args[1]!, one)
  console.log(JSON.stringify({output: args[1], claim: 'public_q64_range', module: 'WordDivisionBridge'}))
} else if (args.length === 3 && args[0] === '--audit-standalone') {
  const one = wordDigitRangeMachineToLean('public_q64', division64)
  if (readFileSync(args[1]!, 'utf8') !== one) throw new Error('standalone source mismatch')
  const log = readFileSync(args[2]!, 'utf8')
  if (/\berror:|declaration uses 'sorry'/.test(log)) throw new Error('standalone Lean error or sorry')
  auditLiftLog(log, [one], ['public_q64_range'])
  console.log(JSON.stringify({checked: 1, strictStandardAxioms: true, standalone: true}))
} else if (args.length === 1 && args[0] !== '--audit') {
  writeFileSync(args[0]!, source)
  console.log(JSON.stringify({output: args[0], claims: [...cases.map(x => x.name), 'actual_wrap_range', 'actual_division_range', 'actual_wrap_certified_range', 'WordDivisionBridge.checkWithFacts_sound',
    'WordDivisionBridge.quotient_digit_bound', 'WordDivisionBridge.remainder_digit_bound',
    'WordDivisionBridge.carry_digit_bound', 'certified_q8_division_range',
    'certified_q64_division_range', ...moreClaims], note: 'unverified source; compile and audit complete Lean log'}))
} else if (args.length === 3 && args[0] === '--audit') {
  if (readFileSync(args[1]!, 'utf8') !== source) throw new Error('generated source mismatch')
  const log = readFileSync(args[2]!, 'utf8')
  if (/\berror:|declaration uses 'sorry'/.test(log)) throw new Error('Lean reported error or sorry')
  const rows = auditLiftLog(log, [source], [...cases.map(x => x.name), 'actual_wrap_range', 'actual_division_range',
    'WordDivisionBridge.checkWithFacts_sound', 'WordDivisionBridge.quotient_digit_bound',
    'WordDivisionBridge.remainder_digit_bound', 'WordDivisionBridge.carry_digit_bound',
    'actual_wrap_certified_range', 'certified_q8_division_range', 'certified_q64_division_range', ...moreClaims])
  console.log(JSON.stringify({checked: rows.length, strictStandardAxioms: true, scope: 'closed transitions, concrete reachability, and fully checked scalar q/r/c machines at widths 8/16/32/64; generic intrinsic SMachine certificates remain unavailable'}))
} else throw new Error('usage: lean-machine-gate.ts OUTPUT | --audit OUTPUT LOG')
