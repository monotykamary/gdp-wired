// Restricted, sound scalar-machine export for real quotient/remainder/carry digits.
// It never turns intrinsic facts into arbitrary-map assumptions: Lean proves the
// sole selected bound against WordDivision.value under a concrete map overlay.
import type {C, E, Machine} from '../core/machine.ts'
import {check, type Goal, type Tree} from '../kernel/kernel.ts'
import {grow} from '../kernel/prove.ts'
import {encode, TRUE} from './emit.ts'
import {leanTerms} from './lean-terms.ts'
import {wordReads, wordMapOverlayLean} from './word-division-export.ts'
import {wordDivisionKey} from '../kernel/word-division.ts'

const constant = (value: number): E => ({op: 'const', value})
const same = (a: unknown, b: unknown) => JSON.stringify(a) === JSON.stringify(b)

/** Certified scalar-machine range for any actual q/r/c digit (8/16/32/64).
 * This is NOT a generic SMachine exporter; the exact source shape is verified. */
export function wordDigitRangeMachineToLean(id: string, m: Machine, opts: {fragment?: boolean} = {}): string {
  const reads = wordReads(m)
  if (reads.length !== 1) throw new Error('expected one valid reserved word read')
  const {width, part, index} = reads[0]!.spec
  // Model shape is an allowlist, not a denylist: future Machine/step fields
  // cannot silently change runtime semantics while this export omits them.
  const machineKeys = new Set(['name', 'params', 'inputs', 'state', 'step'])
  if (Object.keys(m).some(key => !machineKeys.has(key)) ||
      Object.keys(m.step).some(key => key !== 'state'))
    throw new Error('unsupported scalar machine metadata or step effect')
  const n = width === 8 ? 1 : width / 16, radix = width === 8 ? 256 : 65536
  const bound = part === 'c' ? n * radix : radix, op = part === 'c' ? '<=' : '<'
  if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(id) || m.params.length || m.inputs.length !== 2 * n ||
      Object.keys(m.state).length !== 1 || Object.keys(m.step.state ?? {}).length !== 1 ||
      new Set([...m.inputs, ...Object.keys(m.state)]).size !== 2 * n + 1 ||
      !Array.isArray(m.params) || !Array.isArray(m.inputs))
    throw new Error('word digit range machine requires exact scalar shape without auxiliary effects')
  const out = Object.keys(m.state)[0]!
  const key: E = wordDivisionKey(m.inputs.map((name): E => ({op: 'var', name})))
  const expr: E = {op: 'get', map: reads[0]!.map, key}
  if (!same(m.state[out], constant(0)) || !same(m.step.state?.[out], expr) || !same(reads[0]!.key, key))
    throw new Error('word digit range machine must use its exact reserved read and zero initialization')
  const law: C = {op, a: {op: 'var', name: out}, b: constant(bound)}
  const fact: C = {op, a: expr, b: constant(bound)}
  const neg = (x: C): C => ({op: 'not', x})
  const pre: C = {op: '<=', a: constant(0), b: constant(0)}
  const start: Goal = {name: id + '_start', hyps: [pre, neg({op, a: constant(0), b: constant(bound)})]}
  const step: Goal = {name: id + '_step', hyps: [pre, pre, law, fact, neg(fact)]}
  const vars = [...m.inputs, out], maps = [expr.map]
  const terms = leanTerms(vars, maps, id)
  const prove = (g: Goal) => {
    const result = grow(g)
    if (!('tree' in result) || !check(g, result.tree as Tree)) throw new Error(id + ': proof tree does not check')
    return encode({name: g.name, goal: g, tree: result.tree as Tree}, false, true, vars, maps)
  }
  const a = prove(start), b = prove(step)
  const overlay = wordMapOverlayLean(reads, maps, id + '_maps')
  const e = terms.e, c = terms.c, state = m.inputs.length
  const values = `[${m.inputs.map((_, i) => `env ${i}`).join(', ')}]`
  const lemma = part === 'q' ? 'value_q_lt' : 'value_r_lt'
  const factProof = part === 'c'
    ? `have hb := WordDivision.carry_bound ${width} ${values} ${index}
      simpa [${id}_maps, Kern.evalC, Kern.evalE, Kern.pickP, Kern.cun_cpair,
        WordDivision.value_c, WordDivision.limbs, WordDivision.radix] using hb`
    : `have hb := WordDivision.${lemma} ${width} ${index} ${values}
      simpa [${id}_maps, Kern.evalC, Kern.evalE, Kern.pickP,
        Kern.cun_cpair, WordDivision.radix] using hb`
  const source = `${overlay}
def ${id}_machine : Kern.Machine := ⟨[${m.inputs.map((_, i) => i).join(', ')}], [(${state}, ${e(constant(0))})],
  [(${state}, ${e(expr)})], ${TRUE}, ${TRUE}⟩
def ${id}_entry : WordDivisionBridge.Entry :=
  ⟨${c(law)}, [], [${c(fact)}], (${a.tab}, ${a.tree}), (${b.tab}, ${b.tree})⟩
theorem ${id}_check : WordDivisionBridge.checkEntries ${id}_machine [${id}_entry] = true := by decide +kernel
/-- Full reachable-state machine law, for all input sequences and all base maps. -/
theorem ${id}_range (base : Nat → Nat → Nat) (ρ : Nat → Nat)
    (hr : Kern.Reach ${id}_machine (${id}_maps base) ρ) :
    Kern.evalC ρ (${id}_maps base) (${c(law)}) = true := by
  have hf : ∀ env p, p ∈ ([${id}_entry] : List WordDivisionBridge.Entry) →
      (∀ f ∈ p.startFacts, Kern.evalC env (${id}_maps base) f = true) ∧
      (∀ f ∈ p.stepFacts, Kern.evalC env (${id}_maps base) f = true) := by
    intro env p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · intro f h
      change f ∈ ([] : List Kern.C) at h
      simp at h
    · intro f h
      change f ∈ [${c(fact)}] at h
      simp only [List.mem_singleton] at h
      subst f
      ${factProof}
  have hs := WordDivisionBridge.checkEntries_sound ${id}_machine [${id}_entry]
    ${id}_check (${id}_maps base) hf
  exact hs ρ hr (${c(law)}) (by simp [${id}_entry])
#print axioms ${id}_range`
  return opts.fragment ? source : `import WordDivisionBridge
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

${source}
`
}

/** Compatibility wrapper: admit only the original one-limb u8 quotient lane. */
export function q8RangeMachineToLean(id: string, m: Machine, opts: {fragment?: boolean} = {}): string {
  const reads = wordReads(m)
  if (reads.length !== 1 || reads[0]!.spec.width !== 8 || reads[0]!.spec.part !== 'q' || reads[0]!.spec.index !== 0)
    throw new Error('expected one actual u8 quotient digit')
  return wordDigitRangeMachineToLean(id, m, opts)
}
