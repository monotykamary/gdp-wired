// The reserved word maps are *not* arbitrary state maps. This module records the
// exact source-level encoding and renders their Nat semantics for Lean obligations.
// A machine certificate may use these only when the Lean checker itself derives
// the corresponding digit/carry facts; merely adding facts to a certificate is unsound.
import {parseWordDivisionName, wordDivisionArgs, wordDivisionName, type WordDivisionSpec} from '../kernel/word-division.ts'
import type {E} from '../core/machine.ts'
import {leanTerms} from './lean-terms.ts'

export type WordRead = {spec: WordDivisionSpec, args: E[], key: E, map: string}

/** Walk arbitrary machine/law syntax; invalid reserved names or tuple arity fail closed. */
export function wordReads(source: unknown): WordRead[] {
  const out: WordRead[] = [], seen = new WeakSet<object>()
  const visit = (node: unknown): void => {
    if (node === null || typeof node !== 'object' || seen.has(node)) return
    seen.add(node)
    if (!Array.isArray(node)) {
      const x = node as Record<string, unknown>
      if (x.op === 'get' && typeof x.map === 'string' && x.map.startsWith('worddiv$')) {
        const spec = parseWordDivisionName(x.map)
        if (!spec || !x.key || typeof x.key !== 'object') throw new Error('invalid reserved word-division read')
        const key = x.key as E, args = wordDivisionArgs(key, spec.width)
        if (!args) throw new Error('invalid reserved word-division tuple')
        out.push({spec, args, key, map: x.map})
      }
    }
    for (const child of Object.values(node)) visit(child)
  }
  visit(source)
  return out
}

/** Native helper IDs needed even when a word-valued update is irrelevant to all
 * exported laws and therefore absent from the minimized proof obligations. */
export function wordSchemaMapNames(source: unknown): string[] {
  const widths = new Set(wordReads(source).map(read => read.spec.width))
  return [...widths].flatMap(width => {
    const n = width === 8 ? 1 : width / 16
    return [...Array.from({length: n}, (_, i) => wordDivisionName(width, 'q', i)),
      ...Array.from({length: n}, (_, i) => wordDivisionName(width, 'r', i)),
      ...Array.from({length: 2 * n}, (_, i) => wordDivisionName(width, 'c', i + 1))]
  })
}

/** Build a closed Lean computation from actual lowered limb values. The expression
 * is independently evaluated by Lean's Nat division, not by a TS answer. */
export function wordDigitLean(read: WordRead, operands: readonly number[]): string {
  const {width, part, index} = read.spec
  const n = width === 8 ? 1 : width / 16, radix = width === 8 ? 256 : 65536
  if (operands.length !== 2 * n || operands.some(v => !Number.isSafeInteger(v) || v < 0 || v >= radix))
    throw new Error('closed word gate requires exactly bounded limbs')
  const args = '[' + operands.join(', ') + ']'
  return `WordDivision.value ${width} ${part === 'q' ? 0 : part === 'r' ? 1 : 2} ${index} ${args}`
}

/** Right-associated Kern.cpair key decoded in the same order as wordDivisionArgs. */
export function wordKeyPartsLean(key: string, count: number): string[] {
  if (!Number.isSafeInteger(count) || count < 2 || count > 8) throw new Error('invalid word limb count')
  let tail = key
  const parts: string[] = []
  for (let i = 1; i < count; i++) {
    parts.push(`(Kern.pickP 0 ${tail})`)
    tail = `(Kern.pickP 1 ${tail})`
  }
  return [...parts, tail]
}

/** A concrete, transparent interpretation of every reserved map index, including
 * helper digit/carry maps introduced only by generated certificate hypotheses.
 * Ordinary map indices continue to read base. This overlay alone is NOT a proof
 * of a machine certificate: all used helper facts need a Lean semantic discharge. */
export function wordMapOverlayLean(reads: readonly WordRead[], maps: readonly string[], name: string): string {
  if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(name)) throw new Error('invalid Lean name')
  const cases = new Map<string, WordDivisionSpec>()
  for (const read of reads) {
    const at = maps.indexOf(read.map)
    if (at < 0) throw new Error(`missing word map ${read.map}`)
    const old = cases.get(read.map)
    if (old && JSON.stringify(old) !== JSON.stringify(read.spec)) throw new Error('inconsistent reserved map')
    cases.set(read.map, read.spec)
  }
  for (const map of maps) {
    if (!map.startsWith('worddiv$')) continue
    const spec = parseWordDivisionName(map)
    if (!spec) throw new Error(`invalid reserved word map ${map}`)
    cases.set(map, spec)
  }
  let body = 'base mp key'
  for (const [map, spec] of [...cases].reverse()) {
    const n = spec.width === 8 ? 1 : spec.width / 16
    const args = `[${wordKeyPartsLean('key', 2 * n).join(', ')}]`
    const tag = spec.part === 'q' ? 0 : spec.part === 'r' ? 1 : 2
    body = `if mp = ${maps.indexOf(map)} then WordDivision.value ${spec.width} ${tag} ${spec.index} ${args} else ${body}`
  }
  return `def ${name} (base : Nat → Nat → Nat) (mp key : Nat) : Nat :=\n  ${body}`
}

/** Exact descriptor data for the generic Lean schema. No caller-supplied fact
 * proposition is trusted: Lean constructs the complete clause list itself. */
export function wordMachineBridgeLean(id: string, source: unknown, vars: readonly string[], maps: readonly string[]): string {
  const reads = wordReads(source)
  if (!reads.length) return ''
  const unique = new Map<string, WordRead>()
  for (const read of reads) unique.set(`${read.spec.width}:${JSON.stringify(read.args)}`, read)
  const terms = leanTerms(vars, maps, id)
  const list = (xs: readonly (string | number)[]) => `[${xs.join(', ')}]`
  const reserved = maps.flatMap((map, i) => map.startsWith('worddiv$') ? [i] : [])
  const mapId = (width: WordDivisionSpec['width'], part: WordDivisionSpec['part'], i: number): number => {
    const map = wordDivisionName(width, part, i), at = maps.indexOf(map)
    if (at < 0) throw new Error(`${id}: missing schema map ${map}`)
    return at
  }
  const names: string[] = [], blocks: string[] = []
  for (const [i, read] of [...unique.values()].entries()) {
    const name = `${id}_word_spec${i}`, width = read.spec.width, n = width === 8 ? 1 : width / 16
    names.push(name)
    const q = Array.from({length: n}, (_, j) => mapId(width, 'q', j))
    const r = Array.from({length: n}, (_, j) => mapId(width, 'r', j))
    const carries = Array.from({length: 2 * n}, (_, j) => mapId(width, 'c', j + 1))
    const ids = [...q, ...r, ...carries]
    const finiteCases = (indices: number[]) => `have cases : ${indices.map(j => `i = ${j}`).join(' ∨ ')} := by omega\n    rcases cases with ${indices.map(() => 'rfl').join(' | ')}\n    all_goals rfl`
    blocks.push(`def ${name} : WordFacts.Spec := ⟨${width}, ${list(read.args.map(x => `(${terms.e(x)})`))}, ${list(q)}, ${list(r)}, ${list(carries)}⟩
theorem ${name}_valid : ${name}.Valid := by unfold WordFacts.Spec.Valid; decide +kernel
-- Dispatch is checked for every native digit at every concrete tuple key.
theorem ${name}_values : WordFacts.ValueMatches ${name} ${id}_word.value := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi key
    change i < ${n} at hi
    ${finiteCases(Array.from({length: n}, (_, j) => j))}
  · intro i hi key
    change i < ${n} at hi
    ${finiteCases(Array.from({length: n}, (_, j) => j))}
  · intro i hlo hhi key
    change i ≤ ${2 * n} at hhi
    ${finiteCases(Array.from({length: 2 * n}, (_, j) => j + 1))}
theorem ${name}_reserved {mp : Nat} (hm : mp ∈ ${name}.reserved) :
    mp ∈ ${id}_word.reserved := by
  change mp ∈ ${list(ids)} at hm
  change mp ∈ ${list(reserved)}
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with ${ids.map(() => 'rfl').join(' | ')}
  all_goals decide +kernel
`)
  }
  return `${wordMapOverlayLean(reads, maps, `${id}_word_maps`)}
def ${id}_word : Kern.WordReach.WordSMachine := {
  s := ${id}_machine
  reserved := ${list(reserved)}
  value := ${id}_word_maps (fun _ _ => 0)
  startDisjoint := by decide +kernel
  carriedDisjoint := by decide +kernel
  everyDisjoint := by decide +kernel
  writesDisjoint := by decide +kernel
}
${blocks.join('\n')}
def ${id}_word_extra : List Kern.C := (${list(names)} : List WordFacts.Spec).flatMap WordFacts.facts
theorem ${id}_word_extra_sound : ∀ X N,
    Kern.WordReach.WordInterpret ${id}_word.reserved ${id}_word.value N →
    ∀ c ∈ ${id}_word_extra, Kern.evalC X N c = true := by
  intro X N h c hc
  simp only [${id}_word_extra, List.mem_flatMap] at hc
  obtain ⟨spec, hs, hc⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with ${names.map(() => 'rfl').join(' | ')}
${names.map(name => `  · exact WordFacts.facts_sound ${name} ${name}_valid X N
      (WordFacts.interpret_sound ${name} ${name}_valid ${id}_word.value N X ${name}_values
        (fun mp hm key => h mp (${name}_reserved hm) key)) c hc`).join('\n')}`
}
