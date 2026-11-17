// The reserved word maps are *not* arbitrary state maps. This module records the
// exact source-level encoding and renders their Nat semantics for Lean obligations.
// A machine certificate may use these only when the Lean checker itself derives
// the corresponding digit/carry facts; merely adding facts to a certificate is unsound.
import {parseWordDivisionName, wordDivisionArgs, type WordDivisionSpec} from '../kernel/word-division.ts'
import type {E} from '../core/machine.ts'

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
