// Mechanical SUM-name restatement. Declarations and laws are proposals, not facts.
import {MapRef, declaredSum} from '../../core/dsl.ts'
import type {Machine, Sum} from '../../core/machine.ts'
import {sumMachine} from '../../kernel/kernel.ts'
import type {SeedBindings} from './candidate-seed-restatement.ts'

export type SumSeedAudit =
  | {source: string, status: 'candidate', sourceMap: string, targetMap: string, nativeName: string, nativeDefinition: Sum}
  | {source: string, status: 'dropped', reason: string}
export type SumSeedResult = {audit: SumSeedAudit[], substitutions: Record<string, string>, nativeSums: Record<string, Sum>}

/** Register only native whole-cell sums; the caller must materialize them via
 * native.withSumsOf(...laws) inside the prover, leaving its public source machine untouched. */
export function restateSumSeeds(source: Machine, target: Machine, bindings: SeedBindings): SumSeedResult {
  const audit: SumSeedAudit[] = []
  for (const [name, definition] of Object.entries(source.sums ?? {})) {
    try {
      const term = definition.term
      if (typeof definition.key !== 'string' || !definition.key || !term || term.op !== 'get' || term.key.op !== 'var' || term.key.name !== definition.key || Object.keys(term).length !== 3 || Object.keys(term.key).length !== 2 || Object.keys(definition).length !== 2) throw Error('not an exact whole-cell sum')
      const sourceMap = term.map, layout = bindings.maps[sourceMap]
      if (source.maps?.[sourceMap] !== 0 || (source.inputMaps ?? []).includes(sourceMap)) throw Error('source map is not zero-initialized state')
      if (!layout || !layout.target || !layout.sorts.length || !Number.isSafeInteger(layout.radix) || layout.radix < 2) throw Error('missing or invalid map binding')
      if (target.maps?.[layout.target] !== 0 || (target.inputMaps ?? []).includes(layout.target)) throw Error('target map is not zero-initialized state')
      const sorts = target.relations?.[layout.target]
      if (sorts && JSON.stringify(sorts) !== JSON.stringify(layout.sorts)) throw Error('target map layout mismatch')
      for (const sort of layout.sorts) if (!bindings.domains[sort] || !target.params.includes(bindings.domains[sort]!)) throw Error(`missing symbolic domain for ${sort}`)
      const e = new MapRef(layout.target, 0).sum().e
      if (e.op !== 'var') throw Error('native sum did not return a variable')
      const nativeName = e.name, nativeDefinition = declaredSum(nativeName)
      if (!nativeDefinition || nativeDefinition.term.op !== 'get' || nativeDefinition.term.map !== layout.target || nativeDefinition.term.key.op !== 'var' || nativeDefinition.term.key.name !== nativeDefinition.key) throw Error('native declaration mismatch')
      const existing = target.sums?.[nativeName]
      if (existing && JSON.stringify(existing) !== JSON.stringify(nativeDefinition)) throw Error('conflicting target sum')
      sumMachine({...target, sums: {...target.sums, [nativeName]: nativeDefinition}})
      audit.push({source:name, status:'candidate', sourceMap, targetMap:layout.target, nativeName, nativeDefinition})
    } catch (error) { audit.push({source:name, status:'dropped', reason:error instanceof Error ? error.message : String(error)}) }
  }
  const accepted = audit.filter((a): a is Extract<SumSeedAudit,{status:'candidate'}> => a.status === 'candidate')
  return {audit, substitutions:Object.fromEntries(accepted.map(a=>[a.source,a.nativeName])), nativeSums:Object.fromEntries(accepted.map(a=>[a.nativeName,a.nativeDefinition]))}
}
