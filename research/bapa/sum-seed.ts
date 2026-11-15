// Mechanical SUM-name restatement. Declarations and laws are proposals, not facts.
import {MapRef, declaredSum} from '../../core/dsl.ts'
import type {Machine, Sum} from '../../core/machine.ts'
import {mapArities, sumMachine} from '../../kernel/kernel.ts'
import type {TupleSumSeed} from './tuple-sum-seed.ts'
import type {SeedBindings} from './candidate-seed-restatement.ts'

export type SumSeedAudit =
  | {source: string, status: 'candidate', sourceMap: string, targetMap: string, nativeName: string, nativeDefinition: Sum}
  | {source: string, status: 'tuple-proposal', sourceMap: string, targetMap: string, arity: number, projection: 'finite-subsum', globalTotal: false}
  | {source: string, status: 'dropped', reason: string}
export type SumSeedResult = {audit: SumSeedAudit[], substitutions: Record<string, string>, nativeSums: Record<string, Sum>, tupleSums: Record<string, TupleSumSeed>}

/** Register unary whole-cell sums only. Tuple totals have no native SUM declaration:
 * proposeTupleSumCells supplies explicitly weaker, full-coordinate candidate laws.
 * The caller materializes unary sums via native.withSumsOf, not on its public source. */
export function restateSumSeeds(source: Machine, target: Machine, bindings: SeedBindings): SumSeedResult {
  const audit: SumSeedAudit[] = [], tupleSums: Record<string, TupleSumSeed> = {}
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
      const arity = mapArities(target)[layout.target]
      if (arity !== undefined && arity !== layout.sorts.length) throw Error('target key arity does not match layout')
      if (layout.sorts.length > 1) {
        tupleSums[name] = {sourceMap, targetMap:layout.target, arity:layout.sorts.length}
        audit.push({source:name,status:'tuple-proposal',sourceMap,targetMap:layout.target,arity:layout.sorts.length,projection:'finite-subsum',globalTotal:false})
        continue
      }
      const e = new MapRef(layout.target, 0).sum().e
      if (e.op !== 'var') throw Error('native sum did not return a variable')
      const nativeName = e.name, nativeDefinition = declaredSum(nativeName)
      if (!nativeDefinition || nativeDefinition.term.op !== 'get' || nativeDefinition.term.map !== layout.target || nativeDefinition.term.key.op !== 'var' || nativeDefinition.term.key.name !== nativeDefinition.key) throw Error('native declaration mismatch')
      const existing = target.sums?.[nativeName]
      if (existing && JSON.stringify(existing) !== JSON.stringify(nativeDefinition)) throw Error('conflicting target sum')
      // Validate the actual lowered proof machine too, not just the declaration.
      mapArities(sumMachine({...target, sums: {...target.sums, [nativeName]: nativeDefinition}}).machine)
      audit.push({source:name, status:'candidate', sourceMap, targetMap:layout.target, nativeName, nativeDefinition})
    } catch (error) { audit.push({source:name, status:'dropped', reason:error instanceof Error ? error.message : String(error)}) }
  }
  const accepted = audit.filter((a): a is Extract<SumSeedAudit,{status:'candidate'}> => a.status === 'candidate')
  return {audit, substitutions:Object.fromEntries(accepted.map(a=>[a.source,a.nativeName])), nativeSums:Object.fromEntries(accepted.map(a=>[a.nativeName,a.nativeDefinition])),tupleSums}
}
