// Opt-in proposers only. Every successful composer checks the caller's machine;
// definition-extended guard contexts must already be admitted by the caller.
import {type Law, type Machine} from './machine.ts'
import {type CountRequestBuilder, type CountStrategyProof, strategyLeafUnits} from './count-strategy.ts'
import {discoverRowAgreement} from './row-agreement-shape.ts'
import {prepareGuardCountContext} from './count-guard-context.ts'
import {proveCountRowComposition} from './count-row-composition.ts'
import {proveCountGuardComposition} from './count-guard-composition.ts'
import {clock, fullRate, fullWork, late, withDeadline} from '../kernel/prove.ts'
import {env} from './solver.ts'
// Install only conservative count definitions, once before the family's attempts.
// Candidate generation is already finished: no extra law or trusted fact is added.
export function prepareCountStrategyMachine(m: Machine, family: Law[], until: number, observe?: (event: Record<string, unknown>) => void): Machine {
  return withDeadline(until, () => {
    let machine = m
    for (const law of family) {
      if (late(until)) break
      const context = prepareGuardCountContext(machine, law, family)
      if (context) machine = context.machine
    }
    const added = Object.keys(machine.counts ?? {}).filter(name => !m.counts?.[name]).length
    observe?.({added})
    return machine
  })
}
// Shape discovery is scheduling only; it does not authorize a proof or a premise.
export function countStrategyKind(m: Machine, family: Law[], law: Law): 'row' | 'guard' | undefined {
  if (discoverRowAgreement(m, law)) return 'row'
  if (prepareGuardCountContext(m, law, family)) return 'guard'
  return undefined
}
// Structural dispatch only; this admits no proof or premise.
export function selectedCountStrategies(m: Machine, family: Law[]): Law[] {
  return family.filter(law => !!countStrategyKind(m, family, law))
}
// The caller owns allocation (for example the tier budget); every law and case
// consumes this one absolute end. Unused pool time is never reserved here.
export function proveCountStrategyPool(m: Machine, family: Law[], until: number, request: CountRequestBuilder, observe?: (event: Record<string, unknown>) => void, workAllowance = Math.max(0, until - clock())): {proofs: Map<string, CountStrategyProof>, declined: string[]} {
  return withDeadline(until, () => {
    const proofs = new Map<string, CountStrategyProof>(), declined: string[] = []
    if (late(until)) return {proofs, declined}
    const selected = family.map(law => ({law, kind: countStrategyKind(m, family, law)})).filter(row => row.kind)
    selected.sort((a, b) => Number(a.kind === 'row') - Number(b.kind === 'row'))
    for (const {law} of selected) {
      if (late(until)) break
      const start = fullWork()
      const proof = proveCountStrategies(m, family, law, until, request, event => observe?.({law: law.name, end: until, ...event}), workAllowance)
      if (proof) proofs.set(law.name, proof)
      else declined.push(law.name)
      observe?.({stage: 'pool-law', law: law.name, end: until, checked: !!proof, units: (fullWork() - start) / fullRate})
    }
    return {proofs, declined}
  })
}
export function proveCountStrategies(m: Machine, family: Law[], law: Law, until: number, request: CountRequestBuilder, observe?: (event: Record<string, unknown>) => void, workAllowance = Math.max(0, until - clock())): CountStrategyProof | undefined {
  return withDeadline(until, () => {
    if (late(until)) return
    const leafUnits = strategyLeafUnits(workAllowance)
    if (discoverRowAgreement(m, law)) {
      observe?.({strategy: 'row', stage: 'search-budget', workAllowance, leafUnits})
      return proveCountRowComposition(m, family, law, until, request, e => observe?.({strategy: 'row', ...e}), {framePremisesOnly: true, leafUnits, deferRowChecks: env.GDP_COUNT_ROW_DEFER_CHECKS === '1'})
    }
    const context = prepareGuardCountContext(m, law, family)
    if (!context) return
    const original = m.counts ?? {}, extended = context.machine.counts ?? {}
    if (Object.keys(original).length !== Object.keys(extended).length || Object.entries(extended).some(([name, count]) => JSON.stringify(original[name]) !== JSON.stringify(count))) {
      observe?.({strategy: 'guard', stage: 'decline', reason: 'unadmitted count definitions'})
      return
    }
    observe?.({strategy: 'guard', stage: 'search-budget', workAllowance, leafUnits})
    return proveCountGuardComposition({...context, machine: m}, family, law, until, request, e => observe?.({strategy: 'guard', ...e}), {caseOrder: 'cost', minimalView: true, leafUnits})
  })
}
