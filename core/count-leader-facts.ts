// Generate and prove ordinary per-key facts from the current fixed operation.
// Nothing is loaded from a saved proof packet or a protocol-specific table.
import {type Law, n, same, x} from './machine.ts'
import {type GuardCountContext} from './count-guard-context.ts'
import {type CountRequestBuilder} from './count-strategy.ts'
import {countPrimitiveUnits} from './count-primitive-budget.ts'
import {countFrameConditions, fixedCountFrameCase, ownCountLawInstance} from './count-frames.ts'
import {guardRegionProposals} from './count-guard-proposals.ts'
import {type CheckedGuardLinearFact, type GuardCountProposal, guardLinearFact} from './count-guard-facts.ts'
import {countsForReads} from './count-facts.ts'
import {type MapRead, type Path, canon, countedObligations} from '../kernel/kernel.ts'
import {clock, pastWall} from '../kernel/prove.ts'
// The leader closure uses a voter upper bound on the guard complement and a
// pre <= post row bound. Opposite-direction frames and guard-intersection
// proposals are not premises of this closure. Selection is untrusted: retained
// proposals are still proved, and the final original obligation still checks.
export function leaderCountProposals(proposals: readonly GuardCountProposal[]): GuardCountProposal[] {
  return proposals.filter(p => p.kind === 'guard-complement-upper' ||
    p.kind === 'row-frame' && p.terms.length === 2 && p.terms[0]![0] === -1).slice(0, 24)
}
export function proveLeaderCountFacts(context: GuardCountContext, family: Law[], law: Law, until: number, requestFor: CountRequestBuilder, leafUnits?: number): {reads: MapRead[], facts: CheckedGuardLinearFact[]} | undefined {
  const m = context.machine, choice = fixedCountFrameCase(m), index = family.indexOf(law)
  if (!choice || index < 0 || clock() >= until || pastWall()) return
  const step = countedObligations(m, family, {[law.name]: ownCountLawInstance(law, {})}, index).at(-1)!
  const base = requestFor(step.goal, step.decls), reads: MapRead[] = [...base.reads]
  const taken = new Set(reads.map(r => r[0])), scope = JSON.stringify([m, family]); let serial = 0
  for (const entry of context.restrictions) for (const r of base.reads.filter(r => r[1] === entry.base)) for (const map of [entry.positive, entry.negative]) {
    if (reads.some(t => t[1] === map && JSON.stringify(t[2]) === JSON.stringify(r[2]))) continue
    let name: string; do {name = `guard$r${serial++}`} while (taken.has(name) || scope.includes(JSON.stringify(name))); taken.add(name)
    reads.push([name, map, r[2]])
  }
  const counts = countsForReads(step.decls, reads)
  if (!counts) return
  const path: Path = new Map(countFrameConditions(choice).map(lin => [canon(lin), {lin, holds: true}]))
  const proposals = guardRegionProposals(counts, reads, step.decls, m.inputMaps ?? [], same(x(choice.name), n(choice.value)), path), facts: CheckedGuardLinearFact[] = []
  for (const proposal of leaderCountProposals(proposals.counts)) {
    if (clock() >= until || pastWall()) return
    const fact = guardLinearFact(step.decls, reads, proposal, Math.min(until, clock() + countPrimitiveUnits(150, leafUnits)))
    if (fact) facts.push(fact)
  }
  return {reads, facts}
}
