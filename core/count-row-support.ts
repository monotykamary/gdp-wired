// An untrusted strategy request: instantiate an existing PRE count law,
// then propose ordinary inclusion witnesses. No scalar guard is asserted.
import {type Law, type Machine, x} from './machine.ts'
import {type RowAgreementShape} from './row-agreement-shape.ts'
import {type RowAgreementOptions} from './count-row-agreement.ts'
import {type CountRequestBuilder} from './count-strategy.ts'
import {fixedCountFrameCase} from './count-frames.ts'
import {discoverCountGuardShape} from './count-guard-shape.ts'
import {discoverCountThresholdWrite} from './count-write-shape.ts'
import {memberInclusions} from './count-recovery/member-inclusions.ts'
import {certFor} from './counts.ts'
import {clock} from '../kernel/prove.ts'
import {identicalRowCountAliases, restrictedRowCountAliases} from './count-row-aliases.ts'
export function rowCountSupport(m: Machine, family: Law[], target: Law, row: RowAgreementShape, until: number): {options: RowAgreementOptions, request: CountRequestBuilder, report: unknown} | undefined {
  const choice = fixedCountFrameCase(m)
  if (!choice || !target.forall || target.keys?.length !== 2) return
  const matches = family.flatMap(law => {
    const shape = discoverCountGuardShape(m, law, family)
    if (!shape || shape.membershipMap !== row.map || !row.fields.includes(shape.thresholdField)) return []
    const write = discoverCountThresholdWrite(m, shape, choice)
    return write?.increment === 1 ? [{law, shape, write}] : []
  })
  // Prefer the most restricted vote predicate, never its weaker base law.
  // The election witness must prove every restriction; unrelated roots decline.
  const roots = matches.filter(match => !matches.some(other => other.shape.weakerLaw === match.law))
  if (roots.length !== 1) return
  const {law, shape, write} = roots[0]!, report = {law: law.name, shape, write, inclusionCounts: [] as number[], aliasCounts: [] as number[]}
  const seedInstances = {[law.name]: [x(write.source), x(target.forall + '#'), x(write.source), x(target.keys[0]!)]}
  const scope = JSON.stringify([m, family]); let prefix = 'rowCountWitness$'
  while (scope.includes(prefix)) prefix += '$'
  const request: CountRequestBuilder = (goal, decls) => {
    const base = certFor(goal, decls, false, 0, () => clock() < until)
    const inclusions = memberInclusions(m, decls, base.reads, () => clock() < until).filter(p => p.carried === write.input && base.reads.some(r => r[0] === p.negative && r[1] === shape.voteMap)).slice(0, 8)
    const aliases = [...restrictedRowCountAliases(decls, base.reads, shape.voteMap, prefix + 'voteAlias$', () => clock() < until), ...identicalRowCountAliases(decls, base.reads, shape.rowMap, prefix + 'alias$', () => clock() < until)]
    report.inclusionCounts.push(inclusions.length); report.aliasCounts.push(aliases.length)
    return {...base, insts: [...inclusions.map((p, i) => ({wit: prefix + i, below: p.below, terms: [[1, p.positive], [-1, p.negative]] as [number, string][], unit: 0})), ...aliases]}
  }
  return {options: {seedInstances, witnessFlags: true}, request, report}
}
