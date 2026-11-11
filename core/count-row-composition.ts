// Optional versioned-row portfolio. All cases share the caller's deadline.
// STEP cases and INIT are proposals: only the final original-goal checker accepts them.
import {type Law, type Machine, all, n, same, x} from './machine.ts'
import {type CountRequestBuilder, type CountStrategyProof, type CountStrategyOptions} from './count-strategy.ts'
import {finiteCountChoice} from './count-cases.ts'
import {traceNow} from './trace-clock.ts'
import {traceCountStage} from './count-stage-trace.ts'
import {countCertificateSize} from './count-certificate-minimize.ts'
import {discoverCountGuardShape} from './count-guard-shape.ts'
import {discoverCountRowCopy} from './count-copy-shape.ts'
import {discoverRowAgreement} from './row-agreement-shape.ts'
import {proveRowAgreementCase, proposeRowAgreementInitial, rowAgreementWrittenKeys} from './count-row-agreement.ts'
import {classifyRowValueWrite} from './count-row-policy.ts'
import {rowCountSupport} from './count-row-support.ts'
import {composeCountOperationProofs, type FixedOperationProof} from './count-case-compose.ts'
import {clock, fullRate, fullWork, late, withDeadline} from '../kernel/prove.ts'
export function proveCountRowComposition(m: Machine, family: Law[], law: Law, until: number, requestFor: CountRequestBuilder, observe?: (event: Record<string, unknown>) => void, options: CountStrategyOptions & {framePremisesOnly?: boolean} = {}): CountStrategyProof | undefined {
  return withDeadline(until, () => {
    if (late(until)) return
    const row = discoverRowAgreement(m, law), choice = finiteCountChoice(m)
    if (!row || !choice) return
    const shapes = family.flatMap(l => {const s = discoverCountGuardShape(m, l, family); return s?.membershipMap === row.map ? [s] : []})
    if (!shapes.length) return
    const planned = traceCountStage(observe, 'row-plan', 'untrusted-assembly', () => [...choice[1]].map(value => {
      const machine = {...m, assume: all(...(m.assume ? [m.assume] : []), same(x(choice[0]), n(value)))}, support = traceCountStage(observe, 'row-plan-support-' + value, 'untrusted-assembly', () => rowCountSupport(machine, family, law, row, until))
      const kind = !rowAgreementWrittenKeys(machine, row).length ? 'frame' : support ? 'leader' : shapes.some(shape => discoverCountRowCopy(machine, shape, {name: choice[0], value})) ? 'copy' : classifyRowValueWrite(machine, row) ?? 'replacement'
      return {value, machine, support, kind}
    }))
    const rank: Record<string, number> = {leader: 0, copy: 1, load: 2, replacement: 3, frame: 4}
    planned.sort((a, b) => rank[a.kind]! - rank[b.kind]! || a.value - b.value)
    observe?.({stage: 'plan', cases: planned.map(({value, kind}) => ({value, kind}))})
    const cases: FixedOperationProof[] = []
    for (const {value, machine, support, kind} of planned) {
      if (late(until)) return
      const start = fullWork(), wall = traceNow()
      const proof = proveRowAgreementCase(machine, family, law, row, until, support?.request ?? requestFor, {...support?.options, leafUnits: options.leafUnits, sparseOwn: true, symmetryReuse: true, premiseScoped: kind === 'copy', operationPath: kind === 'frame' || kind === 'load' || kind === 'leader' || kind === 'copy', diagonalAlias: kind === 'copy' || kind === 'leader', framePremisesOnly: options.framePremisesOnly && kind === 'frame', deferToComposition: true, deferRowChecks: options.deferRowChecks, tailTrace: observe ? event => observe({operation: value, kind, ...event}) : undefined, trace: observe ? event => observe({stage: 'query', operation: value, kind, ...event}) : undefined, observe: leaf => observe?.({stage: 'leaf', outcome: leaf.outcome, hyps: leaf.goal.hyps.length, units: leaf.units, wallMs: leaf.wallMs, operation: value, kind, method: leaf.method, ...(!['proved', 'unchecked-proposal'].includes(leaf.outcome) ? {goal: leaf.goal, path: [...leaf.path.values()]} : {})})})
      observe?.({stage: 'operation', value, kind, proposed: !!proof, checked: false, ...(proof?.status ? {status: proof.status} : {}), units: (fullWork() - start) / fullRate, wallMs: traceNow() - wall, remaining: until - clock(), ...(proof ? {size: countCertificateSize(proof.certs[law.name + ' @step']!)} : {})})
      if (!proof) return
      cases.push({value, proof})
    }
    if (late(until)) return
    const initial = traceCountStage(observe, 'initial-proposal', 'untrusted-search', () => proposeRowAgreementInitial(m, family, law, until, requestFor))
    if (!initial) return
    return composeCountOperationProofs({original: m, machine: m, shape: shapes[0]!, restrictions: [], inputCounts: {}}, family, law, cases, until, requestFor, (stage, value) => observe?.({stage, value}), {initial, trace: observe, minimize: options.minimize})
  })
}
