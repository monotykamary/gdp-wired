// Optional whole-operation strategy. The caller owns one shared allowance;
// discovery selects a proposer, never a trusted fact or a protocol name.
import {type Law, all, n, same, x} from './machine.ts'
import {type GuardCountContext} from './count-guard-context.ts'
import {type CountRequestBuilder, type CountStrategyProof, type CountStrategyOptions} from './count-strategy.ts'
import {finiteCountChoice} from './count-cases.ts'
import {traceNow} from './trace-clock.ts'
import {orderCountOperations, type CountOperationKind} from './count-operation-order.ts'
import {discoverCountRowCopy} from './count-copy-shape.ts'
import {discoverCountThresholdWrite} from './count-write-shape.ts'
import {proveFixedCountPhase} from './count-phase.ts'
import {proveFixedCountFrame} from './count-fixed-frame.ts'
import {proveCountRowCopy} from './count-row-copy.ts'
import {proveCountRowCopyLinear} from './count-row-copy-linear.ts'
import {proveCountReplacement} from './count-replacement.ts'
import {proveCountLeader} from './count-leader.ts'
import {composeCountOperationProofs, type FixedOperationProof} from './count-case-compose.ts'
import {clock, fullRate, fullWork, late, withDeadline} from '../kernel/prove.ts'
export function proveFixedCountOperations(context: GuardCountContext, family: Law[], law: Law, until: number, requestFor: CountRequestBuilder, observe?: (event: Record<string, unknown>) => void, options: CountStrategyOptions & {caseOrder?: 'original' | 'cost'} = {}): FixedOperationProof[] | undefined {
  return withDeadline(until, () => {
    const choice = finiteCountChoice(context.machine)
    if (!choice || late(until)) return
    const [name, values] = choice, cases: FixedOperationProof[] = []
    const planned = [...values].map(value => {
      const branch = {name, value}, write = discoverCountThresholdWrite(context.original, context.shape, branch), copy = discoverCountRowCopy(context.original, context.shape, branch)
      const kind: CountOperationKind = copy ? 'copy' : write?.increment === 1 ? 'leader' : write?.increment === 0 ? 'replacement' : 'phase'
      return {value, kind}
    })
    for (const {value, kind} of orderCountOperations(planned, options.caseOrder)) {
      if (late(until)) return
      const machine = {...context.machine, assume: all(...(context.machine.assume ? [context.machine.assume] : []), same(x(name), n(value)))}, selected = {...context, machine}, wallStart = traceNow()
      const start = fullWork(), caseOptions = {...options, trace: (event: Record<string, unknown>) => observe?.({stage: 'query', value, kind, ...event})}
      const proof = kind === 'copy' ? proveCountRowCopyLinear(machine, family, law, {}, Math.min(until, clock() + 1000), requestFor, undefined, caseOptions) ?? proveCountRowCopy(machine, family, law, {}, until, requestFor, caseOptions) : kind === 'leader' ? proveCountLeader(selected, family, law, {}, until, requestFor, undefined, caseOptions) : kind === 'replacement' ? proveCountReplacement(selected, family, law, {}, until, requestFor, undefined, caseOptions) : proveFixedCountFrame(machine, family, law, {}, until, requestFor, caseOptions) ?? proveFixedCountPhase(machine, family, law, {}, until, requestFor, undefined, caseOptions)
      observe?.({stage: 'operation', value, kind, proposed: !!proof, checked: !!proof && !options.deferToComposition, units: (fullWork() - start) / fullRate, wallMs: traceNow() - wallStart, remaining: until - clock(), ...(proof ? {premises: Object.keys(proof.instances).filter(name => family.some(law => law.name === name))} : {})})
      if (!proof) return
      cases.push({value, proof})
    }
    return cases
  })
}
export function proveCountGuardComposition(context: GuardCountContext, family: Law[], law: Law, until: number, requestFor: CountRequestBuilder, observe?: (event: Record<string, unknown>) => void, options: CountStrategyOptions & {checkEachCase?: boolean, caseOrder?: 'original' | 'cost', reindexMode?: 'offset' | 'exact'} = {}): CountStrategyProof | undefined {
  return withDeadline(until, () => {
    const cases = proveFixedCountOperations(context, family, law, until, requestFor, observe, {...options, deferToComposition: !options.checkEachCase})
    return cases && composeCountOperationProofs(context, family, law, cases, until, requestFor, (stage, value) => observe?.({stage, value}), {reindexMode: options.reindexMode})
  })
}
