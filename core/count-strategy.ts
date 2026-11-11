// Standalone strategies rebuild and check every original INIT/STEP obligation.
// Composition may request an unchecked STEP proposal; only its final checker
// can accept that proposal as a proof.
import {type Law, type Machine} from './machine.ts'
import {countsForReads} from './count-facts.ts'
import {deferFinalCountStep, type FamilyStepProposal} from './count-final-step.ts'
import {countStageTrace, type CountStageObserver} from './count-stage-trace.ts'
import {type WorkAmount} from './work-amount.ts'
import {type LiftedWorkSliceObserver} from './count-lifted-budget.ts'
import {type CountCert, type CountDecl, type Goal, type Instances, checkMC, countedObligations, mcGoal} from '../kernel/kernel.ts'
import {clock, grow, pastWall} from '../kernel/prove.ts'
// Composition-only proposals intentionally omit INIT and must pass the enclosing final checker.
export type CountStrategyOptions = {familyProposal?: FamilyStepProposal, deferToComposition?: boolean, deferIntermediateChecks?: boolean, deferOwnedReplacementLemmas?: boolean, batchOwnedReplacementPruning?: boolean, deferOwnedReplacementReplay?: boolean, slicedLemmas?: boolean, deferRowChecks?: boolean, minimize?: boolean, reindexFactsOnly?: boolean, emitterFramePool?: boolean, minimalView?: boolean, leafUnits?: number, leafWork?: WorkAmount, workSliceObserver?: LiftedWorkSliceObserver, caseKey?: string, trace?: (event: Record<string, unknown>) => void, tailTrace?: CountStageObserver}
// Calibration-independent: W is the original enclosing work allowance, not
// a case's remaining share. INIT and final checking do not use this cap.
export function strategyLeafUnits(workAllowance: number): number {
  if (!Number.isFinite(workAllowance) || workAllowance < 0) throw new RangeError('invalid strategy work allowance')
  return workAllowance / 120
}
export const strategyLeafUntil = (until: number, options: CountStrategyOptions): number => Math.min(until, clock() + Math.max(0, options.leafUnits ?? Infinity))
// UNCHECKED is construction metadata, never a receipt or public acceptance.
export const deferIntermediateCountChecks = (options: CountStrategyOptions): boolean => options.deferToComposition === true && options.deferIntermediateChecks === true
// Search-only deferral: every retained lemma remains subject to the final native checker.
export const deferOwnedReplacementChecks = (options: CountStrategyOptions): boolean => deferIntermediateCountChecks(options) && options.deferOwnedReplacementLemmas === true
export type CountStrategyProof = {instances: Instances, certs: Record<string, CountCert>, status?: 'unchecked', premises?: readonly string[]}
export type CountRequestBuilder = (goal: Goal, declarations: CountDecl[]) => Pick<CountCert, 'reads' | 'insts' | 'picks'>
export function finishCountStrategy(m: Machine, family: Law[], law: Law, instances: Instances, zeroMap: string, stepCert: CountCert, until: number, requestFor: CountRequestBuilder, observe?: (stage: string, checked: boolean) => void, options: CountStrategyOptions = {}): CountStrategyProof | undefined {
  const index = family.indexOf(law)
  if (index < 0 || clock() >= until || pastWall()) return
  if (options.deferToComposition) return {instances, certs: {[law.name + ' @step']: stepCert}, ...(deferIntermediateCountChecks(options) ? {status: 'unchecked' as const} : {})}
  const trace = countStageTrace(options.tailTrace, 'strategy-finish-total')
  try {
  trace.mark('final-obligation-build', 'untrusted-assembly')
  const packets = countedObligations(m, family, {[law.name]: instances}, index), step = packets.at(-1)
  if (!step) return
  const deferred = deferFinalCountStep(options.familyProposal)
  if (deferred) observe?.('step-proposal', false)
  else {
    trace.mark('native-step-check', 'trusted-check')
    const stepChecked = checkMC(step.goal.hyps, step.decls, stepCert)
    observe?.('step-check', stepChecked)
    if (!stepChecked) return
  }
  const certs: Record<string, CountCert> = {[step.goal.name]: stepCert}
  for (const initial of packets.slice(0, -1)) {
    trace.mark('initial-request-build', 'untrusted-assembly')
    if (clock() >= until || pastWall()) return
    const base = requestFor(initial.goal, initial.decls), counts = countsForReads(initial.decls, base.reads), target = base.reads.find(r => r[1].replace(/#$/, '') === zeroMap)
    const count = counts?.find(c => c.v === target?.[0])
    if (!target || !count) return
    const scope = JSON.stringify([m, family, initial.goal, base]), fresh = (n: number) => `countInitial$${n}`
    let i = 0
    while (scope.includes(JSON.stringify(fresh(i)))) i++
    const request = {reads: base.reads, insts: [{wit: fresh(i), below: count.below, terms: [[1, target[0]] as [number, string]], unit: 0}], picks: []}
    trace.mark('initial-goal-build', 'untrusted-assembly')
    const goal = mcGoal(initial.goal.hyps, initial.decls, request)
    trace.mark('initial-search', 'untrusted-search')
    const result = goal && grow(goal, new Map(), {nodes: 0, until})
    if (!result || !('tree' in result)) {observe?.('initial-search', false); return}
    const cert: CountCert = {...request, tree: result.tree}
    trace.mark('native-init-check', 'trusted-check')
    const initialChecked = checkMC(initial.goal.hyps, initial.decls, cert)
    observe?.('initial-check', initialChecked)
    if (!initialChecked) return
    certs[initial.goal.name] = cert
  }
  trace.mark('certificate-return', 'untrusted-assembly')
  return clock() < until && !pastWall() ? {instances, certs, ...(deferred ? {status: 'unchecked' as const} : {})} : undefined
  } finally {trace.finish()}
}
