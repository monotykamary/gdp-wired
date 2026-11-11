// Untrusted evaluator admission. Permission is not a raw charge and does not
// enlarge a root. Keep this separate from the dependency-free interpreter hook.
import {coreMeter} from './meter.ts'
import {costs} from './solver.ts'
import {eprMeter} from '../kernel/epr.ts'
import {budgetEnd,inBudget} from './wall.ts'
import {rawWork,type RawWork} from './work-meter.ts'
import {completeWorkProfile} from './work-profile.ts'
import {runtimeWall} from './runtime-wall.ts'
import {evaluationAdmissionHook} from './work-observe.ts'
function sameOtherWork(w: RawWork): boolean {
  return w.fm === costs.fm && w.fcells === costs.fcells && w.plainRows === costs.plainRows
    && w.values === costs.values && w.copies === costs.copies && w.edges === costs.edges
    && w.scan === costs.scan && w.pivotRows === costs.pivotRows && w.unitRows === costs.unitRows
    && w.unfoldRows === costs.unfoldRows && w.goalNodes === costs.goalNodes && w.translateRows === costs.translateRows
    && w.tableCells === coreMeter.tableCells && w.checkSteps === coreMeter.checkSteps && w.astNodes === coreMeter.astNodes
    && w.cubeTests === coreMeter.cubeTests && w.ticks === coreMeter.ticks && w.cdclNodes === costs.cdclNodes
    && w.epr === eprMeter.n && w.tinyNodes === coreMeter.tinyNodes && w.tinyTerms === coreMeter.tinyTerms
    && w.reachStates === coreMeter.reachStates && w.reachEdges === coreMeter.reachEdges
    && w.reachEvals === coreMeter.reachEvals && w.reachCompiledEvals === coreMeter.reachCompiledEvals
}
export function withEvaluationAdmission<T>(run: () => T): T {
  if (!completeWorkProfile.enabled || !inBudget()) return run()
  const previous = {...evaluationAdmissionHook}, priorAdmit = runtimeWall.admit
  previous.invalidate?.()
  let credit = 0, end = budgetEnd(), other = rawWork(), expected = coreMeter.evals
  const invalidate = () => { credit = 0 }
  runtimeWall.admit = (units, phase) => { invalidate(); priorAdmit?.(units, phase) }
  evaluationAdmissionHook.invalidate = invalidate
  evaluationAdmissionHook.admit = count => {
    if (count !== 1 && (!Number.isSafeInteger(count) || count < 0)) throw new RangeError('invalid evaluation count')
    if (end !== budgetEnd() || expected !== coreMeter.evals || !sameOtherWork(other)) credit = 0
    if (credit < count) {
      const weight = completeWorkProfile.weights.evals
      const maximum = Math.max(count, Math.max(1, Math.min(256, Math.floor(256 / weight))))
      const block = (runtimeWall.remaining?.() ?? Infinity) >= maximum * weight ? maximum : count
      runtimeWall.admit?.(block * weight, 'model evaluations')
      credit = block; other = rawWork(); end = budgetEnd()
    }
    credit -= count; expected = coreMeter.evals + count
  }
  try { return run() } finally {
    credit = 0; evaluationAdmissionHook.admit = previous.admit; evaluationAdmissionHook.invalidate = previous.invalidate
    runtimeWall.admit = priorAdmit; previous.invalidate?.()
  }
}
