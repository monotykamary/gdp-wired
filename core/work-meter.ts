import {costs} from './solver.ts'
import {completeWorkProfile} from './work-profile.ts'
import {coreMeter} from './meter.ts'
import {eprMeter} from '../kernel/epr.ts'

// The twelve historical coefficients, in their historical summation order.
const initialLegacyWeights = [
  ['fm', 2.33], ['fcells', 0.0123], ['plainRows', 7.93], ['values', 0.672], ['copies', 0.735], ['edges', 0.0435],
  ['scan', 0.0765], ['pivotRows', 0.599], ['unitRows', 15.6], ['unfoldRows', 0.735], ['goalNodes', 0.492], ['translateRows', 7.93],
] as const
export const legacyWeights = Object.freeze(initialLegacyWeights.map(pair => Object.freeze(pair)))
export const extraWorkKeys = ['tableCells', 'checkSteps', 'astNodes', 'evals', 'cubeTests', 'ticks', 'cdclNodes', 'epr', 'tinyNodes', 'tinyTerms', 'reachStates', 'reachEdges', 'reachEvals', 'reachCompiledEvals'] as const
export type ExtraWorkKey = typeof extraWorkKeys[number]
export type ExtraWorkWeights = Readonly<Record<ExtraWorkKey, number>>
export type WorkKey = typeof legacyWeights[number][0] | ExtraWorkKey
export type RawWork = Record<WorkKey, number>
export const workKeys: readonly WorkKey[] = Object.freeze([...legacyWeights.map(([key]) => key), ...extraWorkKeys])
let extraWeights: ExtraWorkWeights | undefined = completeWorkProfile.enabled ? completeWorkProfile.weights : undefined

export function rawWork(): RawWork {
  return {
    fm: costs.fm, fcells: costs.fcells, plainRows: costs.plainRows, values: costs.values, copies: costs.copies, edges: costs.edges,
    scan: costs.scan, pivotRows: costs.pivotRows, unitRows: costs.unitRows, unfoldRows: costs.unfoldRows, goalNodes: costs.goalNodes, translateRows: costs.translateRows,
    tableCells: coreMeter.tableCells, checkSteps: coreMeter.checkSteps, astNodes: coreMeter.astNodes, evals: coreMeter.evals,
    cubeTests: coreMeter.cubeTests, ticks: coreMeter.ticks, cdclNodes: costs.cdclNodes, epr: eprMeter.n,
    tinyNodes: coreMeter.tinyNodes, tinyTerms: coreMeter.tinyTerms, reachStates: coreMeter.reachStates, reachEdges: coreMeter.reachEdges, reachEvals: coreMeter.reachEvals, reachCompiledEvals: coreMeter.reachCompiledEvals,
  }
}
export function weightedWork(raw: RawWork, extra: ExtraWorkWeights | undefined = extraWeights): number {
  let n = 0
  for (const [key, weight] of legacyWeights) n += weight * raw[key]
  if (extra) for (const key of extraWorkKeys) n += extra[key] * raw[key]
  return n
}
export function fullWork(): number {
  let n = 0
  for (const [key, weight] of legacyWeights) n += weight * costs[key]
  // Preserve the legacy fast path exactly; no implicit provisional coefficients.
  if (!extraWeights) return n
  for (const key of ['tableCells', 'checkSteps', 'astNodes', 'evals', 'cubeTests', 'ticks'] as const) n += extraWeights[key] * coreMeter[key]
  n += extraWeights.cdclNodes * costs.cdclNodes
  n += extraWeights.epr * eprMeter.n
  for (const key of ['tinyNodes', 'tinyTerms', 'reachStates', 'reachEdges', 'reachEvals', 'reachCompiledEvals'] as const) n += extraWeights[key] * coreMeter[key]
  return n
}
export const completeWorkWeights = (): ExtraWorkWeights | undefined => extraWeights
// Callers must explicitly supply the frozen D2 vector. Test fixture vectors are
// permitted, but are never calibration records and never silently become defaults.
export function withCompleteWorkWeights<T>(weights: ExtraWorkWeights, run: () => T): T {
  if (extraWorkKeys.some(key => !Object.hasOwn(weights, key) || !Number.isFinite(weights[key]) || weights[key] < 0)
    || Object.keys(weights).some(key => !(extraWorkKeys as readonly string[]).includes(key))) throw new RangeError(`complete work requires exactly ${extraWorkKeys.length} finite nonnegative coefficients (raw-work-v1)`)
  if (completeWorkProfile.enabled && extraWorkKeys.some(key => weights[key] !== completeWorkProfile.weights[key]))
    throw new Error('complete work profile weights are frozen')
  const previous = extraWeights
  extraWeights = Object.freeze({...weights})
  try { return run() } finally { extraWeights = previous }
}
