import {completeWorkKeys, type CompleteWorkKey, type CompleteWorkWeights} from './work-profile.ts'
// Preserve the declared coefficients and legacy ordering; no calibration change.
const initialLegacyWeights = [
  ['fm', 2.33], ['fcells', 0.0123], ['plainRows', 7.93], ['values', 0.672], ['copies', 0.735], ['edges', 0.0435],
  ['scan', 0.0765], ['pivotRows', 0.599], ['unitRows', 15.6], ['unfoldRows', 0.735], ['goalNodes', 0.492], ['translateRows', 7.93],
] as const
export const legacyWeights = Object.freeze(initialLegacyWeights.map(pair => Object.freeze(pair)))
export type LegacyWorkKey = typeof initialLegacyWeights[number][0]
export const extraWorkKeys = completeWorkKeys
export type ExtraWorkKey = CompleteWorkKey
export type ExtraWorkWeights = CompleteWorkWeights
export type WorkKey = LegacyWorkKey | ExtraWorkKey
export type RawWork = Record<WorkKey, number>
export const workKeys: readonly WorkKey[] = Object.freeze([...legacyWeights.map(([key]) => key), ...extraWorkKeys])
